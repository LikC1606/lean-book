# 第 18 章　编写自己的策略

> 本章目标：学会编写真正的策略（tactic）——操作证明状态的程序。这是 Lean 元编程的核心，也是"定制自动化"的入口。

## 18.1 策略到底是什么？

第 9–10 章你是策略的**用户**，本章成为策略的**作者**。

一个策略就是一段操作**证明状态**（goal 列表、局部上下文）的程序，运行在 `TacticM` monad 里：

```lean
TacticM = 读元变量上下文 + 读写 goal 列表 + 可抛错 + 可访问全部环境信息
```

你用过的一切策略——`intro`、`rw`、`simp`——都是别人写的 `TacticM` 程序。今天轮到你。

## 18.2 三个层次的策略写法

### 层次一：宏级策略（够用 70% 的场景）

很多"自定义策略"只是把现有策略打包成快捷键：

```lean
macro "auto" : tactic => `(tactic| intros <;> simp_all <;> try omega)

example (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by auto
```

一行宏，把"intro 所有前提 → simp_all → 试试 omega"串成新策略 `auto`。mathlib 里不少常用策略就是这么"长"出来的。

### 层次二：`elab` + `TacticM` 操作 goal

需要看证明状态的"内容"再决定动作时，进入 `TacticM`：

```lean
import Lean
open Lean Elab Tactic Meta

/-- 打印当前所有假设的名字和类型，然后不做任何事 -/
elab "show_hypotheses" : tactic => do
  let goal ← getMainGoal              -- 当前主目标（一个元变量）
  goal.withContext do                  -- 在目标的上下文中运行
    for localDecl in ← getLCtx do      -- 遍历局部上下文
      if !localDecl.isImplementationDetail then
        logInfo m!"{localDecl.userName} : {localDecl.type}"

example (a : Nat) (h : a > 0) : a + 1 > 0 := by
  show_hypotheses
  -- 输出：a : Nat   h : a > 0   ⊢ ...（用户可见的假设）
  omega
```

核心 API 速览：

| 函数 | 作用 |
|------|------|
| `getMainGoal : TacticM MVarId` | 取当前主目标 |
| `getGoals` / `setGoals` | 取/换目标列表 |
| `goal.withContext do ...` | 在目标的局部上下文里运行代码 |
| `getLCtx` | 取局部上下文（所有假设） |
| `getTarget : MVarId → TacticM Expr` | 取目标的类型（要证明什么） |
| `closeMainGoal e` | 用项 `e` 直接关闭主目标 |
| `throwError` / `logInfo` | 报错 / 输出 |

### 层次三：调用 elaboration 基础设施

真正的策略要**构造表达式**（Expr）、调用类型检查、做合一（unification）。这是深水区，先给一个能跑的模板：

```lean
/-- "exact 上下文中第一个类型匹配目标的假设"——简化版 assumption -/
elab "my_assumption" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type target then        -- 类型是否定义上相等？
        goal.assign decl.toExpr                  -- 用该假设关闭目标
        return
    throwError "上下文中没有匹配目标的假设"

example (h : 1 + 1 = 2) : 1 + 1 = 2 := by my_assumption
```

`isDefEq`（定义相等判定）是 elaborator 的核心服务之一——所有"类型能不能对上"的问题都问它。

## 18.3 实战：写一个 `add_zero_simp` 策略

目标：写一个领域特化的自动化策略，专门清扫"加法中的零"——把所有 `x + 0`、`0 + x` 化掉。技术上就是调用 simp 并指定引理集，但包装成**语义化的一键命令**：

```lean
macro "clean_zeros" : tactic =>
  `(tactic| simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_mul])

example (a b : Nat) : (a + 0) * 1 + 0 * b = a := by
  clean_zeros
  simp
```

实际项目里，这类"团队定制策略"非常有价值：把领域知识和常用引理固化成策略，**新人也能一键享用老手的证明经验**。

## 18.4 进阶：`MetaM` 与证明项的构造

最深的层次是直接构造**证明项**（`Expr`），比如自动构造合取证明：

```lean
open Lean Meta Elab Tactic

elab "split_and_solve" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  match target with
  | .app (.app (.const ``And _) lhs) rhs =>
      -- 目标是 A ∧ B：分别创建子目标
      let lhsGoal ← mkFreshMVar
      let rhsGoal ← mkFreshMVar
      goal.assign (mkApp2 (mkConst ``And.intro) lhsGoal rhsGoal)
      replaceMainGoal [lhsGoal.mvarId!, rhsGoal.mvarId!]
  | _ => throwError "目标不是合取式"

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  split_and_solve
  · rfl
  · rfl
```

这里的要点：**目标是一个元变量（metavariable）**，`goal.assign e` 就是"这个洞的答案是 e"；`mkFreshMVar` 开新洞，`replaceMainGoal` 把它们立为新目标。所有策略的底层都是这套"填洞"游戏。

## 18.5 调试与测试策略

- `logInfo` / `trace[...]` 输出调试信息；
- `throwError` 给出带位置的错误；
- 测试策略：**写成 `example` 文件 + 预期结果**，配合 `#guard_msgs` 可以断言"这条策略应该报这个错"：
  ```lean
  /--
  error: 上下文中没有匹配目标的假设
  -/
  #guard_msgs in
  example : 1 + 1 = 2 := by my_assumption
  ```

## 18.6 学习路径建议

写策略是 Lean 中"上限最高"的技能，但不必一步登天：

1. **第一阶段**：会写宏级策略（打包常用序列）——本书已覆盖；
2. **第二阶段**：会读/改 mathlib 的策略源码（`Mathlib/Tactic/` 目录是宝库）；
3. **第三阶段**：能写 `TacticM` 级别的工具策略；
4. **第四阶段**：设计新的决策过程（`grind` 就是这个级别的作品）。

提醒：**大多数用户永远不需要写策略**。但了解它的原理会让你——读懂报错更透彻、用自动化更自信、必要时能造出自己的工具。

## 18.7 本章小结

- 策略 = `TacticM` monad 里操作"目标洞（metavariable）"的程序；
- 三级写法：宏打包 → `TacticM` 操作 goal → `MetaM` 构造证明项；
- 核心 API：`getMainGoal`、`getType`、`isDefEq`、`assign`、`replaceMainGoal`；
- `#guard_msgs` 可以把"预期报错"写成测试；
- 定制策略是团队固化证明经验的利器。

## 练习

1. 写宏策略 `crush`：`intros; simp_all; try omega; try tauto`（组合自动化全家桶），并在三个不同定理上测试；
2. 写策略 `find_hyp`：打印上下文中所有**形状为等式**（`Eq`）的假设；
3. 改进 `my_assumption`：找不到匹配时，错误信息里列出上下文中所有假设的类型；
4. （挑战）写策略 `swap_first_two`：当目标是 `A ∧ B` 时自动应用 `And.swap`，否则报错。

## 延伸阅读

- 《Metaprogramming in Lean 4》第 5–8 章（TacticM 深入）；
- mathlib 源码：`Mathlib/Tactic/Basic.lean`、`Mathlib/Tactic/NormNum/`（看真实策略怎么写）。

---

⬅️ [第 17 章](17-macros.md) ｜ ➡️ 下一章：[第 19 章　打造领域专用语言（DSL）](19-dsl.md)
