# 第 18 章　编写自己的策略

> 本章目标：学会编写真正的策略——操作证明状态的程序。学完后你能写宏级自动化、用 `TacticM` 打印假设，并实现简化版 `assumption`。

## 本章你会做出什么

1. 宏策略 `auto` / `crush` 打包常用序列；
2. `show_hypotheses` 遍历局部上下文；
3. `my_assumption` 用 `isDefEq` 关目标；
4. 用 `#guard_msgs` 测策略报错。

---

## 18.1 策略是什么？

你曾是策略**用户**；现在是**作者**。

策略 = 在 `TacticM` 中操作证明状态（goals、上下文）的程序：

```
TacticM ≈ 读元变量上下文 + 读写 goals + 可抛错 + 可访问环境
```

`intro`、`rw`、`simp` 全是别人写的 `TacticM` 程序。

---

## 18.2 三层写法

### 层次一：宏级（覆盖约 70% 定制需求）

```lean
macro "auto" : tactic => `(tactic| intros <;> simp_all <;> try omega)

example (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by auto
```

把团队常用套路固化成一键命令。

```lean
macro "crush" : tactic =>
  `(tactic| intros <;> simp_all <;> try omega <;> try decide)
```

### 层次二：`elab` + `TacticM` 看状态

```lean
import Lean
open Lean Elab Tactic Meta

elab "show_hypotheses" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    for localDecl in ← getLCtx do
      if !localDecl.isImplementationDetail then
        logInfo m!"{localDecl.userName} : {localDecl.type}"

example (a : Nat) (h : a > 0) : a + 1 > 0 := by
  show_hypotheses
  omega
```

| API | 作用 |
|-----|------|
| `getMainGoal` | 主目标 `MVarId` |
| `getGoals` / `setGoals` | 目标列表 |
| `goal.withContext` | 在目标上下文中跑 |
| `getLCtx` | 局部声明 |
| `getType` | 目标类型 |
| `throwError` / `logInfo` | 报错 / 日志 |

### 层次三：构造 `Expr` / 合一

```lean
elab "my_assumption" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if ← isDefEq decl.type target then
        goal.assign decl.toExpr
        return
    throwError "上下文中没有匹配目标的假设"

example (h : 1 + 1 = 2) : 1 + 1 = 2 := by my_assumption
```

`isDefEq`：elaborator 核心服务——「类型能否对上」。

---

## 18.3 领域策略：`clean_zeros`

```lean
macro "clean_zeros" : tactic =>
  `(tactic| simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul])

example (a b : Nat) : (a + 0) * 1 + 0 * b = a := by
  clean_zeros
```

价值：**领域知识 → 策略 → 新人一键复用老手经验**。

---

## 18.4 进阶：拆合取

```lean
elab "split_and_solve" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let tgt ← whnf target
  match tgt with
  | .app (.app (.const ``And _) _) _ =>
      evalTactic (← `(tactic| constructor))
  | _ => throwError "目标不是合取"

example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  split_and_solve
  · rfl
  · rfl
```

底层心智：**目标是元变量洞；`assign` 填洞；`constructor` 开新洞。**

更底层可 `mkFreshExprMVar` 手拼 `And.intro`——见 Metaprogramming 书。

---

## 18.5 调试与测试

```lean
/--
error: 上下文中没有匹配目标的假设
-/
#guard_msgs in
example : 1 + 1 = 2 := by my_assumption
```

- `logInfo` / `trace` 调试；
- `throwError` 带位置错误；
- `example` + `#guard_msgs` = 策略测试。

---

## 18.6 学习路径

1. 宏打包常用序列 ← 你在这里；
2. 读 `Mathlib/Tactic/` 源码；
3. 写 `TacticM` 小工具；
4. 设计决策过程级自动化（`grind` 级别）。

**大多数用户不必写策略**；但懂原理 → 更会用、更会读错、必要时能造工具。

---

## 18.7 踩坑对照

| 症状 | 处理 |
|------|------|
| `getMainGoal` 失败 | 无目标 / 已完成 |
| `isDefEq` 意外成功 | 注意归约；必要时 `whnf` |
| 宏展开非预期 | `#print` / `set_option trace.Elab.step true` |
| 修改上下文后目标过期 | 在 `withContext` 内操作并刷新 goal |
| 测试不稳定 | 固定 simp 引理表 |

---

## 18.8 本章小结

- 策略 = `TacticM` 填洞游戏；
- 三层：宏 → TacticM 状态 → Expr 构造；
- 核心 API：`getMainGoal`、`isDefEq`、`assign`；
- `#guard_msgs` 测策略；定制策略固化团队经验。

---

## 练习

### ⭐ 基础

1. 写 `crush` 并在 3 个定理上测。
2. 宏 `refls`：`repeat rfl` 不适用时改成 `try rfl`。

### ⭐⭐ 进阶

3. `find_eq_hyps`：只打印类型为 `Eq` 的假设。
4. 改进 `my_assumption`：失败时列出所有假设类型。

### ⭐⭐⭐ 硬核

5. `swap_and`：目标 `A ∧ B` 时改为证 `B ∧ A` 再 `constructor` 交换。
6. 阅读 `Mathlib/Tactic/Basic.lean` 一个短策略，写注释版笔记。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| Metaprogramming in Lean 4 · TacticM | 深入 |
| [Tactic Programming Guide](https://github.com/mirefek/lean-tactic-programming-guide) | 友好入门 |
| mathlib Tactic 目录 | 真枪实弹 |

---

⬅️ [第 17 章](17-macros.md) ｜ ➡️ 下一章：[第 19 章　打造领域专用语言（DSL）](19-dsl.md)
