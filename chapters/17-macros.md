# 第 17 章　语法扩展与宏：改造 Lean 本身

> 本章目标：认识 Lean 4 元编程入口——`notation` 与 `macro`。学完后你能加中缀记号、写策略/命令宏，并知道何时该上 `elab`。

## 本章你会做出什么

1. 定义 `infixl` / `postfix` 记号；
2. 写 `repeat_ n times` 策略宏；
3. 写 `assert_eq` 命令宏做编译期测试；
4. 会用决策树选择 notation / macro / elab。

---

## 17.1 为何 Lean 的语法是「活的」

多数语言语法冻结；Lean 4 中解析器、elaborator、策略、记号**大量是 Lean 库**，且对用户开放：

- `do`、`calc`、`if` 等「内置」本质是宏；
- 可把领域记号写得像课本；
- `ring` 等是用户级代码。

层级预告：

```
notation → macro → elab/tactic → DSL（第 18–19 章）
```

---

## 17.2 `notation`：最轻量扩展

```lean
def avg (xs : List Nat) : Nat := xs.sum / xs.length

notation "avg(" xs ")" => avg xs

#eval avg([1, 2, 3, 4])   -- 2
```

```lean
infixl:65 " +++ " => fun (a b : Nat) => a + 2 * b

#eval 1 +++ 3        -- 7
#eval 1 +++ 3 +++ 5  -- 17，左结合
```

| 声明 | 含义 |
|------|------|
| `infixl:65` | 左结合，优先级 65（`+` 同级） |
| `infixr` / `infix` | 右结合 / 不结合 |
| `prefix` / `postfix` | 前/后缀 |
| 优先级数字 | 越大绑越紧（`*` 常 70） |

mathlib 的 `∑`、`∫`、`‖·‖`、`∣` 都是这条路——**学科记号 → 接受度**。

```lean
postfix:max "²" => fun (x : Nat) => x ^ 2
#eval 5²   -- 25
```

---

## 17.3 `macro`：语法树变换

```lean
import Lean

syntax "repeat_" num "times" tacticSeq : tactic

macro_rules
  | `(tactic| repeat_ 0 times $_) => `(tactic| skip)
  | `(tactic| repeat_ 1 times $tac) => `(tactic| $tac)
  | `(tactic| repeat_ $(n+1) times $tac) =>
      `(tactic| ($tac; repeat_ $(Lean.quote n) times $tac))
```

拆解：

1. `syntax ... : tactic` —— 声明新语法；
2. `macro_rules` —— 模式匹配语法树；
3. `` `(tactic| ...) `` —— **准引用**模板；`$x` 反引用嵌入。

**宏 = 模式匹配 + 模板拼装**（类 Lisp / Rust `macro_rules!`）。

### 卫生宏

C 宏易变量捕获；Lean 4 **hygienic macros** 自动改名，避免撞车——可放心写复杂展开。

---

## 17.4 实战：`assert_eq` 编译期测试

```lean
syntax "assert_eq" term:65 "≡" term:65 : command

macro_rules
  | `(command| assert_eq $a ≡ $b) =>
      `(command| example : $a = $b := rfl)
```

```lean
assert_eq 1 + 1 ≡ 2
assert_eq [1, 2].length ≡ 2
-- assert_eq 2 + 2 ≡ 5   -- 编译失败 = 测试失败
```

你造了微型测试语言，且无缝嵌入 Lean。

---

## 17.5 语法类别

| 类别 | 是什么 | 例 |
|------|--------|-----|
| `term` | 表达式 | `fun x => x` |
| `tactic` | 策略 | `rw`、`repeat_` |
| `command` | 顶层命令 | `def`、`assert_eq` |

扩哪类就写 `: term` / `: tactic` / `: command`。

---

## 17.6 进阶一瞥：`elab`

宏不够（要类型信息、证明状态、自定义错误）→ **elaborator**：

```lean
open Lean Elab Command

elab "dump_env" : command => do
  let env ← getEnv
  logInfo m!"常量大约 {env.constants.size} 个"

-- dump_env
```

`CommandElabM` / 后文 `TacticM`：元编程全是 monadic（接第 7、18 章）。

---

## 17.7 何时用什么？

| 需求 | 选择 |
|------|------|
| 记号美化 | `notation` / `infix*` |
| 机械模板 | `macro` |
| 要类型/环境 | `elab` |
| 证明自动化 | tactic（第 18 章） |
| 整领域语言 | 组合 + AST（第 19 章） |

⚠️ **克制**：滥用 → 私有黑话。mathlib 对新语法极谨慎。

---

## 17.8 迷你项目：承诺记号 + 清理零策略

```lean
def commitToy (v r : Nat) : Nat := v + r

notation "C⟦" v ", " r "⟧" => commitToy v r
#eval C⟦3, 4⟧   -- 7

macro "clean_zeros" : tactic =>
  `(tactic| simp only [Nat.add_zero, Nat.zero_add, Nat.mul_one, Nat.one_mul])

example (a : Nat) : a + 0 + 0 = a := by clean_zeros
```

---

## 17.9 踩坑对照

| 症状 | 处理 |
|------|------|
| 优先级绑错 | 调数字；加括号测试 |
| 宏无限递归 | 展开到已有语法，别循环 |
| quotation 类型错 | 标明 `term`/`tactic`/`command` |
| 卫生问题难调 | 少手动造 name；用 quote 系统 |
| 记号污染全局 | 放 namespace / 局部 `section` |

---

## 17.10 本章小结

- 语法层开放：`notation` / `macro` / `elab`；
- 宏 = 匹配 + 准引用；卫生系统防捕获；
- 三类扩展点：term / tactic / command；
- 克制使用，服务可读性。

---

## 练习

### ⭐ 基础

1. 定义 `postfix:max "²"`，测 `12²`。
2. 写 `infixl:70 " ** " => Nat.pow` 风格记号（注意与已有冲突）。

### ⭐⭐ 进阶

3. 宏 `defn double x := 2 * x` → 展开成合适 `def`（可简化版）。
4. 策略宏 `assumption_all`：`first | assumption | (constructor <;> assumption_all)` 思路实现简化版。

### ⭐⭐⭐ 硬核

5. 完善 `assert_eq`，失败时自定义错误信息（需 `elab`）。
6. 读 Metaprogramming in Lean 4 宏章节一节，笔记 5 条 API。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| *Metaprogramming in Lean 4* | 权威 |
| Language Reference · Macros | 精确语义 |
| 第 18–19 章 | 策略与 DSL |

---

⬅️ [第 16 章](16-crypto-blockchain.md) ｜ ➡️ 下一章：[第 18 章　编写自己的策略](18-writing-tactics.md)
