# 第 17 章　语法扩展与宏：改造 Lean 本身

> 本章目标：认识 Lean 4 的杀手级特性——元编程。学会用 `notation` 和宏（macro）给 Lean 添加新语法。

## 17.1 元编程：Lean 为什么与众不同

大多数语言的设计是"冻结"的：语法就这些，想要新特性？等语言委员会下个版本吧。

Lean 4 不一样：**语言的大部分（解析器、elaborator、策略、记号）本身就是用 Lean 写的库**，而且向用户全面开放。这意味着：

- `if ... then ... else`、`do` 记法、`calc`、`∀ ∃ →` 这些"内置语法"，其实都是**宏**——和你能写的东西没有本质区别；
- 你可以为自己的领域添加**自然得不像库**的记号：写矩阵像数学课本、写 SQL 像 SQL、写正则表达式像正则表达式；
- mathlib 里的 `ring`、`linarith` 等策略，都是**用户级代码**——理论上你也能写出这个级别的工具。

这就是"可扩展"三个字的分量，也是 Lean 能同时服务数学、软件验证、AI 等多个领域的技术根源。

本章和接下来两章，我们一层层揭开它：**notation（记号）→ macro（宏）→ elaborator/tactic（精化器与策略）→ DSL（领域语言）**。

## 17.2 notation：最轻量的语法扩展

想给"列表平均值"一个顺手的记号？

```lean
def avg (xs : List Nat) : Nat := xs.sum / xs.length

-- 定义记号：∅ xs 表示 "xs 的平均值"（这里用 ∅ 纯粹为了演示，别在生产代码里滥用）
notation "avg(" xs ")" => avg xs

#eval avg([1, 2, 3, 4])   -- 2（整除）
```

`notation` 是**纯文本级**的替换规则：解析器看到 `avg(...)` 就替换成右边。参数、优先级、结合性都能控制：

```lean
-- 带优先级的二元中记号
infixl:65 " +++ " => fun (a b : Nat) => a + 2 * b

#eval 1 +++ 3        -- 7
#eval 1 +++ 3 +++ 5  -- ((1 +++ 3) +++ 5) = 17，左结合
```

- `infixl` / `infixr` / `infix`：左结合/右结合/不结合；
- 数字 65 是**优先级**（越高绑得越紧，`+` 是 65，`*` 是 70）；
- `prefix`、`postfix` 对应前缀、后缀记号。

mathlib 的数学记号（`∑`、`∫ x in a..b, f x`、`‖x‖`、`a ∣ b`）全是这么来的——**数学家用自己学科的记号写形式化数学**，这对数学社区的接受度至关重要。

## 17.3 macro：编译时的代码变换

`notation` 只能做简单的替换，宏（macro）则是**在语法树上做任意计算的变换**。

### 第一个宏：自动生成"交换律 + 结合律"引理对

设想你定义了一个新运算 `⊕`，想一次生成它的交换律和结合律定理名……先看更朴素的例子——"重复执行 n 次"的命令：

```lean
import Lean

syntax "repeat_" num "times" tacticSeq : tactic

macro_rules
  | `(tactic| repeat_ 0 times $_) => `(tactic| skip)
  | `(tactic| repeat_ 1 times $tac) => `(tactic| $tac)
  | `(tactic| repeat_ $(n+1) times $tac) =>
      `(tactic| ($tac; repeat_ $(Lean.quote n) times $tac))
```

别被吓到，逐块拆解：

1. **`syntax ... : tactic`**：声明新语法——`repeat_ 数字 times 一串策略`，归类为 tactic；
2. **`macro_rules`**：给出转换规则，按模式匹配语法树；
3. **反引号记法 `` `(tactic| ...) ``**：**准引用**（quotation）——"这是一段语法模板"；`$x` 是**反引用**——把变量 x 的内容嵌进来。

本质：**宏 = 模式匹配 + 语法模板拼装**。如果你写过 Lisp/Scheme 的宏或者 Rust 的 `macro_rules!`，这是熟悉的配方。

### 卫生宏：不会"变量捕获"

C 语言宏的著名陷阱：宏展开后意外捕获了使用处的变量。Lean 4 有**卫生宏系统**（hygienic macros，为 ITP 专门设计）：宏引入的变量自动改名，永远不会和用户代码的变量撞车。这是 Lean 4 论文的技术亮点之一——你可以放心写复杂宏，系统保证语义不被意外污染。

## 17.4 实战：一个"断言测试"宏

写一个迷你测试框架，体验宏的真实用途：

```lean
syntax "assert_eq" term:65 "≡" term:65 : command

macro_rules
  | `(command| assert_eq $a ≡ $b) =>
      `(command| #guard_msgs in example : $a = $b := rfl)
```

定义之后可以写：

```lean
assert_eq 1 + 1 ≡ 2          -- 通过，安静
assert_eq [1,2].length ≡ 2   -- 通过
assert_eq 2 + 2 ≡ 5          -- 编译错误！测试失败
```

发生了什么：`assert_eq a ≡ b` 被宏展开成"证明 `a = b` 命题（用 `rfl`）"的命令——**编译期测试**，断言失败 = 类型错误。你刚刚造了一门微型测试语言，而它无缝融入了 Lean。

## 17.5 syntax 类别：术语、策略、命令

Lean 的语法扩展点主要有三类，刚才都用过了：

| 类别 | 是什么 | 例子 |
|------|--------|------|
| `term` | 表达式 | `fun x => x`、`⟨a, b⟩` |
| `tactic` | 策略 | `rw`、`simp`、我们写的 `repeat_` |
| `command` | 顶层命令 | `def`、`theorem`、我们写的 `assert_eq` |

扩写哪类语法，就声明 `: term` / `: tactic` / `: command`。

## 17.6 进阶一瞥：elab 与元编程 Monad

当宏不够用（需要查类型信息、操作证明状态、抛自定义错误），就要动用**elaborator**（精化器）——真正的"编译器插件"：

```lean
open Lean Elab Command in
elab "dump_env" : command => do
  let env ← getEnv
  logInfo s!"当前环境有 {env.constants.size} 个常量"

dump_env   -- 输出环境统计
```

`elab ... => do ...` 块运行在 `CommandElabM` monad 里——还记得第 7 章的 Monad 吗？元编程全是 monadic 代码：读环境（`getEnv`）、报错（`throwError`）、日志（`logInfo`）……第 18 章写策略时会深入这层。

## 17.7 什么时候该用宏？

经验法则：

- **记号美化** → `notation`/`infix`（零风险，优先用）；
- **机械的代码模板**（测试断言、样板定义）→ `macro`；
- **需要类型/环境信息的智能变换** → `elab`；
- **全新的证明自动化** → 写 tactic（第 18 章）；
- **一整个领域语言** → 组合以上全部 + 语义设计（第 19 章）。

警告：宏是强力武器，**滥用会让代码变成只有你能懂的黑话**。mathlib 的审稿标准之一就是对新语法极其克制。

## 17.8 本章小结

- Lean 4 的语法层全面开放：`notation`/`macro`/`elab` 三级扩展，且都是普通 Lean 代码；
- `notation` 做文本替换，`macro` 做语法树变换（模式匹配 + 准引用模板）；
- 卫生宏系统自动避免变量捕获；
- 三大语法类别：`term`、`tactic`、`command`；
- 克制使用：语法糖为了可读性服务，而非炫技。

## 练习

1. 定义后缀记号 `postfix:max "²" => fun (x : Nat) => x ^ 2`，使 `5²` 等于 25；
2. 写一个宏 `defn`：`defn double x := 2 * x` 展开成 `def double (x : Nat) : Nat := 2 * x`；
3. 写一个策略宏 `assumption_all`：展开为 `first | assumption | (constructor <;> assumption_all)`（递归尝试）；
4. 给第 16 章的玩具承诺协议定义记号：`C⟦ v , r ⟧` 表示 `commit v r`。

## 延伸阅读

- 《Metaprogramming in Lean 4》（Arthur Paulino 等，免费在线）——本部分的权威参考书；
- Lean 官方语言参考："Syntax Extensions"、"Macros" 章节。

---

⬅️ [第 16 章](16-crypto-blockchain.md) ｜ ➡️ 下一章：[第 18 章　编写自己的策略](18-writing-tactics.md)
