# 第 22 章　社区之旅与第一个实战项目

> 本章目标：认识社区文化与资源，并完成综合全书的实战——**经验证的栈式计算器编译器**。学完后你能独立跑通编译器正确性证明，并知道如何向社区迈出第一步。

## 本章你会做出什么

1. 会在 Zulip 用 MWE 提问；
2. 知道贡献阶梯 L1–L7；
3. 实现 `Instr` / `Expr` / `compile` / `run`；
4. 证明 `compile_correct` 并 `#print axioms` 审计；
5. 写出信任基说明（保证了什么 / 没保证什么）。

---

## 22.1 社区漫游

### Zulip（心脏）

[leanprover.zulipchat.com](https://leanprover.zulipchat.com/)

| 频道 | 用途 |
|------|------|
| `#new members` | 新手问题（欢迎「蠢问」） |
| `#mathlib4` | 数学库 |
| `#lean4` | 语言 |
| `#announce` | 发布 |
| `#Chinese` | 中文 |

提问：**MWE** = 完整可粘贴代码 + 期望 + 实际报错（详见附录 B）。

### GitHub

- `leanprover/lean4`
- `leanprover-community/mathlib4`
- `leanprover-community/cslib`
- `ImperialCollegeLondon/FLT`

### 其他

Reservoir 包索引、Lean FRO 博客/路线图、Lean Together 会议、YouTube 讲座。

---

## 22.2 贡献阶梯

```
L1 自己的小项目          ← 你现在
L2 Zulip 回答更新手
L3 mathlib typo / 小引理（good first issue）
L4 blueprint 叶子引理
L5 mathlib 新板块 PR
L6 维护库 / 写工具
L7 核心开发
```

PR 提示：读 `CONTRIBUTING.md`、命名约定、docstring、`#lint`、风格对齐邻码。Review 认真但友善 = 免费导师。

---

## 22.3 实战：安全栈式计算器

定理证明器经典「皇冠练习」（思想同源 *Software Foundations*）：源语言 → 编译 → 虚拟机，**证明编译保持语义**。

### 第 1 步：指令与栈

```lean
inductive Instr where
  | push (n : Int)
  | add | mul | sub
deriving Repr

abbrev Stack := List Int
abbrev Prog  := List Instr
```

### 第 2 步：虚拟机

```lean
def execInstr : Instr → Stack → Option Stack
  | .push n, s        => some (n :: s)
  | .add, x :: y :: s => some ((y + x) :: s)
  | .mul, x :: y :: s => some ((y * x) :: s)
  | .sub, x :: y :: s => some ((y - x) :: s)
  | _, _              => none

def run : Prog → Stack → Option Stack
  | [], s => some s
  | i :: is, s =>
      match execInstr i s with
      | some s' => run is s'
      | none => none
```

注意：双目运算时栈顶是**右操作数**（先算右再算左的编译顺序与之一致）。

### 第 3 步：源语言与编译器

```lean
inductive Expr where
  | num : Int → Expr
  | add | mul | sub : Expr → Expr → Expr
deriving Repr

def Expr.eval : Expr → Int
  | .num n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .sub a b => a.eval - b.eval

def compile : Expr → Prog
  | .num n => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]
  | .sub a b => compile a ++ compile b ++ [.sub]
```

### 第 4 步：关键引理 + 主定理

```lean
theorem run_append (p q : Prog) (s : Stack) :
    run (p ++ q) s = (run p s).bind (run q) := by
  induction p generalizing s with
  | nil => simp [run]
  | cons i is ih =>
      simp only [List.cons_append, run]
      cases execInstr i s with
      | none => simp
      | some s' => exact ih s'

theorem compile_correct (e : Expr) (s : Stack) :
    run (compile e) s = some (e.eval :: s) := by
  induction e generalizing s with
  | num n => simp [compile, run, execInstr]
  | add a b iha ihb =>
      simp [compile, run_append, iha, ihb, run, execInstr]
  | mul a b iha ihb =>
      simp [compile, run_append, iha, ihb, run, execInstr]
  | sub a b iha ihb =>
      simp [compile, run_append, iha, ihb, run, execInstr]
```

（若 `simp` 集合在你版本上不够，逐步 `rw` / `cases`；思想不变。）

**含义**：对**一切**源表达式，编译后运行结果 = 语义值压栈——不是测 1000 个用例，而是覆盖无穷输入。

### 第 5 步：审计

```lean
#print axioms compile_correct
-- 应无 sorryAx
```

### 信任基（写进你的 README）

| 已保证 | 未保证 |
|--------|--------|
| Lean 模型中 compile 与 eval 一致 | 真实 CPU / 其他语言移植 |
| 无栈下溢于「由 compile 产生的程序」 | 任意手写 Instr 序列仍安全 |
| 内核检查的证明 | 你对需求的理解是否写对规格 |

---

## 22.4 扩展方向

1. `div` + 除零 `Option`，升级 `eval`/`compile_correct`；
2. 变量与环境 `String → Int`；
3. 常量折叠优化 pass + 语义保持；
4. 第 19 章 DSL 表面语法；
5. 第 7 章 IO REPL（纯核心已验证）。

### 项目发布清单

- [ ] `lake new` 项目可 `lake build`
- [ ] 无 `sorry`
- [ ] README：规格 + 信任基 + 如何运行
- [ ] 3 个 `#eval` 演示
- [ ] （可选）Zulip 自我介绍贴链接

---

## 22.5 结业致辞

若你读到这里并完成大部分练习——

你已掌握：现代函数式语言、交互式定理证明、mathlib 用法、验证方法论、元编程入门、AI 时代证明工作流。

Lean 的世界在扩张：数学、软件、密码、AI、教育……社区仍年轻，**认真的后来者站得上前排**。

证明愉快。

---

## 练习

### ⭐ 基础

1. 独立重写 22.3（尽量不看答案），再 diff。
2. `#eval run (compile (...)) []` 测三棵表达式树。

### ⭐⭐ 进阶

3. GitHub 发布 + 信任基 README。
4. 实现常量折叠 `simplify : Expr → Expr` 并证 `e.simplify.eval = e.eval`。

### ⭐⭐⭐ 硬核

5. Zulip `#new members` 自我介绍并分享项目。
6. 写一个月计划：mathlib / blueprint / AI / 工业验证 四选一，可执行步骤 5 条。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| Software Foundations Vol.1 | 编译器验证完整课 |
| 附录 B | 资源与提问 |
| Zulip `#job postings` | 形式化岗位信号 |

---

⬅️ [第 21 章](21-education-research.md) ｜ ➡️ [附录 A　常用策略速查表](appendix-a-tactics-cheatsheet.md)
