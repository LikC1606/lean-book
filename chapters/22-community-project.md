# 第 22 章　社区之旅与第一个实战项目

> 本章目标：认识 Lean 社区的文化与资源，并手把手完成一个综合运用全书知识的实战项目。

## 22.1 Lean 社区漫游指南

Lean 社区以**友好、开放、高手云集又耐心带新**著称。主要据点：

### Zulip：社区的心脏

[leanprover.zulipchat.com](https://leanprover.zulipchat.com/)——几乎所有核心开发者、mathlib 维护者都在这。关键频道：

- `#new members`：新手提问区，**任何"愚蠢"问题都欢迎**（社区文化明确要求友善对待新手）；
- `#mathlib4`：数学库讨论；
- `#lean4`：语言本身；
- `#announce`：重要发布；
- 还有中文频道 `#Chinese`！

提问的艺术（在 Zulip 特别受用）：

> 发 **MWE（minimal working example，最小可复现例子）**：一段完整、可直接粘贴运行的代码 + 你期望的行为 + 实际报错。这样的提问通常在几分钟内就有解答。

### GitHub：代码与协作

- `leanprover/lean4`：语言本体；
- `leanprover-community/mathlib4`：数学库；
- `leanprover-community/cslib`：计算机科学库；
- `ImperialCollegeLondon/FLT`：费马大定理项目。

### 其他

- **Reservoir**（reservoir.lean-lang.org）：Lean 包注册中心，找库、发库的地方；
- **Lean FRO 博客与 Roadmap**：了解语言发展方向；
- **会议**：Lean Together（年度社区会议，有线上参与）；
- **视频**：YouTube 上大量讲座（官方频道 + 各大学课程录像）。

## 22.2 参与贡献的路径

Lean 社区的贡献阶梯：

```
L1 用 Lean 做自己的小项目（你现在就可以）
L2 在 Zulip 回答比你更新的人的问题
L3 给 mathlib 修 typo / 补小引理（"good first issue" 标签）
L4 认领 blueprint 项目的引理（FLT、PFR 等）
L5 给 mathlib 贡献新定义/定理板块（需要走 PR review）
L6 维护一个库 / 写工具（Verso、策略、自动化）
L7 参与 Lean 核心开发
```

给 mathlib 提 PR 的实用提示：读 `CONTRIBUTING.md`、遵守命名约定、写文档字符串、`#lint` 检查、保持证明风格与邻近代码一致。社区 review 认真但友善——被 review 是最好的免费教学。

## 22.3 实战项目：一个被完全验证的"安全计算器"

现在，综合运用全书知识完成一个项目：**一个栈式计算器语言，带编译器，且编译结果经形式化验证。**

这是定理证明器领域的"皇冠练习"（源自 *Software Foundations*），覆盖：归纳类型、递归、IO、定理证明、规格陈述。

### 第 1 步：领域——栈式指令集

```lean
inductive Instr where
  | push (n : Int) : Instr
  | add : Instr
  | mul : Instr
  | sub : Instr
deriving Repr

abbrev Stack := List Int
abbrev Prog  := List Instr
```

### 第 2 步：虚拟机（执行语义）

```lean
def execInstr : Instr → Stack → Option Stack
  | .push n, s             => some (n :: s)
  | .add, x :: y :: s      => some ((y + x) :: s)
  | .mul, x :: y :: s      => some ((y * x) :: s)
  | .sub, x :: y :: s      => some ((y - x) :: s)
  | _,     _               => none    -- 栈下溢

def run : Prog → Stack → Option Stack
  | [],      s => some s
  | i :: is, s => match execInstr i s with
                  | some s' => run is s'
                  | none    => none
```

### 第 3 步：源语言与编译器

```lean
inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | sub : Expr → Expr → Expr

def Expr.eval : Expr → Int
  | .num n   => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
  | .sub a b => a.eval - b.eval

def compile : Expr → Prog
  | .num n   => [.push n]
  | .add a b => compile a ++ compile b ++ [.add]
  | .mul a b => compile a ++ compile b ++ [.mul]
  | .sub a b => compile a ++ compile b ++ [.sub]
```

### 第 4 步：皇冠定理——编译器正确性

> **定理**：对任意表达式 e，运行编译结果 = 把 e 的值压栈。

关键引理（程序拼接的执行语义）：

```lean
theorem run_append (p q : Prog) (s : Stack) :
    run (p ++ q) s = (run p s).bind (run q) := by
  induction p generalizing s with
  | nil => rfl
  | cons i is ih =>
      simp only [List.cons_append, run]
      cases execInstr i s with
      | none => rfl
      | some s' => exact ih s'
```

主定理：

```lean
theorem compile_correct (e : Expr) (s : Stack) :
    run (compile e) s = some (e.eval :: s) := by
  induction e generalizing s with
  | num n => rfl
  | add a b iha ihb =>
      simp only [compile, run_append, iha, ihb, Option.bind]
      rfl
  | mul a b iha ihb =>
      simp only [compile, run_append, iha, ihb, Option.bind]
      rfl
  | sub a b iha ihb =>
      simp only [compile, run_append, iha, ihb, Option.bind]
      rfl
```

完成！**这个编译器对一切可能的源程序都是正确的**——不是测试了 1000 个用例，而是数学地覆盖了无穷多个输入。

### 第 5 步：审计

```lean
#print axioms compile_correct
-- 确认不依赖 sorryAx
```

## 22.4 项目扩展方向（任选练手）

1. 给指令集加 `div`（除法），处理除零（`Option` 传播），更新正确性定理（注意 `Expr.eval` 也要变）；
2. 加"变量"：表达式含 `var : String → Expr`，引入环境 `String → Int`，定理相应升级；
3. 写一个**优化 pass**（常量折叠 `1 + 2 → 3`）并证明"优化保持语义"；
4. 用第 19 章的 DSL 技术给源语言做具体语法：`calc_lang 1 + 2 * 3`；
5. 用第 7 章的 IO 写一个 REPL：读入表达式 → 编译 → 运行 → 打印（纯核心已被验证，IO 薄壳信任之）。

## 22.5 结业致辞

如果你一路读到这里并且动手完成了大部分练习——

你已经掌握了：一门现代函数式语言、一个交互式定理证明器、百万行数学库的使用方法、软件验证的方法论、元编程的入门钥匙、以及 AI 时代的证明工作流。

Lean 的世界正在以肉眼可见的速度扩张：数学、软件、密码学、AI、教育……而它的社区刚刚起步，**每一位认真学习的后来者都站得上前排**。

祝你在 Lean 的世界里，证明愉快。🎉

## 练习

1. 独立（不看示例）完成 22.3 的项目，对比你的证明与书中证明的差异；
2. 把项目发布到 GitHub，写一篇 README 说明"已验证"到底保证了什么、没保证什么（信任基分析）；
3. 在 Zulip `#new members` 做一次自我介绍，并分享你的项目链接；
4. 制定你的"下一步计划"：mathlib 贡献？blueprint 认领？AI 证明实验？写在纸上，一个月后回看。

## 延伸阅读

- 《Software Foundations》Vol.1（编译器验证的完整课程，思想同源）；
- Zulip 社区的 `#job postings` 频道——形式化方法岗位正在增长（AWS、Harmonic、各 zk 公司……）。

---

⬅️ [第 21 章](21-education-research.md) ｜ ➡️ [附录 A　常用策略速查表](appendix-a-tactics-cheatsheet.md)
