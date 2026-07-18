# 第 19 章　打造领域专用语言（DSL）

> 本章目标：综合运用语法、宏与语义设计，在 Lean 内嵌一门小型领域语言——并理解为什么"内嵌 DSL"是 Lean 元编程的皇冠明珠。

## 19.1 什么是内嵌 DSL，为什么它重要？

DSL（Domain-Specific Language，领域专用语言）是为特定领域定制的小语言：SQL 之于数据库、正则之于文本匹配、Cron 表达式之于定时任务。

**内嵌 DSL**（embedded DSL，EDSL）不是独立语言，而是**寄生在宿主语言里**的方言。Lean 凭借开放的语法系统，可能是当今做 EDSL 最好的宿主：

- Veil（第 15 章）：分布式协议 DSL，内嵌 Lean；
- Lean 自身的 `do` 记法、`calc`、`conv`：都是 EDSL；
- mathlib 的 `∑`/`∫` 记号族：数学 notation 的 EDSL。

本章我们亲手造一门：**硬件电路描述语言**——顺带展示 Lean 在硬件验证领域的玩法。

## 19.2 设计一门迷你电路语言

目标：让用户这样描述电路——

```lean
circuit half_adder (a b : Bool) where
  s := xor a b
  c := and a b
  output (s, c)
```

并自动得到：① 可执行的电路求值器；② 可证明性质的数学模型。

分三步走：**语法 → 语义（AST）→ 翻译（宏/elab）**。

### 第 1 步：AST——电路的"语义骨架"

```lean
inductive GateExpr where
  | var (name : String) : GateExpr
  | and : GateExpr → GateExpr → GateExpr
  | or  : GateExpr → GateExpr → GateExpr
  | xor : GateExpr → GateExpr → GateExpr
  | not : GateExpr → GateExpr
deriving Repr

structure Circuit where
  inputs  : List String
  assigns : List (String × GateExpr)
  outputs : List String
deriving Repr
```

AST（抽象语法树）是 DSL 的心脏：**语法可以花哨，语义必须干净。**

### 第 2 步：求值器——给 AST 赋予意义

```lean
def GateExpr.eval (env : String → Bool) : GateExpr → Bool
  | .var n    => env n
  | .and a b  => a.eval env && b.eval env
  | .or a b   => a.eval env || b.eval env
  | .xor a b  => a.eval env != b.eval env
  | .not a    => !(a.eval env)

def Circuit.eval (c : Circuit) (env : String → Bool) : List Bool :=
  -- 简化：按赋值顺序逐步扩展环境
  let env' := c.assigns.foldl (init := env) fun e (n, g) =>
    fun x => if x = n then g.eval e else e x
  c.outputs.map env'
```

现在电路已经是**可执行 + 可证明**的一等数学对象了。

### 第 3 步：语法糖——宏把漂亮的记号翻译成 AST

```lean
declare_syntax_cat gate_expr
syntax ident : gate_expr
syntax "and" gate_expr gate_expr : gate_expr
syntax "or"  gate_expr gate_expr : gate_expr
syntax "xor" gate_expr gate_expr : gate_expr
syntax "not" gate_expr : gate_expr
syntax "(" gate_expr ")" : gate_expr

syntax "circuit" ident "(" ident* ")" "where" (ident ":=" gate_expr)* "output" "(" ident,* ")" : command
```

然后用 `macro_rules` 把这套语法翻译成"构造 `Circuit` 值"的 Lean 代码（为控制篇幅给出核心骨架）：

```lean
macro_rules
  | `(gate_expr| $i:ident) => `(GateExpr.var $(Lean.quote i.getId.toString))
  | `(gate_expr| and $a $b) => `(GateExpr.and $(← `(gate_expr| $a)) $(← `(gate_expr| $b)))
  -- ... 其余构造类似
```

（完整的 command 级展开需要 `elab` 递归处理赋值列表，约 30 行——思路不变：模式匹配语法 → 拼出 AST 构造表达式。完成后，`circuit half_adder ...` 就会真的定义出一个 `Circuit` 常量。）

## 19.3 DSL 的杀手锏：验证性质

现在进入 Lean 独有的环节——**为你的 DSL 证明定理**：

```lean
/-- 半加器的正确性：输出 (s, c) 满足 s + 2c = a + b -/
theorem half_adder_correct (a b : Bool) :
    let s := (a != b)
    let c := (a && b)
    s.toNat + 2 * c.toNat = a.toNat + b.toNat := by
  cases a <;> cases b <;> decide
```

真实项目中这意味着：**硬件设计直接在设计语言里被验证**——不用导出到外部工具，设计和证明共享同一套语义。这也是 Lean 硬件验证生态（如正在发展的 Lakeroad 等项目）的工作方式。

## 19.4 EDSL 设计的三层心法

回顾本章架构，内嵌 DSL 的通用蓝图：

```
┌─ 语法层：declare_syntax_cat + syntax + macro ─┐
│   漂亮、贴近领域记号（给领域专家用）              │
├─ 语义层：inductive AST + eval/语义函数 ─────────┤
│   干净、可执行、可推理（给证明用）                │
├─ 定理层：关于语义的性质 ───────────────────────┤
│   DSL 程序的正确性定理（Lean 独有价值）           │
└───────────────────────────────────────────────┘
```

设计经验：

1. **AST 先行**：先设计干净的语义模型，语法糖后面再贴；
2. **语义函数要纯**：`eval : AST → Env → Result` 纯函数化，证明才好写；
3. **语法适可而止**：覆盖领域 80% 常用写法即可，边角让用户回退到原生 Lean；
4. **示例驱动**：先手写 5 个"理想中的 DSL 程序长什么样"，再回头实现。

## 19.5 更多 DSL 灵感

同样的蓝图可以用于：

- **关系代数/SQL**：`query { from users, where age > 18, select name }` → 可证明"查询结果不含未成年"（配合表模型）；
- **概率程序**：`do x ← uniform; y ← bernoulli x; return x + y` → 在 mathlib 测度论上推理分布性质；
- **机器人/控制**：状态机 DSL → 证明安全性不变量（"机械臂永不出围栏"）；
- **金融业务规则**：会计恒等式 DSL → "复式记账永远平衡"的定理；
- **CI/配置语言**：声明式配置 → 证明"配置满足安全基线"。

凡是有**精确规则 + 高正确性要求**的领域，"Lean EDSL + 定理"的模式都可能颠覆现有的"写配置 + 祈祷"工作流。

## 19.6 本章小结

- EDSL = 宿主语言内的领域方言；Lean 的开放语法系统使其成为 EDSL 的理想宿主；
- 蓝图：语法层（宏）→ 语义层（AST + eval）→ 定理层（性质证明）；
- Lean EDSL 的独特价值：**DSL 程序本身就能被形式化验证**；
- 从硬件电路到金融规则，模式放之四海皆准。

## 练习

1. 补全 19.2 电路 DSL 的 `or`/`xor`/`not`/括号 宏规则；
2. 给电路求值器证明一个引理："未赋值变量按环境原值传递"（`env'` 对不在 assigns 中的变量与 env 一致）；
3. 设计一门**正则表达式 DSL** 的 AST：`star`、`alt`、`concat`、`char`、`empty`，并实现 `matches : Regex → List Char → Bool`（用递归 + 列表分裂；证明"empty 只匹配空串"）；
4. （开放）选一个你熟悉的领域，写出它的 EDSL"理想语法"草稿（5 个示例程序），并标注每个程序你想验证的性质。

## 延伸阅读

- 《Metaprogramming in Lean 4》（语法与宏章节）；
- Veil 的 DSL 实现（GitHub: veil-org/veil……搜索 "Veil Lean verification"）；
- 论文：*Certified Programming with Dependent Types*（EDSL 设计思想的经典，Coq 背景但思想通用）。

---

⬅️ [第 18 章](18-writing-tactics.md) ｜ ➡️ 下一章：[第 20 章　AI 与 Lean：自动定理证明的新时代](20-ai-and-lean.md)
