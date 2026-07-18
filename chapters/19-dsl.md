# 第 19 章　打造领域专用语言（DSL）

> 本章目标：综合语法、宏与语义，在 Lean 内嵌小型领域语言，并理解 EDSL 为何是元编程皇冠。学完后你能设计 AST+eval，挂上 syntax，并为 DSL 程序证一条性质。

## 本章你会做出什么

1. 设计电路 DSL 的 `GateExpr` / `Circuit` AST；
2. 写可执行 `eval`；
3. 用 `declare_syntax_cat` 挂语法；
4. 证明半加器正确性；
5. 套用「语法 / 语义 / 定理」三层蓝图到自己的领域。

---

## 19.1 什么是内嵌 DSL？

DSL：为特定领域定制的小语言（SQL、正则、Cron）。

**EDSL**：寄生在宿主语言中的方言。Lean 开放语法 → 当今最好的 EDSL 宿主之一：

- Veil 协议 DSL；
- `do` / `calc` / `conv`；
- mathlib `∑` / `∫`。

本章造一门**迷你硬件电路语言**。

---

## 19.2 三步：AST → 求值 → 语法

### 理想中的表面语法

```lean
-- 目标体验（完整 elab 后）：
-- circuit half_adder (a b) where
--   s := xor a b
--   c := and a b
--   output (s, c)
```

### 第 1 步：AST（先语义、后糖）

```lean
inductive GateExpr where
  | var (name : String)
  | and : GateExpr → GateExpr → GateExpr
  | or  : GateExpr → GateExpr → GateExpr
  | xor : GateExpr → GateExpr → GateExpr
  | not : GateExpr → GateExpr
deriving Repr, BEq

structure Circuit where
  inputs  : List String
  assigns : List (String × GateExpr)
  outputs : List String
deriving Repr
```

**语法可花哨，语义必须干净。**

### 第 2 步：求值器

```lean
def GateExpr.eval (env : String → Bool) : GateExpr → Bool
  | .var n   => env n
  | .and a b => a.eval env && b.eval env
  | .or a b  => a.eval env || b.eval env
  | .xor a b => xor a.eval env (b.eval env)
  | .not a   => ! a.eval env
where
  xor : Bool → Bool → Bool
    | true,  false => true
    | false, true  => true
    | _,     _     => false

def Circuit.eval (c : Circuit) (env : String → Bool) : List Bool :=
  let env' := c.assigns.foldl (init := env) fun e (n, g) =>
    fun x => if x = n then g.eval e else e x
  c.outputs.map env'

def halfAdderAST : Circuit where
  inputs := ["a", "b"]
  assigns := [
    ("s", .xor (.var "a") (.var "b")),
    ("c", .and (.var "a") (.var "b"))
  ]
  outputs := ["s", "c"]

#eval halfAdderAST.eval fun
  | "a" => true
  | "b" => true
  | _ => false
-- [false, true]  即 sum=0 carry=1，1+1=10₂
```

现在电路是**可执行 + 可证明**的对象。

### 第 3 步：语法类别（挂糖）

```lean
declare_syntax_cat gate_expr
syntax ident : gate_expr
syntax "and" gate_expr gate_expr : gate_expr
syntax "or"  gate_expr gate_expr : gate_expr
syntax "xor" gate_expr gate_expr : gate_expr
syntax "not" gate_expr : gate_expr
syntax "(" gate_expr ")" : gate_expr

-- macro_rules 把 gate_expr 译成 GateExpr 构造
-- command 级 `circuit ...` 需 elab 递归处理列表（约数十行）
-- 练习中补全；思想：匹配语法 → 拼 AST 项
```

```lean
open Lean

macro_rules
  | `(gate_expr| $i:ident) =>
      `(GateExpr.var $(quote i.getId.toString))
  | `(gate_expr| and $a $b) =>
      `(GateExpr.and $(← `(gate_expr| $a)) $(← `(gate_expr| $b)))
  | `(gate_expr| or $a $b) =>
      `(GateExpr.or $(← `(gate_expr| $a)) $(← `(gate_expr| $b)))
  | `(gate_expr| xor $a $b) =>
      `(GateExpr.xor $(← `(gate_expr| $a)) $(← `(gate_expr| $b)))
  | `(gate_expr| not $a) =>
      `(GateExpr.not $(← `(gate_expr| $a)))
  | `(gate_expr| ($a)) => `(gate_expr| $a)
```

---

## 19.3 杀手锏：为 DSL 证定理

```lean
def Bool.toNat : Bool → Nat
  | false => 0
  | true  => 1

theorem half_adder_correct (a b : Bool) :
    let s := (a != b)
    let c := (a && b)
    s.toNat + 2 * c.toNat = a.toNat + b.toNat := by
  cases a <;> cases b <;> decide
```

硬件：**设计与证明共享同一语义**——这是 Lean EDSL 相对「外部工具链」的独特价值（Lakeroad 等生态同思路）。

也可对 AST 版陈述：

```lean
theorem halfAdder_eval_sum (a b : Bool) :
    let out := halfAdderAST.eval fun
      | "a" => a | "b" => b | _ => false
    out.length = 2 := by native_decide
```

---

## 19.4 三层蓝图（可复用）

```
┌─ 语法层：syntax + macro/elab ─────────┐
│  领域专家友好的表面语言                 │
├─ 语义层：AST + 纯 eval ───────────────┤
│  可执行、可推理                         │
├─ 定理层：关于 eval 的性质 ─────────────┤
│  DSL 程序的正确性（Lean 独有）          │
└───────────────────────────────────────┘
```

设计经验：

1. **AST 先行**，糖后贴；
2. **eval 保持纯**；
3. **语法覆盖 80%**，边角回退原生 Lean；
4. **示例驱动**：先写 5 个理想程序再实现。

---

## 19.5 更多灵感

| 领域 | EDSL 想法 | 可证性质 |
|------|-----------|----------|
| SQL | `query { from … where … }` | 结果不含未成年 |
| 概率程序 | monadic 采样 | 分布等式 |
| 控制/机器人 | 状态机 | 永不越界 |
| 金融 | 复式记账 DSL | 借贷永远平衡 |
| 配置/CI | 声明式配置 | 满足安全基线 |

---

## 19.6 正则 DSL 迷你骨架（练习用）

```lean
inductive Regex where
  | empty
  | char (c : Char)
  | alt : Regex → Regex → Regex
  | concat : Regex → Regex → Regex
  | star : Regex → Regex
deriving Repr

-- matches : Regex → List Char → Bool  （练习实现）
```

---

## 19.7 踩坑对照

| 症状 | 处理 |
|------|------|
| 先写宏后改语义 | 永远先定 AST/eval |
| eval 里藏 IO | 拆到薄壳 |
| 语法贪心冲突 | 调优先级 / 关键词 |
| 证明对着语法糖 | 对着 AST/eval 证 |
| DSL 过大 | 砍功能；80 分可交付 |

---

## 19.8 本章小结

- EDSL = 宿主内领域方言；Lean 极擅长；
- 蓝图：语法 → 语义 → 定理；
- 独特价值：DSL 程序可被形式化验证；
- 模式可迁移到任意高正确性规则域。

---

## 练习

### ⭐ 基础

1. 补全 `or`/`xor`/`not` 的 `macro_rules`（若上面已有则写 `nand`）。
2. `#eval` 半加器四种输入。

### ⭐⭐ 进阶

3. 证：对不在 `assigns` 名中的变量，折叠后 env 与原 env 一致（需仔细陈述）。
4. 实现 `Regex` 的 `matches` 子集（至少 `empty`/`char`/`alt`）。

### ⭐⭐⭐ 硬核

5. 用 `elab` 实现简化版 `circuit` 命令，生成 `def` 绑定 `Circuit`。
6. 为自己领域写 5 个理想 DSL 示例 + 每条想证的性质（开放文档题）。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| Metaprogramming in Lean 4 | 语法与宏 |
| Veil 源码 | 工业 EDSL |
| CPDT（Coq）EDSL 思想 | 经典 |
| 第 15 章 Veil、第 17–18 章 | 前后文 |

---

⬅️ [第 18 章](18-writing-tactics.md) ｜ ➡️ 下一章：[第 20 章　AI 与 Lean：自动定理证明的新时代](20-ai-and-lean.md)
