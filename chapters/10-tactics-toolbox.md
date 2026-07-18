# 第 10 章　策略工具箱大全

> 本章目标：认识 Lean 证明工具箱中的「重型装备」——自动化策略、结构化证明利器和 mathlib 专科神器。学完后你应能对着目标按决策树选策略，并习惯用 `exact?` / `simp?` 自助找引理。

第 9 章给了螺丝刀和锤子，本章给电钻和数控机床。

## 本章你会做出什么

1. 用 `omega` / `grind` / `decide` 关掉一批「显然」目标；
2. 用 `simp only` + `simp?` 写出可维护化简；
3. 用 `calc` 写教科书式等式链；
4. 会 `rcases` / `by_cases` / `push_neg`；
5. 在有 mathlib 的环境里用 `ring` / `linarith` / `exact?`。

---

## 10.1 自动化三剑客：`omega`、`grind`、`decide`

### `omega`：线性算术

涉及 `Nat` / `Int` 的**线性**（无「变量 × 变量」）加减比较时：

```lean
example (a b : Nat) (h1 : a + 3 ≤ b) (h2 : b ≤ a + 5) : a + 1 ≤ b := by omega
example (x y : Int) (h : 2 * x + y = 7) (h' : x - y = 2) : x = 3 := by omega
```

**不行时**：出现 `n * m` 且两者都含变量、非线性目标——换 `grind` / 手工 / 其他策略。

### `grind`：新一代全能选手

Lean 近年推出的强力自动化（灵感来自 SMT；与 Z3 作者同源脉络）。擅长：

- 线性不等式；
- 定义展开后的等式；
- 未解释函数 + 量词实例化（E-matching）类推理。

```lean
example (x y : Int)
    (h1 : 27 ≤ 11 * x + 13 * y) (h2 : 11 * x + 13 * y ≤ 45)
    (h3 : -10 ≤ 7 * x - 9 * y) (h4 : 7 * x - 9 * y ≤ 4) :
    7 * x - 9 * y ≤ 4 := by grind

example (a b : Nat) (h : a % b = 0) : b ∣ a := by
  grind [Nat.dvd_of_mod_eq_zero]
```

心法：**`grind [引理₁, 引理₂]`**——把线索引理喂给它。

### `decide`：有限可判定

```lean
example : Nat.Prime 97 := by decide
example : 2^10 = 1024 := by decide
```

目标必须**可判定**（`Decidable`）；无限域上的一般命题不行。

| 策略 | 强项 | 弱项 |
|------|------|------|
| `omega` | Nat/Int 线性 | 非线性、实数 |
| `grind` | 更广的自动推理 | 需线索时要喂引理 |
| `decide` | 具体计算、有限检查 | 一般带变量定理 |

---

## 10.2 `simp` 深入

`simp` 背后是大量 `@[simp]` 重写规则。

```lean
simp only [Nat.add_zero]   -- 只用列出的规则（推荐中间步骤）
simp [myDef]               -- 允许展开 myDef
simp at h ⊢                -- 假设 + 目标（⊢ 用 \|-）
simp_all                   -- 上下文互相利用
```

### 稳定 vs 爽快

| 场景 | 建议 |
|------|------|
| 最后一击关掉目标 | `simp` / `simp_all` 很爽 |
| 大库中间步骤 | **`simp only [...]`**，防库升级打碎证明 |
| 不知道用了啥 | `simp?` → 复制 `Try this` |

```lean
example (xs : List Nat) : xs.reverse.reverse = xs := by
  simp?   -- Try this: simp only [List.reverse_reverse]
```

### 自己挂 `@[simp]`

```lean
@[simp] theorem my_lemma : ... := ...
-- 之后 simp 会尝试使用；勿对「展开会爆炸」的引理乱挂
```

---

## 10.3 `calc`：教科书式推导

```lean
theorem sum_two_mul (n : Nat) : 2 * (n + 1) = 2 * n + 2 := by
  calc 2 * (n + 1)
      = 2 * n + 2 * 1 := by rw [Nat.mul_add]
    _ = 2 * n + 2     := by rw [Nat.mul_one]
```

- 每步右侧 `:= by ...` 证「这一步成立」；
- `_` 承接上行；
- 也支持 `≤`、`<` 等传递关系（分析里极常见）。

**何时用 `calc`：** 多步等式/不等式、要给人读的证明。  
**何时不用：** 一步 `ring` / `omega` 能完事时，别炫技。

---

## 10.4 结构化证明进阶

### 策略里的 `match`

```lean
example (n : Nat) : (match n with | 0 => 0 | k+1 => k) ≤ n := by
  match n with
  | 0 => simp
  | k+1 => simp
```

### `rcases` / `rintro`（mathlib 增强拆包）

```lean
example (h : A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) := by
  rcases h with ⟨ha, hb | hc⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hc⟩

example : A ∧ B → B := by
  rintro ⟨_, hb⟩
  exact hb
```

一行拆多层：合取、析取、存在、乘积……

### `by_cases` 与经典逻辑

```lean
example (P : Prop) : P ∨ ¬P := by
  by_cases h : P
  · exact Or.inl h
  · exact Or.inr h
```

「`x = 0` 或 `x ≠ 0`」式分情形全靠它（隐式用经典逻辑）。

### `push_neg`：否定推进

```lean
example (h : ¬ ∀ n : Nat, n ≤ 10) : ∃ n, ¬ n ≤ 10 := by
  push_neg at h
  exact h
```

`¬∀` → `∃¬`，`¬∃` → `∀¬`，反证与反例的好帮手。

### `refine`：留洞构造

```lean
example (ha : A) (hb : B) : A ∧ B := by
  refine ⟨?_, ?_⟩
  · exact ha
  · exact hb
```

`?_` 是待填子目标；比先 `constructor` 有时更灵活。

---

## 10.5 mathlib 专科医生

需 `import Mathlib`（或更细模块）：

| 策略 | 专长 | 例子 |
|------|------|------|
| `ring` | 交换环多项式等式 | `(a+b)^2 = a^2+2*a*b+b^2` |
| `ring_nf` | 规范化（中间步） | 整理形状 |
| `field_simp` | 域上分式 | 消分母 |
| `linarith` | 有序环/域线性算术 | 实数不等式组 |
| `positivity` | 证正 | `0 < x^2 + 1` |
| `norm_num` | 具体数值 | `(100:ℝ)*0.1 = 10` |
| `gcongr` | 单调 congruence | 放大缩小不等式 |
| `tauto` | 命题逻辑 | 纯逻辑组合 |
| `aesop` | 通用搜索 | 杂活 |
| `exact?`/`apply?`/`rw?` | **搜库** | 卡壳第一反应 |
| `hint` | 试一串常用策略 | 快速试探 |

### `exact?`：最值得记住的外挂

```lean
example (n : Nat) : n + 0 = n := by exact?
-- Try this: exact Nat.add_zero n
```

工作流：`exact?` → 不行 `apply?` → `rw?` → `hint` → Loogle / LeanSearch（第 11 章）。

---

## 10.6 证明调试技巧

| 工具 | 用途 |
|------|------|
| `show e` | 改写目标显示（语义不变），看清要证什么 |
| `set x := e with hx` | 复杂子表达式起名 |
| `guard_target = e` | 断言目标形状（教学/测试） |
| `extract_goal` | 导出当前状态为独立定理草稿 |
| `conv` | 只对子表达式重写 |

```lean
example (a b c : Nat) (h : b = c) : a + (b + 1) = a + (c + 1) := by
  conv => lhs; rw [h]
```

`conv` 在 `rw` 误伤多处匹配时特别有用。

### 常用调试节奏

1. 复制目标到草稿纸 / `have` 拆小；
2. `simp?` / `exact?` 问系统；
3. 仍卡 → 引理可能缺前提，用 `have` 补；
4. 证明又臭又长 → `calc` 或抽 `lemma`。

---

## 10.7 策略选择决策树

```
纯数值 / 可判定？              → decide / norm_num
Nat/Int 线性算术？             → omega / grind
多项式恒等式（环）？           → ring / ring_nf
线性实数不等式？               → linarith / grind
上下文已有答案？               → assumption / exact / simp_all
目标是 ∧ / ∃ / ↔？            → constructor / refine ⟨_, ?_⟩
假设是 ∧ / ∃ / ∨？            → obtain / rcases / cases
全体归纳类型？                 → induction
等式变形？                     → rw / calc / conv
否定量词乱？                   → push_neg
要分 P / ¬P？                  → by_cases
卡住了？                       → exact? / hint / grind [线索]
还不行？                       → have 中间引理；查 Loogle
```

---

## 10.8 踩坑对照

| 症状 | 处理 |
|------|------|
| `omega` 失败 | 检查是否非线性；试 `grind` |
| `simp` 过强改坏目标 | `simp only` 或 `simp [-坏引理]` |
| `ring` 不工作 | 类型是否在环上；需 mathlib |
| `exact?` 无建议 | 目标陈述可能别扭；先 `simp` 整形 |
| `calc` 步步过但连不起 | 关系是否传递；中间类型一致否 |
| 经典 `by_cases` 被拒 | 确认 Prop 与开放 classical 设定 |

---

## 10.9 本章小结

- 三剑客：`omega` / `grind` / `decide`；
- `simp only` + `simp?` 保真可维护；
- `calc`、`rcases`、`by_cases`、`push_neg`、`refine`；
- mathlib：`ring`、`linarith`、`gcongr`、`norm_num`…；
- **卡壳第一反应：`exact?` / `hint`**。

---

## 练习

### ⭐ 基础

1. 用 `omega` 证：`∀ a b c : Nat, a ≤ b → b ≤ c → a ≤ c + 1`。
2. 用 `decide` 证：`7 ∣ 49`（或 `Nat.dvd` 相关陈述，按你环境调整）。

### ⭐⭐ 进阶

3. 用 `calc` 证 `(a + b) + (a + b) = 2 * a + 2 * b`（`Nat`，多用 `rw`）。
4. 用 `rcases` 处理 `h : (A ∧ B) ∨ (C ∧ D)`，推出 `A ∨ C`。
5. 用 `grind`：`example (n : Nat) : n ≤ n + 1 ∧ (n + 1) * 2 = 2 * n + 2`。

### ⭐⭐⭐ 硬核

6. 在 mathlib 项目里 `exact?` 找出：`(xs ++ ys).length = xs.length + ys.length`。
7. 选一个你会手证的代数恒等式，分别用 `ring` 与纯 `rw` 各写一遍，比较长度。

---

## 延伸阅读

| 资源 | 用途 |
|------|------|
| [mathlib4 docs · Tactics](https://leanprover-community.github.io/mathlib4_docs/) | 策略 API |
| Lean Language Reference · Tactic language | 精确语义 |
| [Mechanics of Proof](https://hrmacbeth.github.io/math2001/) | 练习场 |
| 附录 A 策略速查表 | 本书速查 |

---

⬅️ [第 9 章](09-tactics-basics.md) ｜ ➡️ 下一章：[第 11 章　mathlib：一百万行形式化数学](11-mathlib-intro.md)
