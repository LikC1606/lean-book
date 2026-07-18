# 第 8 章　命题即类型：证明的本质

> 本章目标：理解 Lean 证明体系的根基——柯里-霍华德对应。这是全书理论性最强的一章，但我们用大量「同一证明写两遍」（项模式 + 策略模式）把它落地。学完后你能读懂任意逻辑连词的类型含义，并亲手给出小证明。

从本章开始，我们进入 Lean 的第二重身份：**定理证明器**。

## 本章你会做出什么

1. 用柯里-霍华德对照表读懂 `∧ ∨ → ¬ ∀ ∃`；
2. 同一命题分别用**项**和 **`by` 策略**各证一遍；
3. 会用 `rfl` / 重写 / `obtain` 处理等式与存在；
4. 会用 `#print axioms` 审计 `sorry`。

---

## 8.1 一个惊人的等同

1930 年代，逻辑学家柯里（Haskell Curry）与霍华德（William Howard）注意到：

| 逻辑世界 | 编程世界 | Lean 中的名字 |
|----------|----------|---------------|
| 命题 | 类型 | `P : Prop` |
| 命题的证明 | 该类型的一个值 | `h : P` |
| 合取 A ∧ B | 乘积 / 二元组 | `And A B` / `A ∧ B` |
| 析取 A ∨ B | 和类型（二选一） | `Or A B` / `A ∨ B` |
| 蕴含 A → B | 函数类型 | `A → B` |
| 全称 ∀ x, P x | 依赖函数 | `(x : α) → P x` |
| 存在 ∃ x, P x | 依赖对 | `Exists P` / `Σ` 的 Prop 版 |
| 真 | 有一个平凡构造子 | `True` |
| 假 | 空类型（无构造子） | `False` |

这就是**柯里-霍华德对应**（命题即类型）。在 Lean 里它是**字面实现**：

> **证明一个命题 = 写出一个以该命题为类型的项。** 检查证明 = 类型检查。

同一个内核既检查程序类型，也检查证明正确性。内核很小、与庞大库隔离——**可信内核**（trusted kernel）：百万行 mathlib 的正确性，最终归约到这个小检查器。

---

## 8.2 Prop：命题的宇宙

```lean
#check (1 + 1 = 2)              -- Prop
#check (∀ n : Nat, n + 0 = n)   -- Prop
#check (2 + 2 = 5)              -- 也是 Prop！假命题仍是合法命题
```

**「是命题」≠「成立」。** 假命题像空类型：合法，但没有居民（没有证明）。

给出证明 = 给这个 `Prop` 找一个项：

```lean
theorem two_eq_two : 2 = 2 := rfl
theorem trivial_true : True := True.intro
```

### Prop 与 Type 的关键差别（一分钟）

| | `Prop` | `Type` |
|--|--------|--------|
| 用途 | 命题 / 证明 | 数据 / 程序 |
| 证明无关性 | 同一命题的两个证明运行时不可区分 | 数据值通常可区分 |
| 消去 | 从 `False` 可证任何命题 | 从空类型消去到数据有限制 |
| 编译后 | 证明常被擦掉 | 数据保留 |

日常记：**证明是「证据」，不是「要算的数据」。**

---

## 8.3 逻辑连词：构造与消去对照表

每个连词都要会两件事：**怎么构造证明**、**怎么使用（消去）证明**。

### 合取 ∧

| | |
|--|--|
| 含义 | A 且 B |
| 构造 | 一对证明 `⟨ha, hb⟩` 或 `And.intro ha hb` |
| 消去 | `h.left` / `h.right` 或 `And.left h` |

```lean
theorem and_demo : 1 + 1 = 2 ∧ 2 + 2 = 4 :=
  ⟨rfl, rfl⟩

example (h : A ∧ B) : B ∧ A :=
  ⟨h.right, h.left⟩
```

### 析取 ∨

| | |
|--|--|
| 构造 | `Or.inl ha` 或 `Or.inr hb` |
| 消去 | 模式匹配 / `Or.elim h f g` |

```lean
theorem or_demo_left : 1 + 1 = 2 ∨ 2 + 2 = 5 :=
  Or.inl rfl

theorem or_swap_term (h : A ∨ B) : B ∨ A :=
  match h with
  | Or.inl ha => Or.inr ha
  | Or.inr hb => Or.inl hb
```

### 蕴含 →

| | |
|--|--|
| 构造 | `fun h => ...`（假设 A，推出 B） |
| 消去 | 函数应用 `f ha` |

```lean
theorem imp_demo : 2 = 2 → 3 = 3 := fun _ => rfl

theorem succ_eq_of_eq (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]

#check succ_eq_of_eq 3 3 rfl   -- 应用定理 = 调用函数
```

### 否定 ¬

`¬A` **定义为** `A → False`。

```lean
theorem not_false : ¬False := fun h => h

theorem one_ne_two : ¬ (1 = 2) := by
  intro h
  contradiction
```

### 等价 ↔

`A ↔ B` = `(A → B) ∧ (B → A)`。

```lean
theorem iff_demo : (1 + 1 = 2) ↔ (2 = 1 + 1) :=
  ⟨fun h => h.symm, fun h => h.symm⟩
```

### 真与假

```lean
example : True := trivial          -- 或 True.intro
example (h : False) : 1 = 2 := False.elim h  -- 从矛盾证一切（爆炸原理）
```

---

## 8.4 量词：∀ 与 ∃

### 全称 ∀

`∀ n : Nat, P n` = 依赖函数：给任意 `n`，给 `P n` 的证明。

```lean
theorem add_zero_forall : ∀ n : Nat, n + 0 = n := fun n => rfl

#check add_zero_forall 42   -- 42 + 0 = 42 的证明
```

策略里：`intro n` 引入全称。

### 存在 ∃

证明 `∃ n, P n` = **给出见证 + 证明该见证满足 P**。

```lean
theorem exists_even : ∃ n : Nat, n + n = 4 :=
  ⟨2, rfl⟩

example (h : ∃ n : Nat, n + n = 4) : True := by
  obtain ⟨w, hw⟩ := h
  trivial
```

> 💡 **构造性 vs 经典**
>
> 默认构造性逻辑：证存在必须真能拿出见证。不允许「我知道存在但说不出是谁」。需要排中律等时打开 `Classical`（mathlib 大量使用）。直觉：`¬¬A → A` 在构造性里一般不可证——双重否定消除等于「凭空造出 A 的证明」。

---

## 8.5 等号 `=`：最重要的命题

等式只有一个构造子：`Eq.refl` / `rfl`（当两边定义上相同）。

武器：

1. **`rfl`**：两边按定义算出一样；
2. **重写**：有 `h : a = b`，把目标里的 `a` 换成 `b`。

```lean
example (x y : Nat) (h : x = y + 1) : x + 1 = y + 2 := by
  rw [h]

-- 等式工具
-- h.symm : b = a
-- Eq.trans h h' : a = c
-- congrArg f h : f a = f b
```

注意：`0 + n = n` 对任意 `n` **不能**单靠 `rfl`（因为 `+` 对右边参数不是定义性展开的那一侧）——要用归纳或已有引理。这正是第 9 章 `induction` 的动机。

---

## 8.6 两种证明风格：项模式 vs 策略模式

**项模式**（像写程序）：

```lean
theorem and_swap_term : A ∧ B → B ∧ A :=
  fun h => ⟨h.right, h.left⟩
```

**策略模式**（像下命令）：

```lean
theorem and_swap_tac : A ∧ B → B ∧ A := by
  intro h
  exact ⟨h.right, h.left⟩
```

| | 项模式 | 策略模式 |
|--|--------|----------|
| 观感 | 函数式、紧凑 | 交互、可逐步看 Infoview |
| 适合 | 小证明、教学 | **实战 95%**、大证明 |
| 内核看到的 | 证明项 | 策略展开后同样是证明项 |

> 策略不是魔法，只是帮你拼证明项的工具。下一章起全面用策略，但请记住背后仍是「命题 = 类型」。

### 同一命题对照写三遍（推荐跟敲）

命题：`A ∨ B → B ∨ A`。

```lean
-- 1) 项 + match
theorem or_comm_term (h : A ∨ B) : B ∨ A :=
  match h with
  | .inl ha => .inr ha
  | .inr hb => .inl hb

-- 2) 策略 + cases
theorem or_comm_tac (h : A ∨ B) : B ∨ A := by
  cases h with
  | inl ha => exact Or.inr ha
  | inr hb => exact Or.inl hb

-- 3) 策略 + obtain（Or 也可用 cases 更常见）
```

---

## 8.7 证明无关性与 `sorry` 审计

### `#print axioms`

```lean
#print axioms add_zero_forall
-- does not depend on any axioms
```

mathlib 定理常依赖：`Classical.choice`、`Quot.sound`、`propext`——数学上常规。

```lean
theorem cheater : 1 = 1 := by sorry
#print axioms cheater   -- 依赖 sorryAx！
```

`sorry` 开发期好用，**发布前必须清零**。第 14 章工程流程会把公理审计写进 CI。

### 证明不是运行数据

你不能「`#eval` 一个证明得到 42」当业务结果用（在 `Prop` 里）。证明的价值是**通过类型检查**，不是算出一个业务值。需要可计算内容时用 `Type` 里的数据（第 5 章 `Vec`、子类型 `.val` 等）。

---

## 8.8 从自然语言到 Lean（对照）

自然语言：

> 若 A 且 B，则 B 且 A。

Lean：

```lean
theorem and_comm_nl (h : A ∧ B) : B ∧ A :=
  ⟨h.2, h.1⟩
```

自然语言：

> 存在偶数等于 4 的一半的两倍……即存在 n，n+n=4。

Lean：拿出见证 `2` 和计算证明 `rfl`。

练习这种翻译，比背策略名更重要。*Mechanics of Proof* 整本书都在练这件事。

---

## 8.9 踩坑对照

| 症状 | 原因 | 处理 |
|------|------|------|
| 假命题写了但证不出 | 命题合法 ≠ 有证明 | 检查是否证错了陈述 |
| `rfl` 失败 | 不是定义性相等 | `rw` / `simp` / 归纳 |
| `∃` 只有证明没有数 | 构造性要求见证 | 先给出具体 `w` |
| 策略证明通过但 `#print axioms` 有 `sorryAx` | 藏了 sorry | 搜 `sorry` 清掉 |
| 搞混 `→`（蕴含）和 `↔` | 只证了一个方向 | `constructor` 两个方向 |
| `False.elim` 乱用 | 没有真正的 `False` | 先推出矛盾 |

---

## 8.10 本章小结

- **命题 = 类型，证明 = 项**，检查 = 类型检查；
- `Prop` 里假命题合法但无居民；
- 逻辑连词 ↔ 数据型构造：配对 / 选择 / 函数 / 依赖函数 / 见证对；
- 存在要见证；经典逻辑可显式打开；
- 项模式与策略模式等价；`sorry` 用 `#print axioms` 审计。

---

## 练习

### ⭐ 基础

1. 项模式证明 `A ∨ B → B ∨ A`。
2. 证明 `theorem not_false : ¬False`。
3. 证明 `∃ n : Nat, n * n = 16`。

### ⭐⭐ 进阶

4. 项模式与策略模式各写一遍：`A ∧ (B ∧ C) → (A ∧ B) ∧ C`。
5. 证明 `(A → B → C) → (A ∧ B → C)`（提示：拆合取再应用）。
6. `#print axioms` 检查你写过的定理，记录依赖。

### ⭐⭐⭐ 硬核

7. （思考）为何构造性逻辑里 `¬¬A → A` 一般不可证？用「证明必须是项」解释。
8. 证明 `¬ (A ∧ ¬A)`（无矛盾律），再尝试 `A ∨ ¬A`——后者需要什么？

---

## 延伸阅读

| 资源 | 读什么 |
|------|--------|
| [TPIL 第 3–5 章](https://lean-lang.org/theorem_proving_in_lean4/) | 命题、量词、策略 |
| [Natural Number Game](https://adam.math.hhu.de/) Addition / Implication World | 游戏巩固 |
| [Mechanics of Proof](https://hrmacbeth.github.io/math2001/) | 自然语言 ↔ Lean |
| 社区 learn 页 Foundations 简述 | 需要时再挖类型论 |

---

⬅️ [第 7 章](07-monads-io.md) ｜ ➡️ 下一章：[第 9 章　策略证明入门：像搭积木一样写证明](09-tactics-basics.md)
