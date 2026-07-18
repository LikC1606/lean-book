# 第 9 章　策略证明入门：像搭积木一样写证明

> 本章目标：掌握策略模式的基本工作流和最常用基础策略，能独立写出简单定理的证明。学完后你应能看着 Infoview 闭环完成「观察 → 出招 → 再观察」。

策略（tactic）是交互式证明的命令。像解谜：Infoview 显示**当前目标**和**已有假设**，你每出一招局面变一次，直到 **goals accomplished** / **No goals**。

**本章请务必在 VS Code 里边敲边看 Infoview。**

## 本章你会做出什么

1. 读懂 Infoview 的上下文与 `⊢` 目标；
2. 熟练使用约 10 个基础策略 + `have` / `suffices`；
3. 完整推演 `0 + n = n` 的归纳证明；
4. 建立卡壳时的自查清单。

---

## 9.1 证明状态：读懂 Infoview

```lean
example (a b : Nat) (h : a = b) : a + 0 = b + 0 := by
  rw [h]
```

光标放在 `by` 后、`rw` 前，Infoview 类似：

```
a b : Nat
h : a = b
⊢ a + 0 = b + 0
```

| 区域 | 含义 |
|------|------|
| `⊢` 上方 | 局部上下文：变量与假设 |
| `⊢` 后方 | 当前还要证的目标 |
| 多个 goal | 要分别解决；可 `·` 聚焦 |

`rw [h]` 后目标变 `b + 0 = b + 0`，定义上相等，自动关闭。

> 💡 **黄金习惯**：卡住时先读 Infoview，不要死盯源码猜。

---

## 9.2 十大基础策略

### ① `intro`：引入假设

目标是 `A → B` 或 `∀ x, P x` 时：

```lean
example : ∀ n : Nat, n = n := by
  intro n
  rfl
```

多个：`intro a b h`。也可用 `intros`。

**前后对照：**

| 之前 | 之后 |
|------|------|
| `⊢ ∀ n, n = n` | `n : Nat` 且 `⊢ n = n` |
| `⊢ A → B` | `h : A` 且 `⊢ B` |

### ② `exact`：精确命中

上下文里的项**类型正好是目标**：

```lean
example (h : a = b) : a = b := by
  exact h
```

### ③ `apply`：结论匹配、逆向推理

目标像某定理结论时，`apply` 把目标换成前提：

```lean
example (h : a = b) : b = a := by
  apply Eq.symm
  exact h
```

| | `exact` | `apply` |
|--|---------|---------|
| 要求 | 项完整匹配目标 | 结论统一即可，可留子目标 |
| 直觉 | 正向交卷 | 逆向拆任务 |

### ④ `rw`：重写

```lean
example (h : x = 5) : x + x = 10 := by
  rw [h]
```

- `rw [← h]`：反向（`←` 用 `\l`）；
- `rw [h1, h2]`：连续；
- `rw [h] at h2`：改假设；
- `rw [h] at *`：上下文多处。

### ⑤ `simp`：化简器

用 `@[simp]` 引理库自动改写：

```lean
example (xs : List Nat) : xs ++ [] = xs := by simp
example (a b : Nat) : a + b + 0 = b + a := by simp [Nat.add_comm]
```

| 写法 | 含义 |
|------|------|
| `simp` | 默认库 |
| `simp [foo]` | 加入 `foo` |
| `simp only [foo]` | **只用**列出的（可维护） |
| `simp at h` | 化简假设 |
| `simp_all` | 全上下文互相化简 |

> 第 10 章会强调：中间步骤优先 `simp only`，避免库升级导致证明碎。

### ⑥ `constructor`：拆构造目标

目标是合取、存在、`↔` 等「一个构造子」时：

```lean
example (ha : A) (hb : B) : A ∧ B := by
  constructor
  · exact ha
  · exact hb
```

`·`（`\.`）聚焦子目标。

### ⑦ `obtain` / `rcases`：拆假设

```lean
example (h : ∃ n : Nat, n > 100) : True := by
  obtain ⟨w, hw⟩ := h
  trivial
```

合取：`obtain ⟨ha, hb⟩ := h`。更强拆解可用 `rcases`（模式丰富）。

### ⑧ `cases`：分类讨论

```lean
example (n : Nat) : n = 0 ∨ n ≠ 0 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (by omega)

example (h : A ∨ B) (f : A → C) (g : B → C) : C := by
  cases h with
  | inl ha => exact f ha
  | inr hb => exact g hb
```

### ⑨ `induction`：数学归纳

```lean
theorem double_eq_two_mul (n : Nat) : n + n = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp [Nat.mul_succ, Nat.add_succ, ih]
```

| 分支 | 你有什么 |
|------|----------|
| `zero` | 基础情形 |
| `succ k ih` | 归纳假设 `ih` + 证后继 |

列表归纳同理：`nil` / `cons`。

### ⑩ 收尾四兄弟

```lean
example (h : A) : A := by assumption
example : True := by trivial
example : 5 = 5 := by rfl
example : 37 % 5 = 2 := by decide
```

| 策略 | 何时 |
|------|------|
| `assumption` | 上下文已有目标 |
| `trivial` | `True` 等平凡 |
| `rfl` | 定义性相等 |
| `decide` | 可判定命题直接算 |

另：`omega`（线性算术）、`grind`（第 10 章）也是收尾重器。

---

## 9.3 组合技：`<;>`、`repeat`、`all_goals`

```lean
example (n : Nat) : 0 ≤ n ∧ n ≤ n + 1 := by
  constructor <;> omega
```

- `t1 <;> t2`：先 `t1`，再对**所有**子目标跑 `t2`；
- `repeat rw [h]`：能重写就一直重写；
- `all_goals simp`：每个目标都 `simp`。

---

## 9.4 完整工作流：`0 + n = n`

**第 1 步** 陈述并观察：

```lean
theorem zero_add' (n : Nat) : 0 + n = n := by
  sorry
```

`rfl` 不行：`0 + n` 不能靠定义直接变成 `n`（加法递归在第二个参数上……实际上 `Nat.add` 是对第二个参数递归的——等等，在 Lean 中 `n + 0 = n` 是 `rfl`，但 `0 + n = n` 需要归纳或 `Nat.zero_add`）。

**第 2 步** 归纳：

```lean
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => sorry
  | succ k ih => sorry
```

**第 3–4 步** 填坑：

```lean
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, ih]
```

闭环：**看目标 → 选策略 → 看新状态 → 重复**。

> 📦 更长的无 `sorry` 样板（`add_comm`、`add_assoc`）见：
>
> ```bash
> cd examples && lake build   # Examples/Ch09Add.lean
> ```

### 卡壳自查清单

1. Infoview 当前目标是什么？
2. 假设能否 `exact` / `apply` / `rw`？
3. 要拆目标（`constructor`）、拆假设（`obtain`）、分情形（`cases`）、归纳（`induction`）吗？
4. `simp` / `omega` / `grind` 能否收尾？
5. 要不要 `have` 中间引理？
6. 引理名会不会在标准库？（`exact?` / `apply?`，第 10–11 章）

---

## 9.5 `have` 与 `suffices`

```lean
example (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  exact Nat.le_antisymm h1 h2

example (a b : Nat) (h : a + 1 ≤ b) : a ≤ b := by
  have h' : a ≤ a + 1 := Nat.le_succ a
  exact Nat.le_trans h' h
```

- **`have`**：正向「先证一小点，放进上下文」；
- **`suffices`**：规划「若有 X 就够」——把主目标转为「用 X 证原目标」，再证 X（书写细节以当前文档为准，初学多用 `have` 更直观）。

```lean
example (a b : Nat) (h : a + 1 ≤ b) : a ≤ b := by
  suffices a ≤ a + 1 by exact Nat.le_trans this h
  exact Nat.le_succ a
```

---

## 9.6 结构化书写：`·`、缩进、`case`

```lean
example (h : A ∧ B) : B ∧ A := by
  obtain ⟨ha, hb⟩ := h
  constructor
  · exact hb
  · exact ha
```

多目标时**每个 `·` 块解决一个**，比全挤一行清晰，也方便 Infoview 定位。

---

## 9.7 与第 8 章对照：策略在拼什么项

```lean
-- 策略
theorem and_swap' : A ∧ B → B ∧ A := by
  intro h
  exact ⟨h.right, h.left⟩

-- 本质项
-- fun h => ⟨h.right, h.left⟩
```

`intro` ≈ 写 `fun`；`exact ⟨_, _⟩` ≈ 构造 `And`；`cases` ≈ `match`。

---

## 9.8 踩坑对照

| 症状 | 原因 | 处理 |
|------|------|------|
| `rfl` 不收 | 非定义相等 | `rw`/`simp`/归纳 |
| `apply` 目标更糟 | 用错定理 | `exact?` 或撤销重想 |
| `rw` 重写了错误出现 | 多个匹配 | `rw [h]` nth 或先 `conv`（进阶） |
| `induction` 假设用不上 | 目标形状不对 | 先 `generalize`/`revert` 或调整命题 |
| 子目标乱 | 没聚焦 | 用 `·` 分块 |
| 全是 `sorry` 也能「绿」 | 编辑器仍通过 | `#print axioms` / CI 禁 sorry |

---

## 9.9 本章小结

- 策略证明 = **读 Infoview → 出招 → 重复** 直到无目标；
- 基础策略：`intro` / `exact` / `apply` / `rw` / `simp` / `constructor` / `obtain` / `cases` / `induction` / 收尾系；
- `<;>` 批量处理；`have` 组织中间步骤；
- 卡壳盯目标；自动化随时兜底（第 10 章加强）。

---

## 练习

### ⭐ 基础

1. 证明 `theorem mul_zero' (n : Nat) : n * 0 = 0`（可 `rfl` 或查定义；对比 `0 * n`）。
2. 证明 `∀ n : Nat, n < n + 1`（`omega` 或 `simp` / 标准库）。

### ⭐⭐ 进阶

3. 证明 `A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)`。
4. 证明 `theorem add_comm_zero (a : Nat) : a + 0 = 0 + a`（一边 `rfl`，一边用 `Nat.zero_add` 或自证 `zero_add'`）。
5. 对列表证明 `∀ xs : List α, xs ++ [] = xs`（`induction` + `simp`）。

### ⭐⭐⭐ 硬核

6. 不靠 `Nat.add_comm`，归纳证明 `∀ a b, a + b = b + a`（先证 `n + 0`、`n + succ` 辅助引理）。
7. 把第 8 章某个项模式证明改写成**纯策略**，再 `#print` 看生成项（可选）。

---

## 延伸阅读

| 资源 | 用途 |
|------|------|
| [Mechanics of Proof](https://hrmacbeth.github.io/math2001/) | 证明手艺与练习 |
| [TPIL 策略章](https://lean-lang.org/theorem_proving_in_lean4/) | 系统清单 |
| [Tactic cheatsheet PDF](https://leanprover-community.github.io/papers/lean-tactics.pdf) | 速查 |
| 自然数游戏 | 手感 |

---

⬅️ [第 8 章](08-propositions-as-types.md) ｜ ➡️ 下一章：[第 10 章　策略工具箱大全](10-tactics-toolbox.md)
