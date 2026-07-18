# 第 9 章　策略证明入门：像搭积木一样写证明

> 本章目标：掌握策略模式的基本工作流和 10 个最常用策略，能独立写出简单定理的证明。

策略（tactic）是交互式证明的命令。写策略证明的过程像玩解谜游戏：屏幕（Infoview）上显示**当前目标**和**已有假设**，你每出一条策略，局面就变一次，直到目标消失（证明完成）。

本章全程请务必在 VS Code 里边敲边看 Infoview。

## 9.1 证明状态：读懂 Infoview

```lean
example (a b : Nat) (h : a = b) : a + 0 = b + 0 := by
  rw [h]
```

把光标放在 `by` 之后、`rw` 之前，Infoview 显示：

```
a b : Nat
h : a = b
⊢ a + 0 = b + 0
```

- 竖线以上是**局部上下文**（local context）：当前可用的变量和假设；
- `⊢`（输入 `\|-`）后面是**当前目标**（goal）：还需要证明的东西。

`rw [h]` 执行后，目标变为 `b + 0 = b + 0`，然后 Lean 自动发现两边按定义相等（`+ 0` 是定义性等式），目标关闭。当出现 **"No goals"**（没有目标了）时——证明完成！🎉

## 9.2 十大基础策略

### ① `intro`：引入假设

目标是 `A → B` 或 `∀ x, P x` 时，用 `intro` 把前提"请进"上下文：

```lean
example : ∀ n : Nat, n = n := by
  intro n     -- 上下文多了 n : Nat，目标变 n = n
  rfl
```

可以一次引入多个：`intro a b h1 h2`。

### ② `exact`：精确命中

"我手上这个东西正好就是目标"：

```lean
example (h : a = b) : a = b := by
  exact h
```

### ③ `apply`：结论匹配

目标是定理的**结论**时，`apply` 该定理，把目标变成它的**前提**：

```lean
example (h : a = b) : b = a := by
  apply Eq.symm   -- 目标从 b = a 变成 a = b
  exact h
```

`apply` 是"逆向推理"：从目标往回找。`exact` 是"正向命中"。

### ④ `rw`：重写

用等式 `h : a = b` 把目标中的 `a` 换成 `b`：

```lean
example (h : x = 5) : x + x = 10 := by
  rw [h]          -- 目标变 5 + 5 = 10
                  -- 按定义算出相等，自动关闭
```

- 反向重写：`rw [← h]`（输入 `\l` 得 `←`），把 `b` 换成 `a`；
- 连续重写：`rw [h1, h2, h3]`；
- 在假设上重写：`rw [h] at h2`。

### ⑤ `simp`：化简器

调用整个 `@[simp]` 引理库对目标做自动改写，是使用率最高的策略之一：

```lean
example (xs : List Nat) : xs ++ [] = xs := by simp
example (a b : Nat) : a + b + 0 = b + a := by simp [Nat.add_comm]
```

- `simp [foo]`：把定义/引理 `foo` 加入化简规则；
- `simp at h`：化简假设 `h`；
- `simp_all`：把上下文里所有假设都用来化简。

### ⑥ `constructor`：拆构造目标

目标是"合取""存在""iff"等**单构造子**结构时，把它拆成分目标：

```lean
example (ha : A) (hb : B) : A ∧ B := by
  constructor   -- 拆成两个目标：⊢ A 和 ⊢ B
  · exact ha
  · exact hb
```

`·`（输入 `\.`）是**聚焦符**：逐个处理分目标，结构清晰。也可用 `case` 或缩进。

### ⑦ `obtain`：拆解假设

把合取、存在、析取等假设**拆开**：

```lean
example (h : ∃ n : Nat, n > 100) : True := by
  obtain ⟨w, hw⟩ := h   -- w : Nat, hw : w > 100
  trivial
```

### ⑧ `cases`：分类讨论

对归纳类型的值**分情形**：

```lean
example (n : Nat) : n = 0 ∨ n ≠ 0 := by
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (by simp)
```

对 `Or` 假设用 `cases`/`obtain` 就是"分情况证明"：

```lean
example (h : A ∨ B) (f : A → C) (g : B → C) : C := by
  cases h with
  | inl ha => exact f ha
  | inr hb => exact g hb
```

### ⑨ `induction`：数学归纳法

```lean
theorem double_eq_two_mul (n : Nat) : n + n = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      -- k : Nat, ih : k + k = 2 * k（归纳假设）
      -- 目标：k + 1 + (k + 1) = 2 * (k + 1)
      rw [Nat.mul_succ, ← Nat.add_assoc, ← ih]
      ring_nf   -- 或用 grind 直接收尾
```

结构：`zero` 分支证基础情形；`succ k ih` 分支拿到归纳假设 `ih`，证递推情形。

### ⑩ `assumption` / `trivial` / `rfl` / `decide`：收尾四兄弟

```lean
example (h : A) : A := by assumption     -- 上下文里正好有
example : True := by trivial             -- 平凡目标
example : 5 = 5 := by rfl                -- 定义性相等
example : 37 % 5 = 2 := by decide        -- 可判定命题直接算
```

## 9.3 组合技：`<;>` 与 `repeat`

```lean
example (n : Nat) : 0 ≤ n ∧ n ≤ n + 1 := by
  constructor <;> simp    -- 对 constructor 产生的每个目标都执行 simp
```

`t1 <;> t2` 表示"先执行 t1，再对产生的**所有**目标执行 t2"。写简洁证明的利器。

## 9.4 一个完整的工作流示范

证明：**对任意自然数 n，`0 + n = n`。**

第 1 步，陈述定理、开 `by`，看目标：

```lean
theorem zero_add' (n : Nat) : 0 + n = n := by
  sorry
```

Infoview：`⊢ 0 + n = n`。（`rfl` 不行——`0 + n` 不是定义性可化简的。）

第 2 步，对 `n` 归纳：

```lean
  induction n with
  | zero => sorry
  | succ k ih => sorry
```

两个目标：`⊢ 0 + 0 = 0` 和 `k : Nat, ih : 0 + k = k ⊢ 0 + (k + 1) = k + 1`。

第 3 步，基础情形：`0 + 0` 按定义等于 `0`，`rfl` 或 `simp` 收尾。

第 4 步，归纳情形：想把 `0 + (k+1)` 变成 `(0 + k) + 1`（这是加法定理的 `Nat.add_succ`），然后用 `ih` 把 `0 + k` 换成 `k`：

```lean
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
```

完成！全程思路：**先看目标 → 选策略 → 观察新状态 → 重复**。这就是交互式证明的循环。

> 💡 写证明卡壳时的自查清单：
> 1. Infoview 里当前目标是什么？（别盯着代码，盯目标）
> 2. 手头假设有没有能直接用的（`exact`/`apply`/`rw ... at`）？
> 3. 要不要拆目标（`constructor`）、拆假设（`obtain`）、分情形（`cases`）、上归纳（`induction`）？
> 4. 能不能 `simp` / `grind` / `omega` 一把梭？
> 5. 是不是该 `have` 一个中间引理（见下）？

## 9.5 `have` 与 `suffices`：证明中的引理

```lean
example (a b : Nat) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  have h3 : a ≤ a := Nat.le_refl a    -- 先证个中间事实，放进上下文
  exact Nat.le_antisymm h1 h2

example (a b : Nat) (h : a + 1 ≤ b) : a ≤ b := by
  suffices h' : a ≤ a + 1 by           -- "只要证出 a ≤ a+1 就够了"
    exact Nat.le_trans h' h
  exact Nat.le_succ a
```

- `have`：**正向**推进（先证小事实，塞进上下文）；
- `suffices`：**反向**规划（"只要证出 X 就能完成"——目标换成 X，同时欠下"用 X 完成原目标"的证明……注意 Lean 中 `suffices h : X by tac` 是先处理主目标再证 X，书写顺序如例）。

## 9.6 本章小结

- 策略证明 = 观察 Infoview 状态 → 出招 → 重复，直到 **No goals**；
- 十大基础策略：`intro`、`exact`、`apply`、`rw`、`simp`、`constructor`、`obtain`、`cases`、`induction`、收尾系（`assumption`/`trivial`/`rfl`/`decide`）；
- `<;>` 批量处理分目标，`have`/`suffices` 组织中间引理；
- 卡壳时盯着目标想办法，自动化策略随时兜底。

## 练习

1. 证明 `theorem mul_zero (n : Nat) : n * 0 = 0`（对 n 归纳，可能用到 `Nat.mul_succ`）；
2. 证明 `A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)`（综合运用 `intro`/`obtain`/`cases`/`constructor`/`exact`）；
3. 证明 `theorem add_comm_zero (a : Nat) : a + 0 = 0 + a`（提示：右边需要归纳或用现成引理 `Nat.zero_add`）；
4. 证明 `∀ n : Nat, n < n + 1`（提示：`induction` 或直接用标准库引理，`simp` 可能就够）。

## 延伸阅读

- 《The Mechanics of Proof》（Heather Macbeth）——用 Lean 教数学证明的优秀教材，本章策略的绝佳练习册；
- 《Theorem Proving in Lean 4》第 5 章。

---

⬅️ [第 8 章](08-propositions-as-types.md) ｜ ➡️ 下一章：[第 10 章　策略工具箱大全](10-tactics-toolbox.md)
