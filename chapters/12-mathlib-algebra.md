# 第 12 章　代数结构：从群到环域

> 本章目标：理解 mathlib 如何用类型类搭建代数层级，并动手证明一些真正的代数定理。

代数（群、环、域）是形式化数学的"Hello World 进阶版"——结构清晰、定义优雅，最能展示类型类层级的威力。

## 12.1 代数层级：类型类的巅峰之作

回忆第 6 章的预告。mathlib 把代数学的"概念塔"原样搬进了类型类：

```
Semigroup（半群：结合律）
  └─ Monoid（幺半群：+ 单位元）
       └─ Group（群：+ 逆元）
            └─ CommGroup（交换群：+ 交换律）

Ring（环：加法成交换群，乘法成幺半群，分配律）
  └─ CommRing（交换环）
       └─ Field（域：非零元有乘法逆）
```

每个概念 = 一个类型类，**字段包括操作和公理（证明）**：

```lean
-- 概念示意（mathlib 实际定义更精巧，但精神如此）
class Group (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul   : ∀ a : G, 1 * a = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
```

效果是：**在 `Group` 下证的定理，对所有群实例（整数加法群、非零实数乘法群、置换群、矩阵群……）自动成立。** "证明一次，处处适用"——这正是抽象代数的精神，Lean 把它从方法论变成了机器强制的现实。

## 12.2 第一次代数证明：群中的基本功

数学系第一课：群里左消去律成立。看 mathlib 风格的证明：

```lean
import Mathlib

variable {G : Type*} [Group G]

-- 左消去律：a * b = a * c ⟹ b = c
theorem my_mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  calc b = 1 * b           := by rw [one_mul]
    _ = (a⁻¹ * a) * b      := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b)      := by rw [mul_assoc]
    _ = a⁻¹ * (a * c)      := by rw [h]
    _ = (a⁻¹ * a) * c      := by rw [← mul_assoc]
    _ = 1 * c              := by rw [inv_mul_cancel]
    _ = c                  := by rw [one_mul]
```

几个要点：

- `variable {G : Type*} [Group G]`：声明"本节中 G 是任意群"，`Type*` 是宇宙多态的便捷写法；
- `a⁻¹`（输入 `\^-1`）是群中逆元记号；
- `one_mul`、`inv_mul_cancel`、`mul_assoc` 是群公理对应的定理名；
- `calc` 链一步步把 `b` 变成 `c`——和纸面证明的每一步一一对应。

事实上 mathlib 已有此定理（叫 `mul_left_cancel`），自己证一遍是最好的练习。

### 再试一个：(a⁻¹)⁻¹ = a

```lean
theorem my_inv_inv (a : G) : a⁻¹⁻¹ = a := by
  -- 思路：a⁻¹⁻¹ 是"逆的逆"，两边同乘 a⁻¹ 用消去律
  apply mul_left_cancel (a := a⁻¹)
  rw [inv_mul_cancel]
  -- 目标：1 = a⁻¹ * a⁻¹⁻¹
  rw [mul_inv_cancel]
```

写这类证明的节奏：先在纸上想好数学思路，再逐步翻译成 `rw`/`apply`，每步看 Infoview 确认方向。卡住了？`exact?` 往往有惊喜。

## 12.3 环与域：分配律的舞台

```lean
variable {R : Type*} [Ring R]

theorem my_two_mul (a : R) : 2 * a = a + a := by
  rw [two_mul]   -- 现成引理；自己证需要展开 OfNat 定义

example (a b : R) : (a + b) ^ 2 = a^2 + a*b + b*a + b^2 := by ring
```

注意最后一条：`ring` 策略自动搞定**交换半环**中的所有多项式恒等式。非交换环（如矩阵环）里它保持谨慎——`(a+b)²` 展开成 `a² + ab + ba + b²` 而非 `a² + 2ab + b²`，因为矩阵乘法不交换！`ring` 连这都懂。

域（`Field`）里多了除法，`field_simp` 负责通分：

```lean
variable {K : Type*} [Field K]

example (x : K) (hx : x ≠ 0) : x / x = 1 := by
  field_simp
```

## 12.4 具体实例：整数、有理数、模 n 剩余类

抽象定理如何用于具体数系？类型类实例早已备好：

```lean
-- ℤ 是 CommRing，ℚ ℝ ℂ 是 Field
example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- ZMod n：模 n 剩余类
example : (7 : ZMod 12) + 8 = 3 := by decide
example : (5 : ZMod 7) * 3 = 1 := by decide   -- 5 是 3 在 mod 7 下的逆元

-- 对素数 p，ZMod p 是域
example (x : ZMod 7) (hx : x ≠ 0) : x * x⁻¹ = 1 := by field_simp
```

## 12.5 同态：结构之间的桥梁

代数学研究的不只是结构本身，还有**保持结构的映射**（同态）：

```lean
variable {G H : Type*} [Group G] [Group H]

-- G →* H 是"群同态"类型
example (f : G →* H) (a b : G) : f (a * b) = f a * f b := map_mul f a b
example (f : G →* H) : f 1 = 1 := map_one f

-- 同态把单位元映到单位元、把逆映到逆
example (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := map_inv f a
```

`f : G →* H` 是一个**捆绑结构**：里面装着函数本身 + 保持乘法的证明。mathlib 中 `→+*`（环同态）、`→ₗ[]`（线性映射）、`≃+*`（环同构）……一整套"带箭头的类型"构成代数生态的血管网络。

## 12.6 子结构：子群、子环、理想

```lean
variable {G : Type*} [Group G]

-- Subgroup G：G 的子群构成的类型
example (H K : Subgroup G) : H ⊓ K ≤ H := inf_le_left   -- 子群交仍是子群

-- 元素属于子群
example (H : Subgroup G) (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
  H.mul_mem ha hb
```

`⊓`（交）、`≤`（包含）——子结构本身又构成**格**（lattice），mathlib 的层级设计环环相扣。

## 12.7 数论小品：素数有无穷多个

来证一个经典定理收官，体会代数 + 数论的混合使用（这正是官网首页的示例，我们展开讲）：

```lean
import Mathlib

/-- 素数的定义（mathlib 版本）-/
#check Nat.Prime   -- Nat → Prop

/-- 欧几里得：素数有无穷多个。
    即：对任意 n，存在大于 n 的素数。 -/
theorem primes_infinite : ∀ n : Nat, ∃ p > n, Nat.Prime p := by
  intro n
  -- 考虑 n! + 1 的任意素因子 p
  have h1 : 1 < n.factorial + 1 := by
    have := Nat.factorial_pos n; omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h1
  refine ⟨p, ?_, hp_prime⟩
  -- 若 p ≤ n，则 p | n!，又 p | n!+1，故 p | 1，矛盾
  by_contra hle
  push_neg at hle
  have hdvd_fact : p ∣ n.factorial := Nat.dvd_factorial hp_prime.pos hle
  have hdvd_one : p ∣ 1 := by
    have h := Nat.dvd_sub' hp_dvd hdvd_fact
    rwa [Nat.add_sub_cancel_left] at h
  exact Nat.Prime.not_dvd_one hp_prime hdvd_one
```

这个证明用到了：`Nat.exists_prime_and_dvd`（任何大于 1 的数有素因子）、`Nat.dvd_factorial`（≤ n 的正整数整除 n!）、反证法（`by_contra` + `push_neg`）。**每一小步都有 mathlib 引理撑腰**——这就是在大厦上做研究的感觉。

## 12.8 本章小结

- mathlib 用类型类层级表达代数概念塔：公理即字段，定理自动泛化；
- 代数证明的节奏：`calc` 链 + `rw` 公理/引理 + `ring`/`field_simp` 收尾；
- `→*`（同态）、`Subgroup`（子结构）等捆绑类型让"保持结构"成为类型级约束；
- 混合使用数论引理 + 逻辑策略，可以形式化教科书级经典定理。

## 练习

1. 证明群中 `a * b = 1 → b = a⁻¹`（提示：消去律或 `inv_eq_of_mul_eq_one`）；
2. 证明群中 `(a * b)⁻¹ = b⁻¹ * a⁻¹`（注意逆序！可以用 `inv_mul_eq_iff_eq_mul` 等，或者直接查 `mul_inv_rev`）；
3. 在 `ZMod 5` 中用 `decide` 验证费马小定理的实例：`∀ x : ZMod 5, x ≠ 0 → x^4 = 1`；
4. 证明环中 `a * 0 = 0`（提示：`mul_zero` 已存在；自己证可从 `a * 0 = a * (0 + 0)` 入手）；
5. 挑战：证明"群中满足 a² = 1 的元素之逆是它自身"：`(a : G) → a^2 = 1 → a⁻¹ = a`。

## 延伸阅读

- 《Mathematics in Lean》第 6–8 章（代数结构完整教程）；
- mathlib 文档：`Mathlib.Algebra.Group.Basic`；
- Kevin Buzzard 的《Formalising Mathematics》课程笔记（群论部分极佳）。

---

⬅️ [第 11 章](11-mathlib-intro.md) ｜ ➡️ 下一章：[第 13 章　分析、拓扑与计算机科学数学](13-mathlib-analysis.md)
