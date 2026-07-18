# 第 12 章　代数结构：从群到环域

> 本章目标：理解 mathlib 如何用类型类搭建代数层级，并动手证明真正的代数定理。学完后你能在任意群上写 `calc` 证明，调用 `ring`/`field_simp`，并读懂同态与子群的类型。

代数（群、环、域）是形式化数学的「Hello World 进阶版」——结构清晰、定义优雅，最能展示类型类层级的威力。

## 本章你会做出什么

1. 在 `variable {G : Type*} [Group G]` 下证明左消去律与逆的逆；
2. 用 `ring` 展开多项式，用 `ZMod` 做模运算小实验；
3. 读懂 `G →* H` 与 `Subgroup G`；
4. 跟读「素数无穷」证明骨架（欧几里得论证）。

---

## 12.1 代数层级：类型类的巅峰

回忆第 6 章。mathlib 把概念塔搬进类型类：

```
Semigroup（半群：结合律）
  └─ Monoid（幺半群 + 单位元）
       └─ Group（+ 逆元）
            └─ CommGroup（+ 交换律）

Ring（加交换群 + 乘幺半群 + 分配律）
  └─ CommRing
       └─ Field（非零有乘逆）
```

概念示意（真实定义更精巧）：

```lean
class Group (G : Type) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)
  one_mul   : ∀ a : G, 1 * a = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1
```

**在 `Group` 下证的定理，对所有群实例自动成立**——整数加法群、非零实数乘法群、置换群……抽象代数的精神变成机器强制。

### 读定理时的心法

看到：

```lean
variable {G : Type*} [Group G]
theorem foo (a : G) : ...
```

心译：「任意群里……」你的具体群只要有实例，直接用。

---

## 12.2 第一次代数证明：左消去律

```lean
import Mathlib

variable {G : Type*} [Group G]

theorem my_mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  calc b = 1 * b           := by rw [one_mul]
    _ = (a⁻¹ * a) * b      := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b)      := by rw [mul_assoc]
    _ = a⁻¹ * (a * c)      := by rw [h]
    _ = (a⁻¹ * a) * c      := by rw [← mul_assoc]
    _ = 1 * c              := by rw [inv_mul_cancel]
    _ = c                  := by rw [one_mul]
```

要点：

| 写法 | 含义 |
|------|------|
| `variable {G : Type*} [Group G]` | 本节 G 是任意群；`Type*` 宇宙多态 |
| `a⁻¹` | 逆元（`\^-1`） |
| `one_mul` 等 | 群公理对应的定理名 |
| `calc` | 与纸面一步步对应 |

mathlib 已有 `mul_left_cancel`——自己证一遍是最好练习。

### 再证：`(a⁻¹)⁻¹ = a`

```lean
theorem my_inv_inv (a : G) : (a⁻¹)⁻¹ = a := by
  apply mul_left_cancel (a := a⁻¹)
  rw [inv_mul_cancel, mul_inv_cancel]
```

节奏：**纸上想清数学 → `rw`/`apply` 翻译 → Infoview 确认**。卡住用 `exact?`。

### 常见群公理/引理速查

| 名字 | 内容 |
|------|------|
| `mul_assoc` | 结合律 |
| `one_mul` / `mul_one` | 单位元 |
| `inv_mul_cancel` / `mul_inv_cancel` | 逆 |
| `mul_left_cancel` | 左消去 |
| `mul_inv_rev` | `(a*b)⁻¹ = b⁻¹ * a⁻¹` |

---

## 12.3 环与域

```lean
variable {R : Type*} [Ring R]

theorem my_two_mul (a : R) : 2 * a = a + a := by
  rw [two_mul]

example (a b : R) : (a + b) ^ 2 = a^2 + a*b + b*a + b^2 := by ring
```

`ring` 处理**交换半环**多项式恒等式。非交换时保持谨慎：矩阵环上是 `a²+ab+ba+b²` 而非 `a²+2ab+b²`。

```lean
variable {K : Type*} [Field K]

example (x : K) (hx : x ≠ 0) : x / x = 1 := by field_simp
```

| 策略 | 场景 |
|------|------|
| `ring` / `ring_nf` | 环上多项式 |
| `field_simp` | 域上分式通分 |
| `abel` | 交换群加法整理（mathlib） |

---

## 12.4 具体实例：ℤ、ℚ、ZMod

```lean
example (a b : ℤ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

example : (7 : ZMod 12) + 8 = 3 := by decide
example : (5 : ZMod 7) * 3 = 1 := by decide

example (x : ZMod 7) (hx : x ≠ 0) : x * x⁻¹ = 1 := by field_simp
```

素数模下 `ZMod p` 是域——数论与密码学玩具（第 16 章）的常用舞台。

---

## 12.5 同态：结构之间的桥梁

```lean
variable {G H : Type*} [Group G] [Group H]

example (f : G →* H) (a b : G) : f (a * b) = f a * f b := map_mul f a b
example (f : G →* H) : f 1 = 1 := map_one f
example (f : G →* H) (a : G) : f a⁻¹ = (f a)⁻¹ := map_inv f a
```

`G →* H` 是**捆绑类型**：函数 + 保运算证明。同类还有：

| 记号 | 含义 |
|------|------|
| `→+*` | 环同态 |
| `→ₗ[R]` | 线性映射 |
| `≃*` / `≃+*` | 同构 |

---

## 12.6 子结构

```lean
variable {G : Type*} [Group G]

example (H K : Subgroup G) : H ⊓ K ≤ H := inf_le_left

example (H : Subgroup G) (a b : G) (ha : a ∈ H) (hb : b ∈ H) :
    a * b ∈ H := H.mul_mem ha hb
```

`⊓` 交、`≤` 包含——子结构形成格，层级环环相扣。

---

## 12.7 数论小品：素数无穷

```lean
import Mathlib

theorem primes_infinite : ∀ n : Nat, ∃ p > n, Nat.Prime p := by
  intro n
  have h1 : 1 < n.factorial + 1 := by
    have := Nat.factorial_pos n; omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h1.ne'
  refine ⟨p, ?_, hp_prime⟩
  by_contra hle
  push_neg at hle
  have hdvd_fact : p ∣ n.factorial := Nat.dvd_factorial hp_prime.pos hle
  have hdvd_one : p ∣ 1 :=
    (Nat.dvd_add_right hdvd_fact).mp (by convert hp_dvd using 1; omega)
  exact Nat.Prime.not_dvd_one hp_prime hdvd_one
```

（若本地 mathlib 版本上细节引理名略有差异，以 `exact?` 为准微调；骨架是：**n!+1 的素因子 p 不能 ≤ n**。）

用到：`exists_prime_and_dvd`、`dvd_factorial`、反证 + `push_neg`——**每步有库引理撑腰**。

---

## 12.8 迷你项目：自己定义一个「玩具幺半群」

不依赖完整 mathlib 层级时，可手写小类体会：

```lean
structure ToyMonoid where
  carrier : Type
  mul : carrier → carrier → carrier
  one : carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a

def NatAddMonoid : ToyMonoid where
  carrier := Nat
  mul := (· + ·)
  one := 0
  mul_assoc := Nat.add_assoc
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero
```

再对比 mathlib 的 `AddMonoid Nat`——理解「bundled vs typeclass」两种组织法（mathlib 两者都用）。

---

## 12.9 踩坑对照

| 症状 | 处理 |
|------|------|
| `ring` 不收 | 非交换？或需要 `CommRing` |
| `a⁻¹` 报错 | 缺 `Group`/`Inv` 实例 |
| `1` 不是 G | 缺 `One` / `OfNat` |
| 矩阵上 `2*a*b` | 不要假设交换 |
| 素数证明编不过 | 对齐 mathlib 版本引理名 |

---

## 12.10 本章小结

- 代数概念塔 = 类型类层级；公理即字段；
- 证明节奏：`calc` + 公理 `rw` + `ring`/`field_simp`；
- 同态、子群是捆绑类型；
- 数论小定理展示「库引理 + 逻辑策略」组合。

---

## 练习

### ⭐ 基础

1. 证 `a * b = 1 → b = a⁻¹`（或 `exact?` 找现成）。
2. 在 `ZMod 5` 验证：`∀ x : ZMod 5, x ≠ 0 → x^4 = 1`（`decide` 或逐点）。

### ⭐⭐ 进阶

3. 证 `(a * b)⁻¹ = b⁻¹ * a⁻¹`（可 `mul_inv_rev`）。
4. 手证环中 `a * 0 = 0`（从 `a*(0+0)` 入手，或对照 `mul_zero`）。
5. 证：`a^2 = 1 → a⁻¹ = a`。

### ⭐⭐⭐ 硬核

6. 跟做 MIL 代数章节一个完整文件。
7. 在 `Subgroup` 上证明：单位元总在任意子群中。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| [MIL 代数章](https://leanprover-community.github.io/mathematics_in_lean/) | 系统练习 |
| `Mathlib.Algebra.Group.Basic` | 源码 |
| Buzzard *Formalising Mathematics* | 群论笔记 |

---

⬅️ [第 11 章](11-mathlib-intro.md) ｜ ➡️ 下一章：[第 13 章　分析、拓扑与计算机科学数学](13-mathlib-analysis.md)
