# 第 13 章　分析、拓扑与计算机科学数学

> 本章目标：一窥 mathlib 中「硬数学」（极限、连续、测度）的形态，以及 CSLib 与形式化前沿。学完后你能读懂 `Tendsto`/`Continuous`，跑通几个分析小例子，并知道大项目（PFR、FLT）如何组织。

## 本章你会做出什么

1. 用滤子语言读「1/n → 0」「连续复合」；
2. 对多项式函数证连续 / 算简单导数；
3. 知道拓扑、概率、图论在库中的入口；
4. 理解 CSLib / StatLib / EconLib / FLT 在版图中的位置。

---

## 13.1 极限：滤子的胜利

数列极限、函数极限、x→∞……能否统一？

mathlib 的答案：**滤子（filter）**。

```lean
-- f 沿滤子 l 趋于 y 的邻域
Tendsto f l (𝓝 y)
```

`𝓝 y`（`\Nh` / `\Nb` 等，以编辑器为准）是 y 的邻域滤子。

| 日常说法 | Lean |
|----------|------|
| 数列 u → a | `Tendsto u atTop (𝓝 a)` |
| f 在 x₀ 连续 | `ContinuousAt f x₀`，即 `Tendsto f (𝓝 x₀) (𝓝 (f x₀))` |
| x→+∞ 时 f→a | `Tendsto f atTop (𝓝 a)` |

同一套极限引理（加、乘、复合）**通吃**。

```lean
import Mathlib

open Filter Topology

example : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := hg.comp hf
```

### 初学者怎么用

不必第一天吃透滤子公理。实用路径：

1. 会写 `Tendsto` / `Continuous` 目标；
2. `exact?` / 文档搜 `tendsto_` 前缀；
3. 需要时再读 MIL 拓扑章。

---

## 13.2 微积分

```lean
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  simp [deriv_pow'']  -- 引理名随版本可能微调
  norm_num

-- 区间积分示例（工具链较重，有时需更多 import）
-- example : ∫ x in (0:ℝ)..1, x = 1/2 := by ...
```

覆盖面（概念级）：一元/多元导数、积分、微积分基本定理、泰勒……Liquid Tensor 等项目大量依赖分析库。

**练习姿势**：具体点值用 `norm_num`；一般恒等式找 `deriv_*` 引理。

---

## 13.3 拓扑

```lean
variable {X : Type*} [TopologicalSpace X]

example (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) :
    IsOpen (U ∩ V) := hU.inter hV
```

长项：度量空间、紧性、连通、完备——现代分析地基。对应用户：多数时候通过 `Continuous` 间接享受拓扑。

---

## 13.4 概率与测度

概率在 mathlib 是测度论的应用：

```lean
open MeasureTheory ProbabilityTheory

#check MeasureSpace
-- 期望、独立性、大数律等在 Probability 命名空间
```

里程碑：多项式 Freiman–Ruzsa（PFR）形式化大量用概率方法——从论文到形式化速度以周计，展示前沿可及性。

---

## 13.5 组合与图论

```lean
variable {V : Type*} (G : SimpleGraph V)

#check G.Adj
#check SimpleGraph.Walk
```

拉姆齐、匹配、图参数……组合是活跃形式化区。

---

## 13.6 CSLib：计算机科学的形式化

**CSLib** 目标：给 CS 提供 mathlib 级基础——

- 算法与数据结构；
- 复杂度；
- 自动机与形式语言；
- 类型系统与语义。

mathlib 内已有 `Computability`（含图灵机等）。CSLib 独立发展意味着：**验证「真程序」的数学后盾更厚**——接第 14–16 章。

---

## 13.7 新边疆：Stat / Econ / Torch

| 库 | 方向 |
|----|------|
| StatLib | 数理统计 |
| EconLib | 经济理论（博弈、均衡） |
| TorchLean | 神经网络计算与 Lean 桥接 |

形式化正从纯数学 + 软件，溢到一切要严格推理的学科。

---

## 13.8 费马大定理项目：仰望星空

```lean
theorem FermatLastTheorem : ∀ n ≥ 3, ¬ ∃ x y z : ℕ,
    x ≠ 0 ∧ y ≠ 0 ∧ x ^ n + y ^ n = z ^ n
```

一行陈述，350 年历史。意义：

1. 检验超长人类推理链；
2. **倒逼**现代数论进入 mathlib（最大工程遗产）；
3. 探索 AI 辅助协作（blueprint 拆引理）。

浏览 ImperialCollegeLondon/FLT：看 **blueprint 依赖图**——大规模协作的组织方式值得任何验证项目抄作业。

---

## 13.9 迷你项目：三条分析「入口定理」

在 mathlib 项目中尝试：

```lean
import Mathlib

open Filter Topology

-- 1) 连续的多项式
example : Continuous (fun x : ℝ => x^2 + 3*x + 1) := by
  continuity  -- 或 fun_prop；失败则 continuous_add/continuous_pow 拼

-- 2) 数列 (n)/(n+1) → 1
example : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
  -- 思路：写成 1 - 1/(n+1)，再 tendsto 运算
  sorry  -- 练习：搜 tendsto_const、tendsto_one_div...

-- 3) 具体导数
example : deriv (fun x : ℝ => x * x) 5 = 10 := by
  simp [mul_comm, deriv_mul, deriv_id''] <;> norm_num
```

（`sorry` 处按你环境 `exact?` 填满——重点是走通工作流。）

---

## 13.10 踩坑对照

| 症状 | 处理 |
|------|------|
| `Tendsto` 看不懂 | 先当 API 用，后读滤子 |
| `continuity` 失败 | 拆成连续函数组合引理 |
| 积分例子编不过 | import 与 API 变更多，查文档 |
| 宇宙/`ℝ` 问题 | `import Mathlib.Data.Real.Basic` |
| 大项目克隆太大 | 只读 blueprint / 文档，不必全编译 |

---

## 13.11 本章小结

- **滤子**统一极限；`Tendsto` 一句通吃；
- 微积分、拓扑、测度、概率、图论主干已形式化；
- **CSLib** 与新兴库扩展边界；
- FLT/PFR 展示大问题驱动大建设。

---

## 练习

### ⭐ 基础

1. 证 `Continuous (fun x : ℝ => x^2)`。
2. `#check` 并阅读 `tendsto_add` 的类型。

### ⭐⭐ 进阶

3. 完成 `(n : ℝ)/(n+1) → 1`。
4. 计算 `deriv (fun x : ℝ => x^3) 2` 并 `norm_num`。
5. 在 SimpleGraph 上找一条「若边对称」相关引理名。

### ⭐⭐⭐ 硬核

6. 浏览 FLT blueprint，选一个叶子引理读陈述。
7. 读陶哲轩关于 PFR 形式化的博客摘要，列 3 条「人机协作」经验。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| MIL 拓扑/微分/积分章 | 主线教程 |
| Liquid Tensor 综述 | 硬分析里程碑 |
| PFR / FLT 仓库 | 大型项目组织 |
| CSLib README | CS 形式化地图 |

---

⬅️ [第 12 章](12-mathlib-algebra.md) ｜ ➡️ 下一章：[第 14 章　软件验证基础：让 bug 无处遁形](14-software-verification.md)
