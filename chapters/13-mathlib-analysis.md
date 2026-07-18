# 第 13 章　分析、拓扑与计算机科学数学

> 本章目标：一窥 mathlib 中"硬数学"（极限、连续、测度）的形态，以及新兴的计算机科学库 CSLib，理解形式化数学的前沿在哪里。

## 13.1 极限：滤子的胜利

数学分析的核心是极限。mathlib 面对一个难题：数列极限、函数极限、趋于无穷的极限、左极限右极限……定义能不能统一？

mathlib 的答案：**滤子**（filter）。这是一种"越来越小的集合族"的抽象，可以把所有极限统一成一句话：

```lean
-- "f 在 x 趋于 (滤子) l 时的极限是 y" 统一写作：
Tendsto f l (𝓝 y)
```

`𝓝 y`（输入 `\Nb`）是"y 的邻域滤子"。于是：

- 数列 `u : ℕ → ℝ` 收敛到 `a`：`Tendsto u atTop (𝓝 a)`
- 函数在 `x₀` 连续：`ContinuousAt f x₀`，即 `Tendsto f (𝓝 x₀) (𝓝 (f x₀))`
- `x → +∞` 时的极限：`Tendsto f atTop (𝓝 a)`

同一套 `Tendsto` 定理（极限的加法、乘法、复合……）**通吃所有极限**。这是 mathlib 设计哲学的代表作：一个抽象，处处复用。

看个具体例子：

```lean
import Mathlib

open Filter Topology

-- 数列 1/n → 0
example : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := by
  simpa using tendsto_one_div_atTop_nhds_zero_nat

-- 连续函数复合仍连续
example {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (g ∘ f) := hg.comp hf
```

## 13.2 微积分：导数与积分

```lean
-- 导数
example : deriv (fun x : ℝ => x ^ 2) 3 = 6 := by
  simp [deriv_pow]

-- 基本定理：∫x in a..b, x dx = (b² - a²)/2 之类
example : ∫ x in (0:ℝ)..1, x = 1 / 2 := by
  norm_num [integral_id]   -- 具体计算有 intervalIntegral 工具链
```

mathlib 的微积分覆盖：一元/多元导数（Fréchet 导数）、黎曼/勒贝格积分、微积分基本定理、泰勒展开……足够支撑严肃的数学研究（Liquid Tensor Experiment 就大量动用了这部分）。

## 13.3 拓扑：开集的世界

```lean
variable {X : Type*} [TopologicalSpace X]

example (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) : IsOpen (U ∩ V) :=
  hU.inter hV

-- 紧集：任意开覆盖有有限子覆盖
example (s : Set X) (hs : IsCompact s) : True := trivial  -- IsCompact 是核心概念
```

拓扑部分的长项：度量空间、一致空间、紧性（Tychonoff 定理）、连通性、完备性——这些都是现代分析的地基，mathlib 全部形式化了。

## 13.4 概率论与测度论

概率论在 mathlib 里是测度论的应用（这本身就是现代概率论的正统做法）：

```lean
open MeasureTheory ProbabilityTheory

-- 随机变量、期望、方差、独立性、大数定律、中心极限定理……
#check probability_theory
```

里程碑：2023–2024 年，陶哲轩与社区合作形式化了 **多项式 Freiman–Ruzsa 猜想**的证明（加性组合的重要成果），大量使用概率方法——从论文到形式化只用了几周，证明了 Lean 已能跟上前沿研究的速度。

## 13.5 组合与图论

```lean
-- 图：SimpleGraph V
variable {V : Type*} (G : SimpleGraph V)

#check G.Adj        -- 邻接关系
#check SimpleGraph.Walk   -- 路径（归纳定义）
```

拉姆齐定理、四色定理的图论表述、匹配理论……组合数学是形式化的活跃领域。

## 13.6 CSLib：计算机科学的形式化

数学之外，社区近年发起了 **CSLib**（Computer Science Library），目标是为计算机科学提供 mathlib 级别的形式化基础：

- 算法与数据结构（排序、搜索树、堆）；
- 复杂度理论（时间/空间复杂度类）；
- 自动机、形式语言、可计算性；
- 类型系统与程序语义。

mathlib 内部其实已有不少 CS 内容（`Mathlib.Computability.TuringMachine` 里甚至有图灵机的形式化和通用图灵机构造！）。CSLib 的独立发展意味着：**用 Lean 验证"真正的程序"会越来越顺手**——这也正是本书第 14–16 章的数学后盾。

## 13.7 统计与经济：形式化的新边疆

Lean 的应用边界还在扩张，2025–2026 年的新动向：

- **StatLib**：数理统计库（估计量、检验、渐近理论）；
- **EconLib**（Axiom 公司发起）：经济学理论形式化（博弈论、一般均衡）；
- **TorchLean**：连接 PyTorch 与 Lean，探索对神经网络计算的验证。

形式化方法正在从"纯数学 + 软件"溢出到一切**需要严格推理的学科**。

## 13.8 费马大定理项目：仰望星空

本章以整个社区的"珠穆朗玛"收尾：**Fermat's Last Theorem 形式化项目**（Kevin Buzzard 领导，多方资助）。

费马大定理说：方程 `xⁿ + yⁿ = zⁿ`（n ≥ 3）没有正整数解。Wiles 1995 年的证明动用了 20 世纪数学最深的工具（椭圆曲线、模形式、Galois 表示）。形式化它的意义：

1. 检验这条人类推理长链的每一个环节；
2. 倒逼 mathlib 形式化大量现代数论（这是最实际的遗产——就像登月计划留下了无数技术）；
3. 探索人机协作做前沿数学的新范式（项目部分工作已由 AI 辅助推进，陶哲轩等人参与讨论）。

其 Lean 中的最终目标陈述朴素得可爱：

```lean
theorem FermatLastTheorem : ∀ n ≥ 3, ¬ ∃ x y z : ℕ,
    x ≠ 0 ∧ y ≠ 0 ∧ x ^ n + y ^ n = z ^ n
```

一行代码，承载了 350 年的数学史。

## 13.9 本章小结

- mathlib 用**滤子**统一极限，`Tendsto` 一句通吃所有收敛；
- 微积分、拓扑、测度、概率、组合……现代数学主干均已形式化；
- **CSLib** 把同样的方法带给计算机科学，是软件验证的数学后盾；
- 统计（StatLib）、经济（EconLib）、AI（TorchLean）等新边疆正在开辟；
- 费马大定理项目展示了社区"以大问题倒逼大建设"的雄心。

## 练习

1. 用 mathlib 证明数列 `(n : ℕ) ↦ (n : ℝ) / (n + 1)` 收敛到 1（提示：改写为 `1 - 1/(n+1)`，或搜索相关 tendsto 引理）；
2. 证明 `Continuous (fun x : ℝ => x^2 + 3*x + 1)`（提示：`continuous_pow`、`continuous_add` 等引理组合，或试 `fun_prop` 策略）；
3. 计算：`deriv (fun x : ℝ => x * x) 5` 并用 `simp`/`norm_num` 验证；
4. 浏览 FLT 项目的 GitHub 仓库（ImperialCollegeLondon/FLT），看看"蓝点依赖图"（项目把证明拆成带依赖关系的小引理），感受大规模形式化协作的组织方式。

## 延伸阅读

- 《Mathematics in Lean》第 9–11 章（拓扑、微分、积分与测度）；
- 论文：*The Liquid Tensor Experiment*（Scholze 的博客综述）；
- PFR 项目总结：陶哲轩的博客文章。

---

⬅️ [第 12 章](12-mathlib-algebra.md) ｜ ➡️ 下一章：[第 14 章　软件验证基础：让 bug 无处遁形](14-software-verification.md)
