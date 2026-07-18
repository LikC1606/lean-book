# 第 11 章　mathlib：一百万行形式化数学

> 本章目标：认识人类历史上最大的形式化数学库 mathlib4，学会搭建依赖它的项目，并掌握"在图书馆里找书"的核心技能。

## 11.1 mathlib 是什么？

mathlib（数学库）是 Lean 社区共建的形式化数学大厦。几个数字感受下它的体量：

- **超过 100 万行**形式化数学代码，且每天还在增长；
- 覆盖：代数（群环域模）、分析（微积分、测度论）、拓扑、数论、组合、图论、概率、范畴论、微分几何、泛函分析……
- 数百名贡献者，从本科生到菲尔兹奖得主（陶哲轩是活跃用户）；
- 配套的 **CSLib**（计算机科学库）也已启动，专注算法与数据结构的形式化。

它为什么重要？打个比方：

> 如果 Lean 是 Python，mathlib 就是 NumPy + SciPy + pandas + scikit-learn 的总和——没有人"从零开始"做数学，所有人都站在 mathlib 的肩膀上。

第 1 章提到的那些明星项目——费马大定理形式化、Liquid Tensor Experiment、AlphaProof 的几何题——全部构建在 mathlib 之上。

## 11.2 配置一个 mathlib 项目

跟着做，15 分钟搞定（网络好的话）。

**第 1 步**：创建项目（推荐用 mathlib 官方模板仓库或者手动配）：

```bash
lake new my_math math    # math 模板会自动配置 mathlib 依赖
cd my_math
```

或者手动在已有项目的 `lakefile.toml` 中添加：

```toml
[require]
mathlib = { git = "https://github.com/leanprover-community/mathlib4.git", rev = "v4.x.x" }
```

**第 2 步**：下载预编译缓存（**关键！跳过这步你将编译几个小时**）：

```bash
lake update
lake exe cache get
```

**第 3 步**：测试。创建 `Test.lean`：

```lean
import Mathlib

theorem hello_math : Real.sqrt 4 = 2 := by
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
```

`lake build` 或 VS Code 打开，看到没有红色波浪线——恭喜，你接入了全人类的数学知识库。

> ⚠️ 首次 `import Mathlib` 会加载整个库，VS Code 里首次打开稍慢（几秒到十几秒），属正常现象。之后可以按需导入具体模块（如 `import Mathlib.Data.Real.Basic`）加快响应。

## 11.3 mathlib 里有什么：一张寻宝图

mathlib 的文件按数学学科组织在 `Mathlib/` 目录下：

| 目录 | 内容 |
|------|------|
| `Mathlib/Algebra/` | 群、环、域、模、线性代数基础 |
| `Mathlib/Analysis/` | 极限、连续、微分、积分、测度论 |
| `Mathlib/Topology/` | 拓扑空间、连续性、紧性 |
| `Mathlib/NumberTheory/` | 数论：素数、同余、二次互反律 |
| `Mathlib/Combinatorics/` | 组合、图论 |
| `Mathlib/Probability/` | 概率论 |
| `Mathlib/LinearAlgebra/` | 向量空间、矩阵 |
| `Mathlib/Data/` | 具体数系与结构：ℝ、ℂ、多项式、有限集 |
| `Mathlib/Tactic/` | mathlib 扩展的策略（`ring`、`linarith`、`gcongr`…） |
| `Mathlib/CategoryTheory/` | 范畴论 |
| `Mathlib/Geometry/` | 几何学 |
| `Mathlib/Computability/` | 可计算性理论、图灵机 |

数学对象基本采用**类型类层级**组织（回忆第 6 章）：

```
Mul → Semigroup → Monoid → Group → CommGroup
Add + Mul + ... → Ring → CommRing → Field
```

写定理时你面对的不是"整数的加法交换律"，而是"**任意交换环/群中**的交换律"——一次证明，处处可用。

## 11.4 核心技能：找到你要的引理

mathlib 有几万条定理。**找定理的能力 = 使用 mathlib 的能力**。四个渠道：

### ① 命名约定（最重要！）

mathlib 的命名极其规律：`主题.操作_性质_条件`。猜一猜下面定理叫什么：

- "a ≤ b → a + c ≤ b + c"？→ `add_le_add_right`
- "自然数乘法交换律"？→ `Nat.mul_comm`
- "实数中 x ≤ y 且 y ≤ x 则 x = y"？→ `le_antisymm`

规律：**操作名 + 性质 + 方向/条件**， snake_case。猜出大概名字后在 VS Code 里输几个字母，自动补全会给你惊喜。

### ② Loogle（类型搜索）

[loogle.lean-lang.org](https://loogle.lean-lang.org/)——**按类型签名搜定理**，像定理界的 Hoogle：

- 搜 `"a + b = b + a"` 的实数版本？输入 `_ + _ = _ + _`；
- 想找"从 `a ∣ b` 和 `b ∣ c` 推出 `a ∣ c`"？输入 `_ ∣ _ → _ ∣ _ → _ ∣ _`。

### ③ LeanSearch / Moogle（自然语言搜索）

[leansearch.net](https://leansearch.net/)——直接用大白话搜："addition is commutative on natural numbers"。AI 语义匹配。

### ④ `exact?` / `apply?`（IDE 内搜索）

第 10 章已介绍：在证明现场直接让 Lean 搜库。

> 💡 实战工作流：先猜名字 → 补全验证 → 不行就 `exact?` → 还不行上 Loogle → 再不行 Zulip 提问。

## 11.5 实数初体验：一个完整例子

来点真数学。证明：**对任意实数 x，x² ≥ 0，且 x² = 0 当且仅当 x = 0**。

```lean
import Mathlib

theorem sq_nonneg' (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x   -- 库里有现成的！

theorem sq_eq_zero_iff' (x : ℝ) : x ^ 2 = 0 ↔ x = 0 := by
  constructor
  · intro h
    -- x² = 0 ⟹ x = 0：利用 "x*y=0 ⟹ x=0 或 y=0"
    have : x * x = 0 := by rw [← sq, h]
    rcases mul_eq_zero.mp this with h' | h' <;> exact h'
  · intro h
    rw [h]; norm_num
```

观察：

- `ℝ` 是实数（输入 `\R`），`sq_nonneg`、`mul_eq_zero` 都是 mathlib 现成引理；
- 养成"**先搜库再动手**"的习惯：mathlib 里很可能已经有你需要的定理或其近亲。

再看一个带 `calc` 的分析味道例子：

```lean
theorem triangle_ineq_demo (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add a b

example (x y : ℝ) (h : |x - y| < 0.01) : |x^2 - y^2| ≤ (|x| + |y|) * 0.01 := by
  calc |x^2 - y^2|
      = |(x - y) * (x + y)|   := by ring_nf
    _ = |x - y| * |x + y|     := by rw [abs_mul]
    _ ≤ |x - y| * (|x| + |y|) := by
        gcongr                       -- 单调性策略：化归为 |x+y| ≤ |x|+|y|
        exact abs_add x y
    _ ≤ (|x| + |y|) * 0.01       := by
        rw [mul_comm]
        gcongr                       -- 化归为 |x-y| ≤ 0.01
        exact le_of_lt h
```

`gcongr`（generalized congruence）自动处理"两边同乘一个非负数保持 ≤"这类单调性推理——分析证明的得力助手。

## 11.6 mathlib 的设计哲学（知道这些少走弯路）

1. **一切尽量一般化**：能对拓扑群证的，绝不对实数证。所以你常看到定理前提里有一堆 `[CommRing α]` `[MeasurableSpace β]` 这样的类型类参数；
2. **定义要"巧"**：比如实数没有直接定义减法结合律，而是统一从公理出发；`Filter`（滤子）统一处理各种极限……初学时某些定义显得绕，但它们是为了**最大复用**；
3. **`classical` 随便用**：mathlib 是经典数学的天下，排中律、选择公理随意使用（编译时自动处理）；
4. **文档字符串齐全**：悬停任何定义都有说明，`Mathlib.` 开头的官网文档可全文搜索；
5. **性能意识**：大库编译压力大，社区有整套缓存（`lake exe cache get`）和 CI 基础设施。

## 11.7 本章小结

- mathlib = Lean 的数学操作系统，百万行级、覆盖全学科、类型类组织；
- 项目配置三板斧：`lake new ... math` → `lake update` → `lake exe cache get`；
- 找定理四渠道：命名约定、Loogle、LeanSearch、`exact?`；
- 写数学证明的节奏：**先搜库、再拆解、自动化收尾**。

## 练习

1. 配置好 mathlib 项目，跑通 11.2 节的 `Real.sqrt 4 = 2`；
2. 在 Loogle 上搜索类型 `"_ + _ - _ = _"`，观察都能找到什么；
3. 用 mathlib 证明：`example (a b : ℝ) (h : a ≤ b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b`（提示：`constructor` + `linarith`）；
4. 证明"两个偶数之和为偶"：mathlib 中偶数谓词是 `Even`，试着用 `exact?` 找 `Even.add`；
5. 挑战：证明 `Real.sqrt 2 ^ 2 = 2`（提示：`Real.sq_sqrt`，需要 2 ≥ 0 的前提）。

## 延伸阅读

- 《Mathematics in Lean》（MIL）——mathlib 官方教材，免费在线；
- mathlib4 文档站：leanprover-community.github.io/mathlib4_docs/；
- 视频：YouTube 上 "Lean for the Curious Mathematician" 系列讲座。

---

⬅️ [第 10 章](10-tactics-toolbox.md) ｜ ➡️ 下一章：[第 12 章　代数结构：从群到环域](12-mathlib-algebra.md)
