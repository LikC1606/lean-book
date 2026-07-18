# 第 11 章　mathlib：一百万行形式化数学

> 本章目标：认识人类历史上最大的形式化数学库 mathlib4，学会搭建依赖它的项目，并掌握「在图书馆里找书」的核心技能。学完后你能独立新建 math 项目、缓存依赖、用四条渠道找到引理并完成小证明。

## 本章你会做出什么

1. `lake new ... math` + `cache get` 跑通环境；
2. 证明 `Real.sqrt 4 = 2` 与一两个不等式小定理；
3. 走通「猜名 → exact? → Loogle → LeanSearch」找引理流程；
4. 理解 mathlib 一般化与类型类组织的设计哲学。

---

## 11.1 mathlib 是什么？

mathlib 是 Lean 社区共建的形式化数学大厦。体量感：

- **百万行级**形式化数学，且持续增长；
- 覆盖代数、分析、拓扑、数论、组合、图论、概率、范畴、几何、泛函……
- 贡献者从本科生到菲尔兹奖得主；陶哲轩等是活跃用户；
- 配套 **CSLib**（计算机科学）专注算法与形式化 CS。

类比：

> 若 Lean 是 Python，mathlib 就像 NumPy + SciPy + pandas + 半个研究级数学库——没人从零发明实数，人人站在 mathlib 肩膀上。

费马大定理形式化、Liquid Tensor、AlphaProof 相关工作，几乎都建在 mathlib 之上。

---

## 11.2 配置一个 mathlib 项目（跟做）

网络正常时大约十几分钟。

### 第 1 步：创建

```bash
lake new my_math math    # math 模板自带 mathlib 依赖
cd my_math
```

或在已有项目 `lakefile.toml` 中 `require` mathlib（版本以模板 / 文档为准）：

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.x.0"   # 换成与 elan/toolchain 匹配的版本
```

### 第 2 步：更新 + 缓存（关键）

```bash
lake update
lake exe cache get          # 跳过这步 = 本地编译数小时
# lake exe cache get -j 8   # 可多线程
```

### 第 3 步：冒烟测试

`MyMath/Basic.lean` 或 `Test.lean`：

```lean
import Mathlib

theorem hello_math : Real.sqrt 4 = 2 := by
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
```

VS Code 打开或 `lake build`：无红线即成功。

> ⚠️ **首次** `import Mathlib` 会加载大量环境，可能卡几秒到十几秒。日常请**按需导入**，例如：
>
> ```lean
> import Mathlib.Data.Real.Basic
> import Mathlib.Tactic
> ```

### 常见配置翻车

| 症状 | 处理 |
|------|------|
| 编译 mathlib 本身到天荒地老 | 忘了 `lake exe cache get` |
| toolchain 与 mathlib 版本不匹配 | 对齐 `lean-toolchain` 与 `lakefile` rev |
| 公司网络拉不下 git | 配代理；或用社区镜像说明 |
| VS Code 不刷新 | 重启 Lean 服务器（扩展命令） |

---

## 11.3 寻宝图：库里有什么

`Mathlib/` 下按学科分目录（名称可能随版本微调）：

| 目录 | 内容 |
|------|------|
| `Algebra/` | 群环域模、线性代数基础 |
| `Analysis/` | 极限、微积分、测度 |
| `Topology/` | 拓扑、紧性、连续性 |
| `NumberTheory/` | 素数、同余、经典数论 |
| `Combinatorics/` | 组合、图论 |
| `Probability/` | 概率 |
| `LinearAlgebra/` | 向量空间、矩阵 |
| `Data/` | ℝ、ℂ、多项式、有限集… |
| `Tactic/` | `ring`、`linarith`、`gcongr`… |
| `CategoryTheory/` | 范畴论 |
| `Geometry/` | 几何 |
| `Computability/` | 可计算性 |

### 类型类层级（复习第 6 章）

```
Mul → Semigroup → Monoid → Group → CommGroup
Add + Mul + … → Ring → CommRing → Field
```

定理往往写在**最一般**的类上：「任意交换环中…」，整数、矩阵、函数空间一起受益。

---

## 11.4 核心技能：找到你要的引理

**会找定理 = 会用 mathlib。** 四条渠道：

### ① 命名约定（最重要）

模式大致：`对象/命名空间` + `操作` + `性质` + `方向/条件`，snake_case。

| 你想说的 | 常猜 |
|----------|------|
| a≤b → a+c≤b+c | `add_le_add_right` |
| 自然数乘法交换 | `Nat.mul_comm` |
| x≤y 且 y≤x ⇒ x=y | `le_antisymm` |
| 列表 append 长度 | `List.length_append` |

在编辑器里敲前缀，靠补全验证。

### ② Loogle（类型搜索）

[loogle.lean-lang.org](https://loogle.lean-lang.org/)：按类型模式搜，像定理界的 Hoogle。

- `_ + _ = _ + _`
- `_ ∣ _ → _ ∣ _ → _ ∣ _`

### ③ LeanSearch / Moogle（自然语言）

[leansearch.net](https://leansearch.net/)：英文大白话，例如 *addition commutative natural numbers*。

### ④ IDE：`exact?` / `apply?` / `rw?` / `hint`

证明现场直接搜（第 10 章）。

### 推荐工作流

```
猜名字 + 补全
    ↓ 失败
exact? / apply? / hint
    ↓ 失败
Loogle（类型）
    ↓ 失败
LeanSearch（自然语言）
    ↓ 失败
mathlib 文档站全文搜
    ↓ 失败
Zulip #new members 贴 MWE（附录 B）
```

---

## 11.5 完整例子：实数上的平方

```lean
import Mathlib

theorem sq_nonneg' (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

theorem sq_eq_zero_iff' (x : ℝ) : x ^ 2 = 0 ↔ x = 0 := by
  constructor
  · intro h
    have : x * x = 0 := by
      simpa [sq] using h
    rcases mul_eq_zero.mp this with h' | h' <;> exact h'
  · intro h
    simp [h]
```

观察：

- `ℝ` 输入 `\R`；
- **先搜库**（`sq_nonneg`）再动手；
- `norm_num` / `simp` / `rcases` 组合收尾。

### 带 `calc` + `gcongr` 的估计

```lean
import Mathlib

theorem triangle_ineq_demo (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add a b

example (x y : ℝ) (h : |x - y| < (0.01 : ℝ)) :
    |x^2 - y^2| ≤ (|x| + |y|) * 0.01 := by
  have hyx : |x - y| ≤ (0.01 : ℝ) := le_of_lt h
  calc |x^2 - y^2|
      = |(x - y) * (x + y)| := by ring
    _ = |x - y| * |x + y| := by rw [abs_mul]
    _ ≤ |x - y| * (|x| + |y|) := by
        gcongr
        exact abs_add x y
    _ ≤ (|x| + |y|) * 0.01 := by
        rw [mul_comm]
        gcongr
        · exact abs_nonneg _
        · exact hyx
```

（若你本地 mathlib 版本上 `ring`/`gcongr` 细节略有出入，以 `exact?` 与报错为准微调——**版本漂移是正常的**，思想不变。）

`gcongr`：处理「两边同乘非负数保留 ≤」一类单调性，分析证明利器。

---

## 11.6 迷你实录：从空项目到三个定理

建议你完整敲一遍：

```lean
import Mathlib

-- 定理 1：中点夹在两端之间
example (a b : ℝ) (h : a ≤ b) :
    a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b := by
  constructor <;> linarith

-- 定理 2：偶数加偶数
example (a b : ℤ) (ha : Even a) (hb : Even b) : Even (a + b) := by
  exact Even.add ha hb   -- 也可 exact?

-- 定理 3：sqrt 后平方回来
example : Real.sqrt 2 ^ 2 = 2 := by
  have : (0 : ℝ) ≤ 2 := by norm_num
  exact Real.sq_sqrt this
```

每证完一个，用 `#print axioms` 看依赖（常会看到经典公理，正常）。

---

## 11.7 mathlib 设计哲学（少走弯路）

1. **尽量一般化**：能对拓扑群证的，不对「仅实数」证；前提里一长串 `[CommRing α] [...]` 是特性不是折磨。
2. **定义求复用**：滤子（Filter）统一极限语言等——初学觉得绕，是为了全域通用。
3. **经典逻辑默认**：排中律、选择随便用。
4. **文档字符串**：悬停有说明；[mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/) 可搜。
5. **性能与缓存**：永远先 `cache get`；CI 也靠缓存活着。

### 读一般化定理的方法

看到：

```lean
variable {α : Type*} [LinearOrderedField α]
theorem foo (x : α) : ...
```

心译：「任意线性有序域上……」→ 对 `ℚ`、`ℝ` 都适用。你的目标若是 `ℝ`，直接 `foo` 即可。

---

## 11.8 踩坑对照

| 症状 | 处理 |
|------|------|
| 找不到「很显然」的引理 | 可能写在更一般的类上；用类型搜 |
| `import Mathlib` 太慢 | 改细粒度 import |
| 证明在 A 机器过 B 不过 | toolchain / mathlib rev 不一致 |
| `linarith` 失败 | 非线性项；先 `ring_nf` 或拆 `have` |
| Unicode 输不出 | `\R` `\le` `\in` 等缩写 |
| 想改 mathlib 源码 | 不要；上游 PR 或本地 `patch` 需谨慎 |

---

## 11.9 本章小结

- mathlib = Lean 的数学操作系统：巨型、类型类、经典数学；
- 配置三板斧：`lake new … math` → `lake update` → **`lake exe cache get`**；
- 找定理：命名约定、Loogle、LeanSearch、`exact?`；
- 节奏：**先搜库 → 再拆解 → 自动化收尾**；
- 读定理时习惯「一般类上的结果」。

---

## 练习

### ⭐ 基础

1. 配置项目并跑通 `Real.sqrt 4 = 2`。
2. Loogle 搜 `_ + _ = _ + _`，记下 3 个结果的名字。

### ⭐⭐ 进阶

3. 证明：`example (a b : ℝ) (h : a ≤ b) : a ≤ (a + b) / 2 ∧ (a + b) / 2 ≤ b`。
4. 证明两偶数之和为偶（`Even`，优先 `exact?`）。
5. 证明 `Real.sqrt 2 ^ 2 = 2`。

### ⭐⭐⭐ 硬核

6. 在 [MIL](https://leanprover-community.github.io/mathematics_in_lean/) 做完 Introduction 后的第一个练习文件，对照本书策略章。
7. 任选一个你熟的本科定理（如「√2 无理」），在 mathlib 里**搜索是否已有**，阅读其证明骨架（不必全懂）。

---

## 延伸阅读

| 资源 | 用途 |
|------|------|
| [*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean/) | **官方 mathlib 教程，强烈跟做** |
| [mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/) | API 文档 |
| [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean) | 快速文件型入门 |
| Lean for the Curious Mathematician 录像 | 数学家向演讲 |
| 第 12–13 章 | 代数与分析专题 |

下一章我们沿着类型类梯子往上爬：从群到环到域。

---

⬅️ [第 10 章](10-tactics-toolbox.md) ｜ ➡️ 下一章：[第 12 章　代数结构：从群到环域](12-mathlib-algebra.md)
