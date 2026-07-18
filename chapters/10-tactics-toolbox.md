# 第 10 章　策略工具箱大全

> 本章目标：认识 Lean 证明工具箱中的"重型装备"——自动化策略、结构化证明利器和 mathlib 专属神器。

第 9 章给了你螺丝刀和锤子，本章给你电钻和数控机床。

## 10.1 自动化三剑客：omega、grind、decide

### `omega`：线性算术终结者

凡是涉及 `Nat`/`Int` 的**线性**（没有变量乘变量）加减比较，`omega` 几乎必杀：

```lean
example (a b : Nat) (h1 : a + 3 ≤ b) (h2 : b ≤ a + 5) : a + 1 ≤ b := by omega
example (x y : Int) (h : 2 * x + y = 7) (h' : x - y = 2) : x = 3 := by omega
```

### `grind`：新一代全能选手

`grind` 是 Lean 在 2025 年推出的强力自动化策略，灵感来自 SMT 求解器（作者正是 Z3 之父 Leo de Moura）。它擅长：

- 线性不等式组；
- 模式匹配/定义展开后的等式；
- 带未解释函数符号 + 量词实例化（E-matching）的推理。

```lean
example (x y : Int)
    (h1 : 27 ≤ 11 * x + 13 * y) (h2 : 11 * x + 13 * y ≤ 45)
    (h3 : -10 ≤ 7 * x - 9 * y) (h4 : 7 * x - 9 * y ≤ 4) :
    7 * x - 9 * y ≤ 4 := by grind

-- 给它引理提示，威力更大
example (a b : Nat) (h : a % b = 0) : b ∣ a := by grind [Nat.dvd_of_mod_eq_zero]
```

使用心法：**`grind [引理1, 引理2]`**——把你认为相关的引理喂给它当线索。

### `decide`：有限问题直接算

```lean
example : Nat.Prime 97 := by decide
example : 2^10 = 1024 := by decide
```

## 10.2 `simp` 深入：化简器的正确打开方式

`simp` 背后是一个由数千条 `@[simp]` 引理组成的重写系统。进阶用法：

```lean
simp only [Nat.add_zero]   -- 只用指定引理（精确、快、可复现）
simp [myDef]               -- 把定义 myDef 展开参与化简
simp at h ⊢                -- 同时化简假设 h 和目标（⊢ 输入 \|-）
simp_all                   -- 上下文、目标全化简，还尝试互相利用
```

经验法则：

- 收尾（close the goal）时用 `simp` 很爽，但**中间步骤**建议用 `simp only [...]`——`simp` 规则库会变，大库（mathlib）里的证明靠 `simp only` 保持长期稳定；
- `simp?`（mathlib 提供）会**告诉你**它用了哪些引理，方便你换成 `simp only`：
  ```lean
  example (xs : List Nat) : xs.reverse.reverse = xs := by simp?  -- 提示 Try this: simp only [List.reverse_reverse]
  ```

## 10.3 等式链：`calc` 写出教科书式推导

数学证明里最常见的形式："A = B = C = D"。`calc` 让 Lean 证明长得和纸面推导一模一样：

```lean
theorem sum_two_mul (n : Nat) : 2 * (n + 1) = 2 * n + 2 := by
  calc 2 * (n + 1)
      = 2 * n + 2 * 1 := by rw [Nat.mul_add]
    _ = 2 * n + 2     := by rw [Nat.mul_one]
```

每一行提供一步证明（通常是 `by rw/simp/omega`），`_` 表示上一行的结果。`calc` 也支持 `<`、`≤`、`|` 等传递关系——mathlib 里大量分析学证明都是长串 `calc`。

## 10.4 结构化证明进阶

### `match`（策略版）：在证明中模式匹配

```lean
example (n : Nat) : (match n with | 0 => 0 | k+1 => k) ≤ n := by
  match n with
  | 0 => simp
  | k+1 => simp
```

### `rcases` / `rintro`：花式拆解

mathlib 提供的增强版 `obtain`/`intro`，支持嵌套模式：

```lean
example (h : A ∧ (B ∨ C)) : (A ∧ B) ∨ (A ∧ C) := by
  rcases h with ⟨ha, hb | hc⟩   -- 一步到位：拆 ∧，再对 ∨ 分支
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hc⟩

example : A ∧ B → B := by
  rintro ⟨_, hb⟩   -- intro 的同时拆包，_ 表示不关心
  exact hb
```

### `by_cases` 与 `classical`：排中律的开关

```lean
example (P : Prop) : P ∨ ¬P := by
  by_cases h : P     -- 需要经典逻辑，Lean 自动引入 Classical
  · exact Or.inl h
  · exact Or.inr h
```

数学里"分情况：x = 0 或 x ≠ 0"这类推理全靠它。

### `push_neg`：把否定推进去

目标是 `¬ (∀ x, P x)`？`push_neg` 变成 `∃ x, ¬P x`——反证法、构造反例的利器：

```lean
example (h : ¬ ∀ n : Nat, n ≤ 10) : ∃ n, n > 10 := by
  push_neg at h
  exact h
```

## 10.5 mathlib 的"专科医生"

以下策略来自 mathlib（需 `import Mathlib`），第四部分会天天见：

| 策略 | 专长 | 示例 |
|------|------|------|
| `ring` | 交换环上的多项式等式 | `(a+b)² = a²+2ab+b²` |
| `ring_nf` | 同上，但只做规范化 | 用于中间步骤 |
| `field_simp` | 域上的分式化简 | 通分消分母 |
| `linarith` | 有序域上的线性算术 | 实数不等式组 |
| `positivity` | 证明表达式为正 | `0 < x^2 + 1` |
| `norm_num` | 数值计算类命题 | `(100 : ℝ) * 0.1 = 10` |
| `gcongr` | 单调性 congruence | `x ≤ y → f x ≤ f y` 型 |
| `polyrith` | 多项式等式（调外部工具） | 复杂恒等式 |
| `tauto` | 命题逻辑自动推理 | 纯逻辑组合 |
| `aesop` | 通用自动化搜索 | 各种杂活 |
| `exact?` / `apply?` | **帮你找引理！** | 卡壳时首选 |

### `exact?`：最值得记住的"外挂"

不知道该用哪个引理？让 Lean 自己在库里搜：

```lean
example (n : Nat) : n + 0 = n := by exact?
-- 提示：Try this: exact Nat.add_zero n
```

`exact?`、`apply?`、`rw?`、`hint`（一键试一串常用策略）是探索 mathlib 这座巨型图书馆的向导。

## 10.6 证明调试技巧

1. **`show`**：改变目标的显示形式（语义不变），帮你看清"现在到底要证什么"：
   ```lean
   show 2 * (n + 1) = 2 * n + 2
   ```
2. **`guard_target`** / `guard_hyp`：断言当前目标/假设的形状，用于测试和教学；
3. **`extract_goal`**：把当前状态整理成一个独立定理模板，方便重构；
4. **`set x := expr with hx`**：给复杂表达式起别名，让目标清爽；
5. **`conv`**：进入"转换模式"，精确对目标的**子表达式**做重写（`rw` 做不到聚焦时用）：
   ```lean
   example (a b c : Nat) (h : b = c) : a + (b + 1) = a + (c + 1) := by
     conv => lhs; rw [h]   -- 只在等式左边操作
   ```

## 10.7 策略选择的"决策树"

实战中面对一个目标，心里过一遍这棵树：

```
目标是纯数值计算？         → decide / norm_num
线性整数/自然数算术？      → omega / grind
多项式恒等式？            → ring / ring_nf
线性实数不等式？          → linarith / grind
上下文里有现成答案？       → assumption / exact h / simp_all
目标是 ∧/∃/↔？           → constructor / refine ⟨_, ?_⟩
手里有 ∧/∃/∨ 假设？      → obtain / rcases / cases
涉及归纳类型全体？         → induction
需要等式变形？            → rw / calc / conv
卡住了？                  → exact? / hint / grind [线索引理...]
都不行？                  → 该拆出 have 中间引理了
```

## 10.8 本章小结

- 自动化三剑客：`omega`（线性算术）、`grind`（全能新星）、`decide`（可判定计算）；
- `simp only` 保稳定，`simp?` 找引理；
- `calc` 写出与纸面一致的等式链；`rcases`/`rintro` 花式拆包；
- `by_cases` + `push_neg` 驾驭经典逻辑；
- mathlib 专科策略：`ring`、`linarith`、`positivity`、`norm_num`、`gcongr`……
- **找引理神器：`exact?`、`apply?`、`rw?`、`hint`**——卡壳时的第一反应。

## 练习

1. 用 `calc` 证明 `(a + b) + (a + b) = 2 * a + 2 * b`（`Nat` 上，只用 `rw` 和算术引理）；
2. 用 `omega` 证明：`∀ a b c : Nat, a ≤ b → b ≤ c → a ≤ c + 1`；
3. 用 `rcases` 一行拆完 `h : (A ∧ B) ∨ (C ∧ D)` 并分别完成证明 `(A ∨ C)`；
4. 在装有 mathlib 的项目里，用 `exact?` 找出"列表长度与 append"的引理：`example (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length`；
5. 用 `grind` 验证：`example (n : Nat) : n ≤ n + 1 ∧ (n + 1) * 2 = 2 * n + 2`。

## 延伸阅读

- mathlib 文档的 [tactic 列表](https://leanprover-community.github.io/mathlib4_docs/)；
- Lean 官方语言参考中的 "The Tactic Language" 一章；
- Heather Macbeth 的 [mathlib 策略使用笔记](https://hrmacbeth.github.io/math2001/)。

---

⬅️ [第 9 章](09-tactics-basics.md) ｜ ➡️ 下一章：[第 11 章　mathlib：一百万行形式化数学](11-mathlib-intro.md)
