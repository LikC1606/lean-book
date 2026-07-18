# 第 8 章　命题即类型：证明的本质

> 本章目标：理解 Lean 证明体系的根基——柯里-霍华德对应。这一章是全书理论性最强的一章，但我们会用大量例子把它"落地"。

从本章开始，我们进入 Lean 的第二重身份：**定理证明器**。

## 8.1 一个惊人的等同

1930 年代，逻辑学家柯里（Haskell Curry）和霍华德（William Howard）先后注意到一件奇妙的事：

| 逻辑世界 | 编程世界 |
|----------|----------|
| 命题 | 类型 |
| 命题的证明 | 该类型的一个值（程序） |
| 合取 A ∧ B（A 且 B） | 乘积类型 A × B（二元组） |
| 析取 A ∨ B（A 或 B） | 和类型 A ⊕ B（`Sum`，二选一） |
| 蕴含 A → B | 函数类型 A → B |
| 全称 ∀ x, P x | 依赖函数类型 (x : α) → P x |
| 存在 ∃ x, P x | 依赖对类型 Σ x, P x（`Exists` 是其在 Prop 的版本） |
| 真（True） | 单位类型（`True` 有一个无内容构造子） |
| 假（False） | 空类型（`False` 没有任何构造子） |

这就是**柯里-霍华德对应**（也叫"命题即类型"）。它不是哲学类比，而是 Lean 的**字面实现方式**：

> 在 Lean 里，**证明一个命题 = 写出一个以该命题为类型的项**。检查证明 = 类型检查。

所以 Lean 不需要两套系统：它的**同一个内核**既检查程序的类型，也检查证明的正确性。内核很小（几千行）、独立于其他部分——这就是"可信内核"（trusted kernel）设计：全世界上百万行数学库的正确性，最终都归约到这个小内核的检查上。

## 8.2 Prop：命题的宇宙

命题们住在自己的宇宙里：`Prop`。

```lean
#check (1 + 1 = 2)        -- 1 + 1 = 2 : Prop
#check (∀ n : Nat, n + 0 = n)  -- : Prop
#check (2 + 2 = 5)        -- 2 + 2 = 5 : Prop（假命题也是命题！）
```

注意：**假命题也是合法的 Prop**，就像 `False` 也是合法的类型——它只是没有值（没有证明）而已。"是命题"和"成立"是两回事。

给出证明，就是给这个 Prop 找一个"居民"（项）：

```lean
theorem two_eq_two : 2 = 2 := rfl        -- rfl 是等号的自反性证明项
theorem trivial_true : True := True.intro -- True 的唯一构造子
```

## 8.3 逻辑连词的"编程实现"

逐个看逻辑连词在 Lean 里长什么样。

### 合取 ∧（并且）

`A ∧ B` 的证明就是一个**二元组**：A 的证明配 B 的证明。

```lean
theorem and_demo : 1 + 1 = 2 ∧ 2 + 2 = 4 :=
  ⟨rfl, rfl⟩            -- ⟨ , ⟩ 是构造对的记法（输入 \< \>）

-- 拆开用：
#check And.left  -- And 的第一部分
#check And.right -- 第二部分
```

### 析取 ∨（或者）

`A ∨ B` 的证明是**二选一**并给出所选那边的证明：

```lean
theorem or_demo_left : 1 + 1 = 2 ∨ 2 + 2 = 5 :=
  Or.inl rfl          -- inl = 选左边

theorem or_demo_right : 2 + 2 = 5 ∨ 1 + 1 = 2 :=
  Or.inr rfl          -- inr = 选右边
```

### 蕴含 →（推出）

`A → B` 的证明就是一个**函数**：把 A 的任意证明变成 B 的证明。

```lean
theorem imp_demo : 2 = 2 → 3 = 3 := fun _ => rfl

-- 更真实的例子：从前提推导结论
theorem succ_eq_of_eq (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
```

读 `succ_eq_of_eq` 的类型："给我两个自然数和一个 `a = b` 的证明，我还你一个 `a + 1 = b + 1` 的证明"。定理就是函数，**应用定理就是函数调用**：

```lean
#check succ_eq_of_eq 3 3 rfl   -- 类型：3 + 1 = 3 + 1，一个现成的证明
```

### 否定 ¬（并非）

`¬A` 定义为 `A → False`——"从 A 的证明能推出矛盾"。

```lean
theorem one_ne_two : ¬ (1 = 2) := by
  intro h          -- 假设 1 = 2
  contradiction    -- 它本身就矛盾（decide 也行）
```

### 等价 ↔（当且仅当）

`A ↔ B` 就是 `(A → B) ∧ (B → A)` 的打包：

```lean
theorem iff_demo : (1 + 1 = 2) ↔ (2 = 1 + 1) :=
  ⟨fun h => h.symm, fun h => h.symm⟩
```

## 8.4 量词：∀ 与 ∃

### 全称量词 ∀

`∀ n : Nat, P n` 就是依赖函数类型：给任意 `n`，产出 `P n` 的证明。

```lean
theorem add_zero_forall : ∀ n : Nat, n + 0 = n := fun n => rfl
```

应用一个 ∀ 定理 = 传参调用：

```lean
#check add_zero_forall 42   -- 42 + 0 = 42 的证明
```

### 存在量词 ∃

`∃ n : Nat, P n` 的证明是"**一个具体的见证 n，配上 P n 的证明**"：

```lean
theorem exists_even : ∃ n : Nat, n + n = 4 :=
  ⟨2, rfl⟩        -- 见证 2 + 等式证明
```

使用一个 ∃ 假设 = 拆开它：

```lean
example (h : ∃ n : Nat, n + n = 4) : True := by
  obtain ⟨w, hw⟩ := h   -- 拿到见证 w 和性质 hw
  trivial
```

> 💡 这里藏着构造性数学的精髓：在 Lean 默认的**构造性逻辑**里，证明 `∃ x, P x` 必须真的**构造出**那个 x。不允许"我知道它存在但我说不出是谁"。（需要经典逻辑时可以显式启用 `Classical`，比如排中律 `em : p ∨ ¬p`，mathlib 大量使用。）

## 8.5 等号 `=`：最重要的命题

等式 `a = b` 是一个归纳定义的命题，只有一个构造子：`refl : a = a`。这给了我们两样武器：

1. **`rfl`**：当两边"按定义能算出相同结果"时直接得证；
2. **重写（rewrite）**：有 `h : a = b`，就能把目标里的 `a` 换成 `b`。

```lean
example (x y : Nat) (h : x = y + 1) : x + 1 = y + 2 := by
  rw [h]        -- 把 x 替换成 y + 1，目标变 y + 1 + 1 = y + 2
  -- 两边按加法定义相等
```

等式证明的常用操作：

```lean
h.symm     -- 从 a = b 得 b = a
h.trans h' -- 从 a = b 和 b = c 得 a = c
congrArg f h -- 从 a = b 得 f a = f b
```

## 8.6 两种证明风格：项模式 vs 策略模式

既然证明就是项，你可以**直接写出证明项**（像写程序一样）：

```lean
theorem and_swap_term : A ∧ B → B ∧ A :=
  fun h => ⟨h.right, h.left⟩
```

也可以**用策略一步步搭**（像下命令一样）：

```lean
theorem and_swap_tac : A ∧ B → B ∧ A := by
  intro h
  exact ⟨h.right, h.left⟩
```

两种风格编译后是同一种东西（内核只认项），但体验不同：

- **项模式**：简洁优雅，适合小证明，像函数式编程；
- **策略模式**：交互友好，Infoview 实时显示状态，适合大证明——**实战中 95% 的证明用策略模式写**。

从下一章开始我们全面转向策略模式，但请记住：**策略不是魔法，它们只是帮你把证明项一块块拼起来的工具。**

## 8.7 证明的检查：`#print axioms`

怎么知道一个定理真的被完全证明了、没有偷偷引入额外假设？Lean 提供了审计工具：

```lean
#print axioms add_zero_forall
-- 'add_zero_forall' does not depend on any axioms
```

mathlib 的定理通常依赖三个标准公理（`Classical.choice` 选择公理、`Quot.sound` 商类型、`propext` 命题外延）——这在数学界被视为常规配置。如果你的定理显示 `does not depend on any axioms`，那是纯构造性证明，含金量更高。

而如果证明里留了 `sorry`（占位符，"此处以后再证"），审计会立刻揪出来：

```lean
theorem cheater : 1 = 1 := by sorry
#print axioms cheater   -- 依赖 'sorryAx' —— 被抓现行！
```

`sorry` 是开发中的好帮手（先搭框架再填坑），但**发布前必须清零**。本书第 14 章讲验证时会看到，`sorry` 审计是工程流程的一部分。

## 8.8 本章小结

- 柯里-霍华德对应是 Lean 的灵魂：**命题 = 类型，证明 = 项**，检查证明 = 类型检查；
- `Prop` 是所有命题的宇宙；假命题也是命题，只是没有居民；
- 逻辑连词对应数据类型：∧ 是配对、∨ 是二选一、→ 是函数、∀ 是依赖函数、∃ 是"见证+证明"对；
- 构造性逻辑中，存在必须有见证；经典逻辑可用 `Classical` 显式开启；
- `sorry` 是证明中的占位洞，`#print axioms` 是审计照妖镜。

## 练习

1. 用**项模式**证明 `A ∨ B → B ∨ A`（提示：模式匹配 `Or.inl h | Or.inr h`）；
2. 证明 `theorem not_false : ¬False := ...`（提示：`¬False` 就是 `False → False`）；
3. 证明 `∃ n : Nat, n * n = 16`（给出见证和证明）；
4. 用 `#print axioms` 检查你在第 3 章写的 `zero_add`，报告它依赖哪些公理；
5. （思考题）为什么在构造性逻辑里 `¬¬A → A` 不可证？试着从"证明必须是项"的角度给出直觉解释。

## 延伸阅读

- 《Theorem Proving in Lean 4》第 3–5 章（命题与证明、量词与等式、策略）；
- 游戏 *Incredidome*…… 不，认真推荐：**自然数游戏**的 Addition World 和 Implication World，用游戏方式巩固本章概念。

---

⬅️ [第 7 章](07-monads-io.md) ｜ ➡️ 下一章：[第 9 章　策略证明入门：像搭积木一样写证明](09-tactics-basics.md)
