# 附录 A　常用策略速查表

> 本附录是你在写证明时手边的"工具箱索引"。按用途分类，附常见用法与陷阱。遇到目标先问一句"我属于哪一类证明？"，再到对应表里找工具。

## A.1 基础策略（入门必备）

| 策略 | 用途 | 示例场景 |
|------|------|----------|
| `intro x h` | 引入 ∀/→ 的前提 | 目标 `∀ n, P n` → 上下文得 `n` |
| `exact e` | 精确给出证明项 | `exact h` |
| `apply t` | 用结论匹配目标，前提变新目标 | `apply Nat.le_trans` |
| `assumption` | 在上下文中找类型匹配目标的项 | 目标与某假设相同时 |
| `rfl` | 证定义性相等（含 `a = a`） | `1 + 1 = 2`（可计算时） |
| `trivial` | 证平凡目标（`True`、自反关系等） | — |
| `decide` | 计算判定有限/可判定命题 | `Nat.Prime 97` |
| `sorry` | 占位（开发用，发布前清除！） | — |
| `admit` | `sorry` 的别名，常用于"承认这一步" | — |
| `done` | 断言"无剩余目标"，否则报错（调试用） | 检查证明是否真的完成 |
| `by_cases h : P` | 排中律分情形（经典逻辑） | 目标在 P/¬P 两支下都可证 |

## A.2 改写与化简

| 策略 | 用途 |
|------|------|
| `rw [h]` | 用 `h : a = b` 把目标中 a 换成 b |
| `rw [← h]` | 反向重写（b 换成 a） |
| `rw [h] at h2` | 在假设 `h2` 上重写 |
| `rw [h] at *` | 在所有可重写处重写 |
| `simp` | 用 simp 引理库化简 |
| `simp only [a, b]` | 只用指定引理化简（结果稳定、可复现） |
| `simp [foo]` | 展开定义 `foo` 参与化简 |
| `simp?` | 显示 simp 实际使用的引理（便于替换为 `simp only`） |
| `simp at h` / `simp_all` | 化简假设 / 化简全部 |
| `dsimp` | 只做定义展开，不做"非显然"重写（更可预测） |
| `change t` | 把目标换成定义相等的 t |
| `show t` | 同 change，多用于阅读/聚焦 |
| `conv => ...` | 聚焦目标子表达式做转换 |
| `unfold foo` | 展开定义 `foo`（比 `simp only [foo]` 更直接） |

## A.3 结构处理（合取/析取/存在/等价）

| 策略 | 用途 |
|------|------|
| `constructor` | 拆分单构造子目标（∧/∃/↔…） |
| `obtain ⟨a, b⟩ := h` | 拆解假设（∧/∃/…） |
| `rcases h with ⟨a, b ∣ c⟩` | 花式嵌套拆解（mathlib） |
| `rintro ⟨a, b⟩` | intro + 拆包二合一 |
| `cases x with ...` | 对归纳类型分情形 |
| `induction n with ...` | 数学归纳法 |
| `match x with ...` | 策略内模式匹配 |
| `injection h` | 从构造子不相等的前提拆出参数相等 |
| `contradiction` | 上下文中存在矛盾时收尾 |
| `push_neg` | 把 ¬ 推进量词/连词内（标准化否定形） |
| `obtain rfl \| h := h` | 对 `a = b ∨ P` 类前提分流 |

## A.4 推理组织（让证明可读）

| 策略 | 用途 |
|------|------|
| `have h : P := ...` | 正向引入中间引理 |
| `have h : P := by ...` | 中间引理本身用策略证 |
| `suffices h : P by ...` | 反向规划："只需证 P" |
| `let h : T := ...` | 引入有类型的中间值 |
| `calc a = b := ... _ = c := ...` | 等式/不等式链 |
| `t1 <;> t2` | t1 后对所有子目标执行 t2 |
| `· ...` / `case ... =>` | 聚焦某个分目标 |
| `first \| t1 \| t2` | 依次尝试，首个成功者生效 |
| `try t` | 失败也算成功（容错） |
| `repeat t` | 重复直至失败 |
| `any_goals t` | 对每个目标尝试 t |
| `all_goals t` | 对全部目标都执行 t |
| `stop` / `save` | 调试断点 |
| `with_assignable_goal_msgs` | 捕获目标信息（调试） |

## A.5 自动化（核心库 + mathlib）

| 策略 | 专长 | 何时用 |
|------|------|--------|
| `omega` | Nat/Int 线性算术 | 含 `+`、`-`、`≤`、`<` 的整数/自然数线性目标 |
| `grind` | 全能新星（模式匹配、线性、E-matching） | 中等复杂度目标的一键尝试 |
| `ring` / `ring_nf` | 交换环/半环多项式等式 | 多项式恒等式（不含 ≤、不含除法） |
| `field_simp` | 域上分式化简 | 把分式整理成单分母 |
| `linarith` | 有序域线性不等式 | 纯 `≤`/`<` 线性链 |
| `nlinarith` | 非线性不等式（乘积） | 含 `x*y` 之类，但需"提示"引理时 |
| `positivity` | 证表达式 > 0 / ≥ 0 | 平方、绝对值、乘积的非负性 |
| `norm_num` | 数值计算类命题 | 具体数字的算术 |
| `gcongr` | 单调性侧条件推理 | "两边同乘非负数保持 ≤"类 |
| `polyrith` | 用线性组合拼出等式 | `ring` 失败但其实是多项式恒等式时 |
| `tauto` / `tauto!` | 命题逻辑（经典/构造） | 纯 ∧∨¬→ 逻辑 |
| `aesop` | 通用搜索式自动化 | 规则可配置的归一化/搜索 |
| `fun_prop` | 证"函数性质"（连续/可测…） | 连续/可微/可测的组合 |
| `measurability` | 可测性专门自动化 | 测度论证明 |
| `set_facets` | 集合论性质 | 子集、并交补 |
| `decide` | 离散可判定命题 | 有限枚举、可计算判定 |

## A.6 搜索助手（mathlib）

| 策略 | 用途 |
|------|------|
| `exact?` | 搜能精确关闭目标的引理 |
| `apply?` | 搜可 apply 的引理 |
| `rw?` | 搜可用的重写 |
| `hint` | 一键试一串常用策略，给出建议 |
| `simp?` | 显示 simp 实际使用的引理 |
| `library_search` | 旧名，等价于 `exact?` |

> 💡 **找定理的优先级**：先凭命名约定猜 → 用 IDE 补全验证 → 不行 `exact?`/`apply?` → 还不行上 Loogle（按类型搜）或 LeanSearch（按自然语言搜）→ 最后 Zulip 提问。

## A.7 常见证明模式（ Recipes ）

写证明时先把目标归类，再套对应套路，能少走很多弯路。

### 模式 1：证 `A ↔ B`

```lean
theorem foo : A ↔ B := by
  constructor
  · intro hA          -- 证 A → B
    ...
  · intro hB          -- 证 B → A
    ...
```

若一边比另一边简单，可改用 `rw`：`rw [foo_iff_foo]` 把目标重写到等价形式。

### 模式 2：证 `∀ n, P n`（用归纳法）

```lean
example : ∀ n : Nat, P n := by
  intro n
  induction n with
  | zero => ...        -- 基础步
  | succ k ih => ...   -- 归纳步，ih : P k
```

强归纳用 `induction n using Nat.strongInduction` 或 `Nat.strong_rec_on`。

### 模式 3：证不等式链

```lean
calc a
    ≤ b := h1
  _ ≤ c := h2
  _ ≤ d := h3
```

线性时直接 `linarith`；含乘法/平方时先 `positivity` 补非负性，再 `gcongr` 或 `nlinarith`。

### 模式 4：证 `∃ x, P x`

```lean
use 42                 -- 给出见证 x := 42
...                    -- 证 P 42
```

找见证靠直觉；证 `P 42` 往往交给 `omega`/`ring`/`simp`。

### 模式 5：处理 `¬ ∃` / `¬ ∀`

先 `push_neg` 把否定推到内部，变成更顺手的 `∀ x, ¬ P x` 或 `∃ x, ¬ P x`。

```lean
example : ¬ ∃ n : Nat, n < 0 := by
  push_neg            -- 目标变 ∀ n, ¬ n < 0
  intro n; omega
```

### 模式 6：分类讨论（排中律）

```lean
by_cases h : P
· -- P 成立分支
  ...
· -- ¬P 成立分支
  ...
```

需要经典逻辑时记得 `open Classical` 或 `Classical` 已由 mathlib 默认开启。

### 模式 7：拆解复杂前提

```lean
rcases h with ⟨a, b, c, rfl | h2⟩   -- 多重合取 + 一个析取
```

`rcases`（mathlib）比 `cases` 强大得多，支持 `⟨⟩` 嵌套与 `∣` 析取，是拆假设的首选。

### 模式 8：换一个等价的目标

证不下去时，常常是"形式不对"。先 `show ...` 或 `change ...` 把目标改写成等价但更好证的形式，再继续。

```lean
example (n : Nat) : n + 0 = n := by
  show n = n + 0       -- 反过来（定义上相等）
  rw [Nat.add_zero]
```

## A.8 常见错误与排查

| 症状 | 可能原因 | 解法 |
|------|----------|------|
| `type mismatch, term h has type ... but expected ...` | 假设类型与目标看着像但其实不同 | `#check h` 看精确类型；可能差一个 `↑` 强制转换或一个 `id` |
| `unsolved goals` 但你"明明证完了" | 留了 trivial 的隐藏目标 | 末尾加 `done` 或检查是否有未关闭的 `·` 分支 |
| `simp` 能关但你想要稳定证明 | `simp` 引理集随库变化 | 改用 `simp only [具体引理]`，先用 `simp?` 看用了哪些 |
| `omega` 报 `not a linear arithmetic goal` | 含非线性项（乘积、指数） | 拆出乘积用引理；或 `nlinarith [提示引理]` |
| `ring` 失败但等式"显然成立" | 含 `≤` 或除法 | 不等式用 `linarith`/`gcongr`；除法先 `field_simp` |
| `apply` 后留下一堆难目标 | `apply` 反推太宽 | 改用 `have` 正向构造，或用 `exact?` 让它找精确引理 |
| 证明依赖 `sorry` 没注意 | 拼写或没删占位 | `#print axioms thm` 确认无 `sorryAx` |
| 归纳后 `ih` 用不上 | 归纳对象选错，或归纳时没 `generalizing` | `induction n generalizing x` 保持通用性 |
| `decide` 超时 | 状态空间太大 | 换 `omega`/`ring` 或手动拆解 |

## A.9 常用 Unicode 输入速查

Lean 的数学符号靠"反斜杠词 + 空格/Tab"输入。下面是高频符号。

### 逻辑与集合

| 输入 | 符号 | 输入 | 符号 | 输入 | 符号 |
|------|------|------|------|------|------|
| `\to` | → | `\forall` | ∀ | `\exists` | ∃ |
| `\and` | ∧ | `\or` | ∨ | `\not` | ¬ |
| `\iff` | ↔ | `\ne` | ≠ | `\le` | ≤ |
| `\ge` | ≥ | `\in` | ∈ | `\notin` | ∉ |
| `\subset` | ⊂ | `\subseteq` | ⊆ | `\cup` | ∪ |
| `\cap` | ∩ | `\empty` | ∅ | `\S` | ∖（差集，语境） |
| `\union` | ∪ | `\inter` | ∩ | `\bigcup` | ⋃ |
| `\bigcap` | ⋂ | `\setminus` | ＼ | `\powerset` | 𝒫 |

### 数系与代数

| 输入 | 符号 | 输入 | 符号 | 输入 | 符号 |
|------|------|------|------|------|------|
| `\R` | ℝ | `\N` | ℕ | `\Z` | ℤ |
| `\Q` | ℚ | `\C` | ℂ | `\nat` | ℕ |
| `\a` | α | `\b` | β | `\g` | γ |
| `\dvd` | ∣ | `\mid` | ∣ | `\equiv` | ≡ |
| `\circ` | ∘ | `\comp` | ∘ | `\cdot` | ⋅ |
| `\^-1` | ⁻¹ | `\sqr` | √ | `\sqrt` | √ |

### 证明专用

| 输入 | 符号 | 输入 | 符号 |
|------|------|------|------|
| `\<` | ⟨ | `\>` | ⟩ |
| `\|-` | ⊢ | `\t` | τ |
| `\l` | λ | `\lam` | λ |
| `\.` | ·（聚焦/匿名） | `\big` | 大算子前缀 |

### 微积分与分析

| 输入 | 符号 | 输入 | 符号 | 输入 | 符号 |
|------|------|------|------|------|------|
| `\sum` | ∑ | `\prod` | ∏ | `\int` | ∫ |
| `\infty` | ∞ | `\partial` | ∂ | `\nabla` | ∇ |
| `\le` | ≤ | `\ge` | ≥ | `\to` | → |
| `\sup` | sup | `\inf` | inf | `\lim` | lim |

### 上下标与编号

| 输入 | 符号 | 输入 | 符号 |
|------|------|------|------|
| `\0` `\1` `\2` … | ₀ ₁ ₂ … | `\^0` `\^1` … | ⁰ ¹ … |
| `\_0` `\_1` | ₀ ₁ | `\comp` | ∘ |

> 💡 找不到某个符号？在 VS Code 里直接打 `\` 后开始输入关键词会弹出候选；或查阅 [Lean Unicode 输入表](https://lean-lang.org/unicode/)。

---

⬅️ [第 22 章](22-community-project.md) ｜ ➡️ [附录 B　常用资源与工具清单](appendix-b-resources.md)