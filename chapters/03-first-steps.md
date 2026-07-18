# 第 3 章　三十分钟上手 Lean 4

> 本章目标：通过一连串小例子，建立对 Lean 4 的第一手感。不求甚解，先混个脸熟——把每个例子亲手敲一遍，在 VS Code 里观察结果。

## 本章你会做出什么

1. 用 `#eval` / `def` / 模式匹配写出小函数；
2. 用 `theorem ... := by rfl` 与 `induction` 各证一个小定理；
3. 试过 `simp` / `grind` / `omega` 自动化；
4. （推荐）在 `examples/LeanBookExamples/Ch03.lean` 里对照构建。

这一章像逛主题公园：把 Lean 最好玩的几个「项目」快速体验一遍。请**务必亲手敲**，并开着 Infoview——它是你的导览图。

## 3.1 Lean 是一个计算器

新建文件 `play.lean`，输入：

```lean
#eval 1 + 2 * 3        -- 7
#eval (5 : Float) / 2  -- 2.500000
#eval "Hello" ++ ", Lean!"  -- "Hello, Lean!"
#eval List.range 5     -- [0, 1, 2, 3, 4]
```

几个观察：

- `#eval` 是我们最好的朋友，它让 Lean 立刻求值并显示结果；
- `--` 是单行注释；
- Lean 区分整数（`Nat`/`Int`）和浮点数（`Float`），`(5 : Float)` 这种写法叫**类型标注**，告诉 Lean "把 5 当作浮点数"；
- 字符串拼接用 `++`（`+` 是数字专用）。

Lean 的类型推断很勤快，大多数时候你不必写类型标注。但**有歧义时**（比如字面量 `5` 可以是很多种数），就需要帮它一把。试试不写标注会怎样：

```lean
#eval 5 / 2          -- ❌ 报错：无法确定 5 是 Nat 还是 Int 还是 Float
#eval (5 : Int) / 2  -- 2  （整数除法，向 0 取整）
#eval (5 : Float) / 2  -- 2.5
```

同一个 `/`，作用在不同类型上语义完全不同——这就是 Lean 要你显式标注类型的原因：**消除歧义，让程序行为不靠猜**。

再来几个常用的：

```lean
#eval String.length "Lean"   -- 4
#eval 2 ^ 10                 -- 1024
#eval [1, 2, 3].reverse      -- [3, 2, 1]
#eval true && false          -- false
#eval 10 % 3                 -- 1
```

## 3.2 定义函数：一切的核心

```lean
def greet (name : String) : String :=
  s!"你好，{name}！欢迎来到 Lean 的世界。"

#eval greet "小明"   -- 你好，小明！欢迎来到 Lean 的世界。
```

解剖这个定义：

```
def  函数名  (参数 : 参数类型) : 返回类型 :=
  函数体
```

和 Python 的 `def greet(name): return ...` 对比，Lean 要求你写出参数类型（返回类型可推断时可省略）。`s!"..."` 是**字符串插值**，`{name}` 会被替换成变量值。

### 柯里化：所有函数都只吃一个参数

函数可以有多个参数：

```lean
def add (a b : Nat) : Nat := a + b

#eval add 3 4          -- 7
#eval add 3            -- 类型是 Nat → Nat 的函数！（部分应用）
```

注意最后一行：`add 3` 不是错误，而是返回一个"还差一个参数"的新函数。这叫**柯里化**（currying），是函数式编程的常态——Lean 里所有函数本质上都是单参数函数，`add 3 4` 实际是 `(add 3) 4`。

柯里化最直接的用途是**部分应用**：先固定一部分参数，得到一个待补全的函数：

```lean
def add3 : Nat → Nat := add 3
#eval add3 10          -- 13

-- 配合列表的高阶函数，威力更大：
#eval [1, 2, 3, 4].map (add 100)   -- [101, 102, 103, 104]
```

### 匿名函数：`fun` 与 `·`

写一次性小函数时，不必起名。两种写法：

```lean
#eval [1, 2, 3].map (fun x => x * x)   -- [1, 4, 9]
#eval [1, 2, 3].map (· * ·)            -- [1, 4, 9]
```

- `fun x => ...` 是完整写法；
- `· * ·` 是简写，每个 `·` 代表一个参数，按出现顺序对应。简洁但只适合短小的表达式，太长就别用，可读性会下降。

> 💡 **小陷阱**：`· * 10` 和 `· * ·` 不是一回事。前者接受一个参数（`x => x * 10`），后者接受两个（`x y => x * y`）。漏写一个 `·` 会得到类型不匹配的错误。

## 3.3 列表与模式匹配

```lean
def myList : List Nat := [1, 2, 3, 4, 5]

#eval myList.length            -- 5
#eval myList.map (· * 10)      -- [10, 20, 30, 40, 50]
#eval myList.filter (· > 2)    -- [3, 4, 5]
#eval myList.sum               -- 15
#eval myList.head?              -- some 1
#eval [].head?                 -- none
```

`.map`、`.filter` 这种点记法（dot notation）读作"对 `myList` 调用 `List.map`"。注意 `head?` 返回的是 `Option Nat`——可能为空列表时它给 `none`，不空时给 `some x`。Lean **不会**让你像 Python 那样 `myList[0]` 然后撞上 `IndexError`，它把"可能失败"写进了类型里。

### 模式匹配：拆开数据结构

处理列表的经典方式是**模式匹配**：

```lean
def describe : List Nat → String
  | []      => "空列表，什么都没有"
  | [x]     => s!"只有一个元素：{x}"
  | x :: xs => s!"首元素是 {x}，后面还有 {xs.length} 个"

#eval describe []         -- 空列表，什么都没有
#eval describe [42]       -- 只有一个元素：42
#eval describe [1, 2, 3]  -- 首元素是 1，后面还有 2 个
```

`[]` 是空列表，`x :: xs` 读作"x 接在 xs 前面"（`::` 是构造列表的运算符）。模式匹配从上往下尝试，第一个匹配上的分支胜出。

模式匹配必须**覆盖所有情况**，否则 Lean 会报错：

```lean
def badHead : List Nat → Nat
  | x :: _ => x
-- ❌ 报错：没有处理 [] 的情况
```

这正是 Lean "没有部分函数"哲学的体现：要么你处理空列表，要么你把返回类型改成 `Option Nat`——总之不许假装"空列表不会发生"。

修正方式之一：

```lean
def safeHead : List Nat → Option Nat
  | []     => none
  | x :: _ => some x
```

### 递归：让 Lean 替你操心"停不停"

递归函数也非常自然：

```lean
def sum : List Nat → Nat
  | []      => 0
  | x :: xs => x + sum xs

#eval sum [1, 2, 3, 4, 5]  -- 15
```

> 💡 Lean 会检查你的递归**是否终止**。`sum` 每次递归处理更短的列表，所以能通过检查。如果你写了死循环式的递归，Lean 会拒绝编译——这是定理证明器的本能：**所有函数必须有确定的结果**。

试试这个会被拒绝的例子：

```lean
def loopForever (n : Nat) : Nat := loopForever n
-- ❌ 报错：无法证明递归终止
```

不是说"运行时会卡住"——而是**编译期就直接拒绝**。要绕过这个限制，要么改写为明显终止的形式，要么用专门处理"非结构递归"的命令（如 `termination_by`，第 4 章讲）。

更优雅的写法通常是用库函数而不是手写递归：

```lean
def sum' (xs : List Nat) : Nat := xs.foldl (· + ·) 0
#eval sum' [1, 2, 3, 4, 5]  -- 15
```

`foldl`（左折叠）把列表"压"成一个值——这是函数式编程里最常用的套路之一，比手写递归更不容易出错。

### 模式匹配进阶：匹配任意类型

模式匹配不限于列表，它能拆开任何有构造子的类型。比如 `Option`：

```lean
def describeOpt : Option Nat → String
  | none    => "没有值"
  | some n  => s!"值是 {n}"

#eval describeOpt none       -- 没有值
#eval describeOpt (some 7)   -- 值是 7
```

甚至可以匹配字面量和嵌套结构：

```lean
def classify : Nat → String
  | 0     => "零"
  | 1     => "一"
  | n + 2 => s!"比较大的数：{n + 2}"   -- n + 2 匹配任何 ≥ 2 的数，n 是它减 2

#eval classify 0    -- 零
#eval classify 1    -- 一
#eval classify 42   -- 比较大的数：42
```

`n + 2` 这样的模式叫**加法模式**，Lean 会自动把匹配到的值拆成"n"和"2"。非常方便，但也容易看漏——读别人代码时留意。

## 3.4 第一次接触"证明"

下面才是 Lean 真正的魔法。看这段代码：

```lean
theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl
```

这是一个**定理**：`1 + 1 = 2`。`by` 开启了**策略模式**（tactic mode），`rfl` 是一条策略，意思是"两边按定义算一算就相等"（reflexivity，自反性）。

保存文件，没有报错——**证明通过了**。Lean 的内核已经检查过：是的，1 + 1 确实等于 2。

再看一个带变量的：

```lean
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl
```

这个定理说：对任意自然数 `n`，`n + 0 = n`。这也是"按定义"成立的，因为自然数加法就是按 `+ 0 = n` 这条规则递归定义的。

但是注意——下面这个**不能**用 `rfl`：

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  rfl    -- ❌ 报错！
```

为什么？因为加法是按第二个参数递归定义的：`n + 0` 直接由定义得 `n`，但 `0 + n` 需要对 `n` 做**归纳**才能化简。正确的证明：

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
```

这就是著名的**数学归纳法**在 Lean 里的样子：

- 基础情形（`zero`）：`0 + 0 = 0`，`rfl` 搞定；
- 归纳情形（`succ k`）：假设 `0 + k = k`（这个假设叫 `ih`，归纳假设），证明 `0 + (k+1) = k+1`。`rw` 是"重写"策略，用等式把目标变形。

把光标放在 `induction n with` 后面那行的末尾，Infoview 会显示归纳后产生的两个子目标；放在 `| succ k ih =>` 这行末尾，会看到目标变成了 `0 + k + 1 = k + 1`，而 context 里多了 `ih : 0 + k = k`。**盯 Infoview 跟着证明走**，是学策略证明最快的路子。

现在你可能还有点晕——没关系！第三部分会系统地讲。这里只需要记住一个感觉：

> **在 Lean 里，证明就是交互式地把"目标"一步步变形，直到变成显然成立的事实。**

写证明时，把光标放在 `by` 后面不同的行，VS Code 右侧的 **Infoview** 会显示当前的"证明状态"：有哪些假设、还需要证明什么。这就像游戏里的任务面板。

### 项模式：另一种写证明的风格

除了 `by ...` 的策略模式，Lean 也允许你**直接写出证明这个类型的值**，这叫项模式：

```lean
theorem one_add_one_eq_two' : 1 + 1 = 2 := rfl
```

把 `rfl` 当作一个"值"直接给定理。两种风格等价，但策略模式更常用——它把证明拆成小步，Infoview 能逐步反馈，对人类友好。项模式更像写程序，适合简单证明或当你已经胸有成竹时。

## 3.5 自动化：让 Lean 自己动脑筋

很多证明不用手写，Lean 有强大的自动化策略：

```lean
example (n : Nat) : n + 0 = n := by simp
example (a b c : Nat) : (a + b) + c = a + (b + c) := by grind
example (x y : Nat) (h : x ≤ y) : x + 1 ≤ y + 1 := by grind
```

`example` 是"不取名字的定理"，常用于随手验证。

- `simp`（化简器）：运用大量标记了 `@[simp]` 的引理自动化简目标；
- `grind`：Lean 新一代强力自动化策略，擅长处理模式匹配、线性不等式、布尔推理等（2025 年加入，正在快速变强）；
- `omega`：专治自然数/整数的线性算术；
- `ring`：专治交换环上的多项式等式（需 mathlib）；
- `decide`：对有限的可判定命题直接计算真假。

```lean
example : 104729 % 7 = 2 := by decide
example (x y : Int) (h1 : x + 2 * y = 10) (h2 : x - y = 1) : x = 4 ∧ y = 3 := by
  grind
```

第二个例子里，`grind` 接过了一个二元一次方程组，自己解出来 `x = 4, y = 3`——这正是 `omega`/`grind` 擅长的"线性算术自动求解"。

自动化是 Lean 体验的重要组成部分：**让机器干粗活，人负责巧思。** 一条经验法则：先用 `simp` / `grind` / `omega` 试一把，解不掉再上手写细致的归纳、重写。

### 自动化的边界

别误以为自动化能证一切。下面这个看似简单的命题，`simp`/`grind` 都可能束手无策：

```lean
example (n : Nat) : 2 * n + 1 ≠ n := by
  -- simp / grind 不一定能直接搞定，需要归纳
  induction n with
  | zero => decide
  | succ k ih => simp [Nat.succ_ne_zero]; omega
```

自动化擅长"局部、规则明确"的化简，但不擅长需要**数学归纳**这类"全局结构"的推理。这正是后面几章要训练你的：判断什么时候该交给自动化、什么时候该自己上手搭框架。

## 3.6 Lean 的"奇怪"之处：提前打个预防针

从其他语言转来的人常在这里摔跤，先打个招呼。每条都配一个"反例"，让你看清楚 Lean 在拦什么。

**1. 没有可变变量。**
`let x := 5` 之后，`x` 永远是 5。想"更新"就构造新值：

```lean
let x := 5
-- x := 6  -- ❌ 不存在这种语法
let y := x + 1   -- 新名字绑定新值
```

听着别扭，但这让推理容易得多（`f x` 永远等于 `f x`），也是能做证明的前提。

**2. 没有 `null`。**
可能缺失的值用 `Option α`（`some x` 或 `none`）显式表达，编译器强制你处理 `none`：

```lean
def firstChar (s : String) : Option Char :=
  if s.isEmpty then none else some s.get! 0
-- 调用方必须 match，不能假装 s 一定非空
```

**3. 没有异常满天飞。**
用 `Except ε α`、`Option` 等类型把"可能失败"写在类型里：

```lean
def parseNat (s : String) : Except String Nat :=
  match s.toInt? with
  | some i => if i ≥ 0 then ok i.toNat else error "负数不是 Nat"
  | none   => error "不是合法数字"
```

调用者从类型上就能看出"这个函数可能失败"，不用读文档猜。

**4. 函数必须有结果。**
不允许死循环，不允许"算不出来"（数学上叫**停机性**）。见 3.3 节的 `loopForever` 例子。

**5. `=` 是数学等式，不是赋值。**
`x = 5` 是一个**命题**（可真可假），赋值是 `let x := 5`；证明里用 `=` 描述相等关系：

```lean
example : 1 + 1 = 2 := by rfl   -- 这是命题
let x := 5                      -- 这是赋值
```

**6. 缩进敏感但宽容。**
Lean 用缩进表达代码块，风格上接近 Python。但嵌套模式匹配时尤其要小心对齐，否则分支归属会错。

这些"限制"看起来碍手，但每一条都对应一种"能让你相信代码/证明是对的"的能力。等你习惯之后，回看普通语言里那些隐式假设（"这里不会是 null"、"这个循环总会结束"），反而会觉得那是欠下的债。

## 3.7 一个稍大的例子：把上面的串起来

写一个判断"某数是否在列表里"的函数，并顺手证明它的一点点性质：

```lean
def contains : Nat → List Nat → Bool
  | _, []      => false
  | x, y :: ys => if x == y then true else contains x ys

#eval contains 3 [1, 2, 3, 4]   -- true
#eval contains 9 [1, 2, 3, 4]   -- false

-- 一个关于它的小性质：contains 的结果是 Bool（不会卡住）
example (x : Nat) (xs : List Nat) : contains x xs = true ∨ contains x xs = false := by
  simp [contains]
  -- bool 推理，自动结束
```

这个例子把"定义函数 → 模式匹配 → 递归 → 命题陈述 → 自动证明"一整套流程浓缩在十行里。等你读完第三部分，回头再看这段，会发现每一步都清晰可解。现在的重点是感受：**程序和证明用同一种语言写，在同一份文件里，被同一个工具检查。**

## 3.8 三十分钟路线图（时间盒）

| 分钟 | 做什么 |
|------|--------|
| 0–5 | `#eval` 算术与列表 |
| 5–12 | `def greet`、柯里化、`map` |
| 12–18 | 模式匹配 `describe`、`safeHead` |
| 18–25 | `add_zero` / `zero_add` + 盯 Infoview |
| 25–30 | 试 `simp`/`grind`，故意写错一次读报错 |

超时没关系——宁可慢，也要把 Infoview 读懂。

## 3.9 和 `examples/` 对照

```bash
cd examples && lake build
# 打开 LeanBookExamples/Ch03.lean
```

书中片段若与你本机小版本差异，以 `examples/` 能通过编译的为准，再回改书上笔记。

## 3.10 本章小结

- `#eval` 求值、`def` 定义函数、模式匹配 + 递归处理数据结构；
- 函数柯里化、匿名函数（`fun` / `·`）是函数式编程的日常；
- `theorem ... := by` 开启证明，`rfl`、`simp`、`grind`、`omega` 等策略各显神通；项模式可直接 `:= rfl`；
- **Infoview 实时显示证明状态**，是交互式证明的「仪表盘」——养成边写边看的习惯；
- Lean 是纯函数式语言：不可变、无 null、函数必须终止——这些「限制」正是它能做严格证明的原因；
- 用三十分钟路线图 + `examples/` 固化手感。

## 练习

### ⭐ 基础

1. 写 `myReverse : List Nat → List Nat`，`#eval` 测 `[1,2,3]`。
2. 写 `firstTwo : List α → Option (α × α)`。
3. 证 `n + 1 = Nat.succ n`（`rfl`）与 `a + b = b + a`（`grind`/`omega`）。
4. 故意证 `1 + 1 = 3`，读 Infoview 报错。

### ⭐⭐ 进阶

5. 手写 `length`，证其等于 `.length`（`induction`）。
6. 写 `countdown : Nat → List Nat`，解释终止性。
7. 证 `contains` 的结果必为 true 或 false（Bool 穷尽）。

### ⭐⭐⭐ 硬核

8. 项模式写出 `1+1=2` 与 `n+0=n`，思考 `rfl` 为何通用。
9. 在 `examples` 里给 Ch03 加一个你自己的 `theorem` 并 `lake build`。

## 延伸阅读

| 资源 | 内容 |
|------|------|
| FPIL 第 1–2 章 | 编程入门 |
| NNG Tutorial | 证明手感 |
| TPIL 第 1–2 章 | 证明视角 |
| 附录 E | NNG ↔ 本书章节 |

---

⬅️ [第 2 章](02-installation.md) ｜ ➡️ 下一章：[第 4 章　函数式编程的基本功](04-functional-programming.md)