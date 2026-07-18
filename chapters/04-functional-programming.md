# 第 4 章　函数式编程的基本功

> 本章目标：掌握函数式编程的核心思维——函数是一等公民、数据不可变、用组合代替循环。学完后你能独立写出一个可扩展的表达式求值器，并用 `map` / `filter` / `fold` 处理真实数据。

如果你来自 Python / Java / C++ 的世界，这一章会改变你写程序的方式。函数式编程（FP）不是炫技，而是一套**让程序更容易推理**的纪律。而「容易推理」正是 Lean 能做定理证明的根本原因：没有隐藏副作用，等式才能成立；没有任意修改，归纳才能顺利。

## 本章你会做出什么

读完并动手后，你手里会有：

1. 一组小工具函数：`applyTwice`、`makeAdder`、自己的 `compose`；
2. 一条数据处理管道：从原始列表筛出偶数 → 平方 → 求和；
3. 一个完整的 **算术表达式求值器**（数字、加减乘、括号语义），后面第 5、14 章还会在它上面加错误处理和验证。

建议：边读边在 VS Code 或 [live.lean-lang.org](https://live.lean-lang.org/) 里敲代码。FP 是手感课，只看不写等于没学。

---

## 4.1 函数是一等公民

在 Lean 里，函数和数字、字符串一样，是普通的值。你可以：

**把函数赋给变量：**

```lean
def double : Nat → Nat := fun n => 2 * n
#eval double 5   -- 10
```

`fun n => 2 * n` 是匿名函数（lambda），读作「接收 `n`，返回 `2 * n`」。也可以写成：

```lean
def double' (n : Nat) : Nat := 2 * n
-- 与上面的 double 等价；只是把参数写到了定义头上
```

**把函数当参数传：**

```lean
def applyTwice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

#eval applyTwice double 3      -- 12（翻倍两次：3 → 6 → 12）
#eval applyTwice (· + 1) 3     -- 5（加一两次）
```

`(· + 1)` 是**点记号**（dot notation / placeholder）：空位 `·` 表示「这里是参数」。`(· + 1)` 等价于 `fun x => x + 1`，`(2 * ·)` 等价于 `fun x => 2 * x`。多占位也可以：`(· + ·)` 是二元加法函数。

**把函数当返回值：**

```lean
def makeAdder (k : Nat) : Nat → Nat := fun n => n + k

def add5 := makeAdder 5
#eval add5 10   -- 15
```

`makeAdder 5` 生成了一个「加 5 专用函数」。这种「函数工厂」是 FP 的常用套路，术语叫**闭包**（closure）——返回的函数记住了 `k` 的值。

### 类型注解：`Nat → Nat` 怎么读

`f : Nat → Nat` 读作「`f` 是从自然数到自然数的函数」。`→` 是**右结合**的：

```
Nat → Nat → Nat   等价于   Nat → (Nat → Nat)
```

所以 `add : Nat → Nat → Nat` 实际是「接收一个 `Nat`，返回一个 `Nat → Nat` 函数」——这就是**柯里化**（currying）的类型表达。

调用时两种写法等价：

```lean
def add (a b : Nat) : Nat := a + b

#eval add 2 3        -- 5，多参数语法糖
#eval (add 2) 3      -- 5，显式柯里化：先固定 a=2，再喂 b
#eval List.map (add 10) [1, 2, 3]  -- [11, 12, 13]，偏应用超好用
```

> 💡 **和 Python 的对比**
>
> Python 里 `lambda n: 2 * n`、高阶函数 `map`/`filter` 都有，但柯里化和类型检查不强制。Lean 把「函数是值」贯彻到底：**每个多参数函数天生可偏应用**，类型系统会拦住「把字符串当数字传」这类错。

### 命名参数 vs 位置参数

```lean
def greet (name : String) (times : Nat := 1) : String :=
  String.join (List.replicate times s!"你好，{name}！")

#eval greet "小明"        -- 用默认 times = 1
#eval greet "小明" 3      -- 重复三次
#eval greet (times := 2) (name := "Ada")  -- 命名实参，顺序可换
```

日常写库时，给「有合理默认值」的参数设默认，调用会清爽很多。

---

## 4.2 不可变性：一旦出生，永不改变

```lean
def xs := [1, 2, 3]
def ys := xs ++ [4]   -- 拼接出新列表

#eval xs   -- [1, 2, 3]，原列表纹丝不动
#eval ys   -- [1, 2, 3, 4]
```

Lean 里没有 `xs.push(4)` 这种「原地修改」。所有操作都返回**新值**。

> 🤔 **这样不是很浪费内存吗？**
>
> 不用担心。Lean 的运行时使用**持久化数据结构**（persistent data structures）：新列表和旧列表**共享**没变的部分。而且 Lean 4 有独特的**就地更新**优化（*functional but in-place*）：当编译器能证明旧值此后不再被使用时，会直接复用其内存——纯函数式的外表，接近 C 的性能。这是 Lean 4 论文的招牌技术之一。

不可变性带来的好处是实打实的：

| 好处 | 含义 |
|------|------|
| 没有意外副作用 | 函数拿到什么就是什么，不会被别的代码偷偷改掉 |
| 并发天然安全 | 不可变数据随便多线程共享，不需要锁 |
| 可以「等式推理」 | `f x = f x` 永远成立——数学证明的基石 |

对比命令式思维：

```lean
-- 命令式脑子里想的（伪代码）：
-- xs = [1,2,3]; xs.push(4);  // xs 被改了

-- Lean 的写法：始终产生新绑定
def xs' := [1, 2, 3]
def ys' := xs'.concat 4   -- 或 xs' ++ [4]
```

> ⚠️ **注意**：Lean 里也有 `IO`、可变引用（`IO.Ref`）等「真正可变」的设施，那是第 7 章的事。在纯函数世界里，**默认一切不可变**。

---

## 4.3 三板斧：map、filter、fold

命令式语言用循环做的事，FP 用三个高阶函数解决大约 80%：

```lean
def nums := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

-- map：每个元素变一变
#eval nums.map (· * 2)          -- [2, 4, 6, ..., 20]

-- filter：留下满足条件的
#eval nums.filter (· % 2 == 0)  -- [2, 4, 6, 8, 10]

-- fold：把所有元素「折叠」成一个值
#eval nums.foldl (· + ·) 0      -- 55（累加）
```

### 逐个拆开

**`map`**：长度不变，元素类型可变。

```lean
#eval [1, 2, 3].map toString           -- ["1", "2", "3"] : List String
#eval ["a", "bb"].map (·.length)       -- [1, 2]
```

**`filter`**：长度可变，元素类型不变。

```lean
#eval ["hi", "hello", "ok"].filter (fun s => s.length ≥ 3)
-- ["hello"]
```

**`foldl` / `foldr`**：类型最值得细看：

```lean
List.foldl : (β → α → β) → β → List α → β
List.foldr : (α → β → β) → β → List α → β
```

读法：给一个「把累计值和新元素合成新累计值」的函数、一个初始累计值、一个列表，返回最终累计值。

```lean
-- foldl：从左往右  (((0+1)+2)+3) = 6
#eval [1, 2, 3].foldl (· + ·) 0

-- foldr：从右往左  (1+(2+(3+0))) = 6
#eval [1, 2, 3].foldr (· + ·) 0

-- 对非结合运算，左右折叠结果不同！
#eval [1, 2, 3].foldl (· - ·) 0   -- ((0-1)-2)-3 = -6
#eval [1, 2, 3].foldr (· - ·) 0   -- 1-(2-(3-0)) = 2
```

经验法则：

- **求和、求积、聚合统计** → 通常 `foldl`；
- **构造新列表、依赖「右边先算完」** → 常 `foldr`（例如用 fold 实现 `map`）；
- 吃不准时，先写递归版，再考虑折叠。

### 管道串联

```lean
-- 1~10 中偶数的平方和
#eval nums
  |>.filter (· % 2 == 0)
  |>.map (· ^ 2)
  |>.foldl (· + ·) 0
-- 4 + 16 + 36 + 64 + 100 = 220
```

`|>` 是管道符：`x |> f` 就是 `f x`，让代码从左向右流动。多行管道时建议每步一个 `|>.`，阅读体验接近 SQL 或 Unix 管道。

还有 `<|`（反管道，有时用于减少括号）和 `$`（部分代码风格里等同于低优先级函数应用）：

```lean
#eval List.length <| [1, 2, 3].map (· + 1)   -- 3
```

### 自己实现一遍（理解用）

```lean
def myMap (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: myMap f xs

def myFilter (p : α → Bool) : List α → List α
  | []      => []
  | x :: xs => if p x then x :: myFilter p xs else myFilter p xs

def myFoldl (f : β → α → β) (init : β) : List α → β
  | []      => init
  | x :: xs => myFoldl f (f init x) xs
```

写过这三份，你就再也忘不了它们在干什么。标准库实现经过优化，日常请继续用 `List.map` 等。

---

## 4.4 组合：把小程序拼成大程序

函数式编程的精髓是**组合**（composition）：每个函数只做一件事，然后像乐高一样拼起来。

```lean
def isEven (n : Nat) : Bool := n % 2 == 0
def square (n : Nat) : Nat := n * n

-- 函数组合：先 square 再 isEven
def isEvenSquare := isEven ∘ square

#eval isEvenSquare 4   -- true（16 是偶数）
#eval isEvenSquare 3   -- false（9 是奇数）
```

`∘`（输入 `\circ`）是数学里的复合符号：`(f ∘ g) x = f (g x)`。注意顺序：**先写外层，再写内层**——和管道 `|>` 的「从左到右」阅读习惯相反，初次容易混。

| 写法 | 求值顺序 | 读法 |
|------|----------|------|
| `(f ∘ g) x` | 先 `g` 后 `f` | 数学复合 |
| `x \|> g \|> f` | 先 `g` 后 `f` | 管道，常更易读 |
| `f (g x)` | 先 `g` 后 `f` | 直接嵌套 |

一个更实际的例子——统计文本中长度超过 3 的单词数：

```lean
def countLongWords (text : String) : Nat :=
  text.splitOn " "
    |>.filter (fun w => w.length > 3)
    |>.length

#eval countLongWords "the quick brown fox jumps over the lazy dog"
-- 5：quick, brown, jumps, over, lazy（the/fox/the/dog 被滤掉）
```

> 💡 小陷阱：`splitOn " "` 不会合并连续空格，也不会去掉标点。真实文本处理要用更细的分词；这里只演示管道思维。

### 局部定义：`let` 与 `where`

复杂函数里用局部绑定保持清晰：

```lean
def average (xs : List Nat) : Option Nat :=
  let n := xs.length
  if n == 0 then none
  else some (xs.foldl (· + ·) 0 / n)

def report (xs : List Nat) : String :=
  match average xs with
  | none   => "空列表，无法求平均"
  | some a => s!"平均约为 {a}"
where
  -- where 子句也可以挂在定义后（本例逻辑已在 average 里）
  -- 这里仅作语法示意
  dummy := ()
```

`let` 引入局部名；多个步骤时比硬嵌套可读得多。

---

## 4.5 递归：函数式编程的「循环」

没有传统 for/while 作为首选（Lean 在 `IO` 里也有循环，见第 7 章；纯计算首选递归），重复靠递归表达：

```lean
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5   -- 120
```

模式 `n + 1` 匹配所有 ≥ 1 的自然数，并自动把「前驱」绑定为 `n`——这是 Lean 对皮亚诺自然数的友好语法。

### 终止性检查

Lean 会**检查递归终止**：每次递归调用的参数必须「变小」。对列表，从 `x :: xs` 递归到 `xs`；对自然数，从 `n + 1` 到 `n`——编译器才放行。

有些递归「变小」不那么显然：

```lean
def gcd (a b : Nat) : Nat :=
  if b = 0 then a else gcd b (a % b)
termination_by b
```

`termination_by b` 告诉 Lean：「请盯着 `b`，它每次都在变小」（因为 `a % b < b`，当 `b ≠ 0`）。必要时还可以写 `decreasing_by` 给出证明。

这套**终止性论证**保证了 Lean 里（通过检查的）每个函数都会停机——对数学证明至关重要：一个允许死循环的逻辑系统可以「证明」任何东西，那就毫无价值了。

### 尾递归（了解即可）

```lean
def factorialTR (n : Nat) : Nat :=
  let rec go (k acc : Nat) : Nat :=
    match k with
    | 0     => acc
    | k + 1 => go k ((k + 1) * acc)
  go n 1
```

`go` 的递归调用是函数的最后一步（尾调用），Lean 常能优化成循环，避免栈溢出。对初学：先写清楚的普通递归，性能热点再改尾递归。

### 互相递归

两个函数互相调用时用 `mutual`：

```lean
mutual
  def isEven' : Nat → Bool
    | 0     => true
    | n + 1 => isOdd' n

  def isOdd' : Nat → Bool
    | 0     => false
    | n + 1 => isEven' n
end

#eval isEven' 4   -- true
#eval isOdd' 4    -- false
```

---

## 4.6 模式匹配与分支

递归几乎总是和**模式匹配**一起出现。除了定义上的多方程写法，还有 `match`：

```lean
def describeNumber (n : Nat) : String :=
  match n with
  | 0     => "零"
  | 1     => "一"
  | n + 1 => s!"某个比 0 大的数（前驱是 {n}）"
```

列表上的经典：

```lean
def List.myHead? (xs : List α) : Option α :=
  match xs with
  | []     => none
  | x :: _ => some x

def List.myTail (xs : List α) : List α :=
  match xs with
  | []      => []
  | _ :: xs => xs
```

`if ... then ... else ...` 适合布尔条件；**数据结构有几种形状，就用 match**——编译器会检查是否漏情况。

```lean
-- 布尔其实也是归纳类型，这两种风格都常见
def absDiff (a b : Nat) : Nat :=
  if a ≥ b then a - b else b - a
```

> 📖 第 5 章会看到：`Option`、`Except`、自定义 `inductive` 全靠模式匹配处理。现在先把「匹配列表空/非空」「匹配自然数 0/后继」练熟。

---

## 4.7 惰性求值与严格求值

Lean 默认是**严格求值**（像 OCaml / Rust / C）：参数先算好再进函数。需要惰性（比如延迟昂贵计算、处理潜在很大的结构）时，用 `Thunk` 把计算包起来：

```lean
def expensive : Thunk Nat := Thunk.mk fun _ =>
  (List.range 1000000).foldl (· + ·) 0

-- 此时还没真的算
#eval expensive.get   -- 现在才算：499999500000
```

日常代码用得不多，知道有这回事即可。Lean 的证明世界里还有更细的「归约」策略（`rfl`、`simp` 等），那是第三部分的事。

---

## 4.8 踩坑对照（本章高频）

| 症状 / 写法 | 原因 | 正确姿势 |
|-------------|------|----------|
| `nums.map · * 2` 解析错乱 | 点记号优先级 | 写成 `nums.map (· * 2)`，括号包住 |
| 想写 `xs[0]` 取首元素 | 列表没有随意下标语法当总安全 | 用 `xs.head?`（返回 `Option`）或 `xs[0]!`（可 panic，慎用） |
| `List.get` 需要证明下标合法 | 依赖类型在保护你 | 初学用 `get?` / `head?`；第 5 章再碰 `Fin` |
| 递归报 `failed to prove termination` | 参数没有明显变小 | `termination_by` 标度量，或改写递归结构 |
| `foldl` / `foldr` 结果不同 | 运算不满足结合律 | 想清楚折叠方向；加法没事，减法和 `::` 要小心 |
| `(f ∘ g)` 和管道顺序搞反 | 复合先写外层 | 不熟就用 `x \|> g \|> f` |
| `#eval` 很慢或栈溢出 | 非尾递归 + 大数据 | 换 `foldl`、减小输入，或尾递归 |

---

## 4.9 和标准库对照

本章手写的东西，标准库几乎都有现成版——**学习时自己写，项目里用库**：

| 我们练的 | 标准库 |
|----------|--------|
| `myMap` / `myFilter` / `myFoldl` | `List.map` / `filter` / `foldl` |
| `myLength`（练习） | `List.length` |
| `isEven ∘ square` | `Function.comp` 或 `∘` |
| 管道 | `\|\>`、`\|\>.` |
| 字符串插值 | `s!"..."`（已用） |
| 可选值 | `Option`（第 5 章深入） |

在 VS Code 里对标识符按 **F12 / 右键 Go to Definition**，可以直接跳进标准库源码——这是学地道写法的最好方法。

---

## 4.10 迷你项目：可扩展的算术表达式求值器

把本章知识串起来。目标：用一小套构造规则描述表达式语法，用递归赋予语义。

```lean
/-- 算术表达式的抽象语法树（AST） -/
inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
deriving Repr, BEq

/-- 递归求值：语法 → 整数语义 -/
def Expr.eval : Expr → Int
  | .num n   => n
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .neg a   => - a.eval

-- 帮助构造：用运算符风格拼树（可选）
namespace Expr
  def ofNat (n : Nat) : Expr := .num ↑n
end Expr

-- (1 + 2) * 3
def exampleExpr : Expr :=
  .mul (.add (.num 1) (.num 2)) (.num 3)

#eval exampleExpr.eval   -- 9

-- -(10 - 3) * 2
def exampleExpr₂ : Expr :=
  .mul (.neg (.sub (.num 10) (.num 3))) (.num 2)

#eval exampleExpr₂.eval  -- -14
```

再加一层：**把表达式漂亮打印**（也是递归 + 模式匹配）：

```lean
def Expr.pretty : Expr → String
  | .num n   => toString n
  | .add a b => s!"({a.pretty} + {b.pretty})"
  | .sub a b => s!"({a.pretty} - {b.pretty})"
  | .mul a b => s!"({a.pretty} * {b.pretty})"
  | .neg a   => s!"(-{a.pretty})"

#eval exampleExpr.pretty   -- "((1 + 2) * 3)"
```

以及一个**用 fold 做的统计**：数一数树里有多少个 `num` 叶子：

```lean
def Expr.numCount : Expr → Nat
  | .num _   => 1
  | .add a b => a.numCount + b.numCount
  | .sub a b => a.numCount + b.numCount
  | .mul a b => a.numCount + b.numCount
  | .neg a   => a.numCount

#eval exampleExpr.numCount   -- 3
```

`inductive` 下一章会系统讲。这里先建立直觉：**用构造规则描述数据形状，用模式匹配递归地赋予含义**——这是编程语言理论的看家本领，也是 Lean 编译器自身的写法。

> 📖 **下一步可以怎么扩展**（选做，贯穿后面章节）
>
> - 加 `div`，除零时返回 `Option Int` 或 `Except String Int`（第 5 章）；
> - 证明 `eval (add a b) = eval a + eval b` 这类显然等式（第 8–9 章）；
> - 用宏做 `expr!|(1+2)*3|` 语法糖（第 17 章）。

---

## 4.11 本章小结

- **函数是值**：可传递、返回、组合；`fun x => ...` 与点记号 `(· + 1)` 创建匿名函数；多参数函数默认柯里化。
- **数据不可变**：所有「修改」都是创建新值；运行时靠结构共享 + 就地更新保证性能。
- **`map` / `filter` / `fold` + 管道 `|>`** 是日常数据处理的主力；会自己实现一遍再安心用库。
- **递归代替循环**，且必须通过**终止性检查**；必要时 `termination_by`。
- **模式匹配**是处理结构化数据的默认方式；组合小函数拼出大程序。
- **迷你项目**：`Expr` 求值器展示了「语法 + 语义」的经典 FP 结构。

---

## 练习

### ⭐ 基础

1. 用 `foldl` 实现 `myLength : List α → Nat`（不许用 `.length`）。
2. 实现 `compose2 : (β → γ) → (α → β) → α → γ`，即自己写一遍 `∘`，并 `#eval` 验证 `(compose2 isEven square) 4 = true`。
3. 用 `map` 把 `List Nat` 转成 `List String`（每位数字 `toString`）。

### ⭐⭐ 进阶

4. 写 `primesUpTo (n : Nat) : List Nat`：筛法思路——从 `List.range n` 里从 2 起保留素数（提示：`List.filter` + 辅助 `Nat` 整除判断；可先写 `isPrime`）。
5. 用 `foldl` 实现 `reverse : List α → List α`（不许用标准库 `reverse`）。
6. 扩展 4.10 的求值器：增加 `div : Expr → Expr → Expr`，把 `eval` 改成 `Expr → Option Int`，除数为 0 时返回 `none`。

### ⭐⭐⭐ 硬核

7. 实现 `groupBy (eq : α → α → Bool) : List α → List (List α)`，把相邻且 `eq` 为真的元素归为一组（类似 run-length 前一步）。
8. 为 `Expr` 写 `simplify : Expr → Expr`：至少完成 `x + 0 → x`、`x * 1 → x`、`x * 0 → 0`、`--x → x` 的局部化简，并保证 `e.simplify.eval = e.eval`（可用 `#eval` 多测几例；正式证明留到第 8–9 章）。

---

## 延伸阅读

| 资源 | 读什么 | 和本章关系 |
|------|--------|------------|
| [*Functional Programming in Lean*](https://lean-lang.org/functional_programming_in_lean/) 第 1–2 章 | 求值、定义、类型、函数抽象 | 官方程序员主教材，细节比本章更深 |
| 同上，第 3 章（Polymorphism / containers） | 多态与列表库 | 接第 5 章泛型与容器 |
| Lean 4 论文 *The Lean 4 Theorem Prover and Programming Language*（CADE-28） | "functional but in-place" | 理解性能故事的第一手材料 |
| 标准库 `Init.Data.List.Basic` | 源码 | 对照 `map`/`foldl` 地道实现 |

卡住时：先把 4.10 求值器跑通，再回头补练习。下一章我们把「类型」从 `Nat`、`List` 升级到你自己定义的世界。

---

⬅️ [第 3 章](03-first-steps.md) ｜ ➡️ 下一章：[第 5 章　类型、结构体与归纳类型](05-types-inductive.md)
