# 第 5 章　类型、结构体与归纳类型

> 本章目标：学会用类型精确地描述数据——这是 Lean 一切能力（编程 + 证明）的地基。

如果说函数是 Lean 的动词，类型就是名词。Lean 的类型系统极其强大：它不仅能描述"这是个整数"，还能描述"这是个**不超过 100** 的整数"、"这是个**已排序**的列表"，甚至"这是哥德巴赫猜想的一个证明"。本章先把地基打牢：结构体、归纳类型、依赖类型的初体验。

## 5.1 结构体：有名字的打包

把几个值打包成一个记录，用 `structure`：

```lean
structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0, y := 0 }

#eval origin.x          -- 0.000000
#eval { origin with y := 3.0 }   -- 基于 origin 创建新 Point，只改 y
```

要点：

- `{ x := 0, y := 0 }` 是**匿名构造器**记法；
- `origin.x` 访问字段；
- `{ p with y := 3.0 }` 是**函数式更新**：得到一个新 `Point`（旧的不变，记住第 4 章的纪律）；
- `deriving Repr` 让 Lean 自动生成"可打印表示"，这样 `#eval` 才能显示它。类似的还有 `deriving BEq`（相等判断）、`deriving DecidableEq`（可判定的相等）、`deriving Inhabited`（提供默认值）等。

结构体可以带**参数**（泛型）：

```lean
structure Pair (α : Type) where
  first : α
  second : α

def p1 : Pair Nat := { first := 1, second := 2 }
def p2 : Pair String := { first := "左", second := "右" }
```

还可以**继承/扩展**另一个结构体：

```lean
structure Point3D extends Point where
  z : Float

def p : Point3D := { x := 1, y := 2, z := 3 }
#eval p.x    -- 继承来的字段直接用
```

## 5.2 归纳类型：一砖一瓦造世界

`inductive` 是 Lean 中**定义新类型的终极武器**。思想朴素得惊人：

> 一个归纳类型 = 列出构造它的所有方式（构造子）。

### 最简单的例子：枚举

```lean
inductive Weekday where
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday
deriving Repr

def isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _                   => false
```

七个构造子，就这么多。模式匹配保证不重不漏（漏了 Lean 会警告）。

### 带数据的构造子

构造子可以携带数据，这让归纳类型能表达"**或**"（这个，或者那个）：

```lean
inductive Shape where
  | circle (radius : Float) : Shape
  | rect (width height : Float) : Shape
deriving Repr

def area : Shape → Float
  | .circle r   => Float.pi * r * r
  | .rect w h   => w * h

#eval area (.circle 1.0)   -- 3.141593
```

一个 `Shape` **要么**是圆（带半径），**要么**是矩形（带宽高）。这就是函数式语言里所谓的**和类型**（sum type）/ 标签联合（tagged union）。对比 Java 需要一堆类和 instanceof，Lean 里四行搞定，而且模式匹配是**穷尽性检查**的——以后给 `Shape` 加了三角形，所有忘记处理的 `area` 式函数都会被编译器点名。

### 递归的构造子：列表和树

构造子还可以引用类型自身，造出**任意大**的结构：

```lean
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
deriving Repr

-- cons 1 (cons 2 (cons 3 nil)) 就是列表 [1,2,3]
```

标准库里的 `List α` 就是这么定义的（`[]` 和 `::` 是它的语法糖）。二叉树同理：

```lean
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α
deriving Repr

def Tree.size : Tree α → Nat
  | .leaf         => 0
  | .node _ l r   => 1 + l.size + r.size
```

### 自然数：一切归纳类型的祖师爷

最深刻的例子藏在最平常的地方——Lean 里的自然数 `Nat` 本身就是归纳类型：

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

`zero` 是 0，`succ zero` 是 1，`succ (succ zero)` 是 2……皮亚诺公理！你平时写的 `5` 只是语法糖。

为什么这重要？因为**数学归纳法不是外加的技巧，而是由这个定义自动生成的**：要证明性质对所有 `Nat` 成立，只需证 `zero` 情形和"若对 `n` 成立则对 `succ n` 成立"。每个归纳类型都会自动生成这样的**归纳原理**（recursor），这就是 `induction` 策略的来源（第 9、10 章详述）。

## 5.3 Option 和 Except：把"可能失败"写进类型

```lean
inductive Option (α : Type) where
  | none : Option α
  | some : α → Option α
```

`Option α` = 要么有值 `some x`，要么 `none`。它是 Lean 对付"空指针"的武器——**函数可能没结果这件事，从类型上就看得一清二楚，编译器逼着你处理**：

```lean
def List.head? : List α → Option α
  | []      => none
  | x :: _  => some x

-- 用模式匹配安全地取首元素
def describeHead (xs : List Nat) : String :=
  match xs.head? with
  | none   => "空的！"
  | some x => s!"首元素是 {x}"
```

需要携带错误信息时用 `Except`：

```lean
def parsePositive (s : String) : Except String Nat :=
  match s.toNat? with
  | none   => .error s!"'{s}' 不是数字"
  | some 0 => .error "必须是正数"
  | some n => .ok n
```

## 5.4 依赖类型：Lean 的超能力（初体验）

到目前为止的类型（`Nat`、`List α`、`Shape`）在其他函数式语言里也有。Lean 真正的杀手锏是**依赖类型**（dependent types）：**类型可以依赖于值**。

看招牌例子——定长向量：

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```

注意 `Vec α n` 的 `n` 是**类型的一部分**：`Vec Nat 3` 和 `Vec Nat 4` 是不同的类型！于是：

```lean
def v1 : Vec Nat 2 := .cons 10 (.cons 20 .nil)

-- 安全的索引访问：下标不可能越界，因为越界的下标类型就不对
def Vec.get : Vec α n → Fin n → α
  | .cons x _,  ⟨0, _⟩     => x
  | .cons _ xs, ⟨i+1, h⟩   => xs.get ⟨i, Nat.lt_of_succ_lt_succ h⟩
```

`Fin n` 是"小于 n 的自然数"类型——下标想越界，连类型检查这关都过不了。**bug 在编译期被类型系统物理性消灭**，而不是靠运行时报错或单元测试。

依赖类型还能表达函数规格：

```lean
-- "输入一个列表，返回一个和输入等长的列表"——长度关系写进类型！
def Vec.map (f : α → β) : Vec α n → Vec β n
  | .nil       => .nil
  | .cons x xs => .cons (f x) (Vec.map f xs)
```

普通语言的类型系统只能管"形状对不对"，Lean 的类型系统能管"**性质对不对**"。到第 8 章我们会看到，把这条路线推到底，"类型"就变成了"命题"，"类型检查"就变成了"证明检查"。

## 5.5 子类型：给类型加约束

另一种常用的精化手段是**子类型**（subtype）——"满足某个性质的那些值"：

```lean
def EvenNat := { n : Nat // n % 2 = 0 }

def four : EvenNat := ⟨4, by decide⟩
--                            ^^^ 必须现场提供"4 确实是偶数"的证明！
```

`{ n : Nat // P n }` 读作"满足性质 P 的 Nat 所成的类型"。构造一个值必须**连证明一起给**。这就是"类型即规格"的又一形态，mathlib 里到处都是（比如 `Fin n` 就是 `{ i : Nat // i < n }` 的包装）。

## 5.6 类型宇宙：Type、Type 1、Sort……

最后一个容易晕的概念，用比喻讲清楚。

问：`Nat : ?` 的类型是什么？答：`Nat : Type`（Nat 是一个类型）。
再问：`Type : ?` 的类型是什么？

如果答 `Type : Type`，逻辑上会推出悖论（类似"说谎者悖论"）。Lean 的解法是**宇宙层级**（universes）：

```
Type   : Type 1
Type 1 : Type 2
Type 2 : Type 3
...
```

一层压一层，无穷递增，绝不自指。另外：

- `Prop`（命题的宇宙）住在最底层：`Prop : Type`；
- `Type` 其实是 `Type 0` 的别名；
- 写泛型代码时可以写 `Type u`，让 Lean 自动适配任意层级（**宇宙多态**）。

日常编程 99% 的时间你不用操心宇宙——Lean 会自动推断。只有写高度抽象的库代码时才会和它打交道。

## 5.7 本章小结

- `structure` 打包数据，`inductive` 列出所有构造方式——两者覆盖绝大多数建模需求；
- 归纳类型可以是递归的（列表、树、自然数），并自动附带**归纳原理**；
- `Option` / `Except` 把"可能失败"显式化，编译器强制处理；
- **依赖类型让类型可以依赖值**——`Vec α n`、`Fin n`、子类型 `{x // P x}`，把程序性质前移到编译期；
- 类型按宇宙分层：`Prop : Type : Type 1 : Type 2 : ...`，避免自指悖论。

## 练习

1. 定义归纳类型 `Color`（红绿蓝三色），写一个 `mix : Color → Color → Color` 描述颜料混合，并用 `deriving Repr` 打印结果；
2. 定义"可能含错误的表达式求值"：`evalSafe : Expr → Option Nat`，处理除法中除数为零的情形（需先给 `Expr` 加 `div` 构造子）；
3. 定义 `SortedList`：用子类型 `{ xs : List Nat // 已排序性质 }` 表达"已排序列表"（提示：可以定义辅助命题 `List.Pairwise (· ≤ ·)` 或直接递归定义"相邻递增"）；
4. 用 `Vec` 写一个 `append : Vec α m → Vec α n → Vec α (m + n)`——体验一把"类型帮你写程序"（让 Lean 的报错引导你补全代码）。

## 延伸阅读

- 《Theorem Proving in Lean 4》第 7 章（Inductive Types）；
- 《Functional Programming in Lean》第 4 章。

---

⬅️ [第 4 章](04-functional-programming.md) ｜ ➡️ 下一章：[第 6 章　类型类：Lean 的"接口"](06-typeclasses.md)
