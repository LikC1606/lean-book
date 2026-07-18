# 第 5 章　类型、结构体与归纳类型

> 本章目标：学会用类型精确地描述数据——这是 Lean 一切能力（编程 + 证明）的地基。学完后你能自定义结构体与归纳类型，安全处理失败，并写出长度写在类型里的 `Vec`。

如果说函数是 Lean 的动词，类型就是名词。Lean 的类型系统极其强大：它不仅能描述「这是个整数」，还能描述「这是个**不超过 100** 的整数」、「这是个**已排序**的列表」，甚至「这是哥德巴赫猜想的一个证明」。本章先把地基打牢：结构体、归纳类型、依赖类型的初体验。

## 本章你会做出什么

1. 用 `structure` 建模二维/三维点，并做函数式更新；
2. 用 `inductive` 定义形状、列表、二叉树，并写穷尽的模式匹配；
3. 用 `Option` / `Except` 处理「可能失败」，消灭空指针式崩溃；
4. 亲手定义定长向量 `Vec`，体会「类型依赖值」。

---

## 5.1 结构体：有名字的打包

把几个值打包成一个记录，用 `structure`：

```lean
structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0, y := 0 }

#eval origin.x                    -- 0.000000
#eval { origin with y := 3.0 }    -- 基于 origin 创建新 Point，只改 y
```

要点：

| 语法 | 含义 |
|------|------|
| `{ x := 0, y := 0 }` | 匿名构造器 |
| `origin.x` | 字段投影 |
| `{ p with y := 3.0 }` | **函数式更新**：得到新 `Point`，旧的不变 |
| `deriving Repr` | 自动生成可打印表示，`#eval` 才能显示 |

也可以用位置构造子（结构体名即构造子）：

```lean
def p' : Point := Point.mk 1.0 2.0
-- 或（Lean 4 常直接）
def p'' : Point := ⟨1.0, 2.0⟩
```

`deriving` 家族常用：

| 派生 | 作用 |
|------|------|
| `Repr` | `#eval` 打印 |
| `BEq` | `==` 布尔相等 |
| `DecidableEq` | 可判定的命题相等 `=`（证明里好用） |
| `Inhabited` | 提供默认值 |
| `Hashable` | 可哈希（进 `HashMap`） |

### 泛型结构体

```lean
structure Pair (α : Type) where
  first : α
  second : α
deriving Repr

def p1 : Pair Nat := { first := 1, second := 2 }
def p2 : Pair String := { first := "左", second := "右" }
```

### 扩展另一个结构体

```lean
structure Point3D extends Point where
  z : Float
deriving Repr

def q : Point3D := { x := 1, y := 2, z := 3 }
#eval q.x    -- 继承字段直接用
#eval q.toPoint  --  ent 到 Point：{ x := 1.000000, y := 2.000000 }
```

### 给结构体挂方法

```lean
structure Point where
  x : Float
  y : Float
deriving Repr

def Point.magnitude (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

def Point.translate (p : Point) (dx dy : Float) : Point :=
  { p with x := p.x + dx, y := p.y + dy }

#eval (Point.mk 3 4).magnitude     -- 5.000000
#eval origin.translate 1 1         -- 点记号：第一个参数是「接收者」
```

> 💡 在类型 `Point` 的命名空间下定义 `magnitude`，即可写 `p.magnitude`——这是 Lean 的**点记号投影**（与字段访问同一套机制）。

---

## 5.2 归纳类型：一砖一瓦造世界

`inductive` 是 Lean 中**定义新类型的终极武器**。思想朴素得惊人：

> 一个归纳类型 = 列出构造它的所有方式（构造子）。

### 枚举

```lean
inductive Weekday where
  | monday | tuesday | wednesday | thursday
  | friday | saturday | sunday
deriving Repr, BEq

def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _                   => false

#eval Weekday.friday.isWeekend   -- false
```

七个构造子，就这么多。模式匹配保证不重不漏——漏了 Lean 会报 *missing cases*。

### 带数据的构造子：和类型

构造子可以携带数据，表达「**这个，或者那个**」：

```lean
inductive Shape where
  | circle (radius : Float) : Shape
  | rect (width height : Float) : Shape
deriving Repr

def Shape.area : Shape → Float
  | .circle r => Float.pi * r * r
  | .rect w h => w * h

#eval (Shape.circle 1.0).area   -- 约 3.141593
```

一个 `Shape` **要么**是圆（带半径），**要么**是矩形（带宽高）。这就是**和类型**（sum type）/ 标签联合。对比 Java 需要继承层次 + `instanceof`，Lean 里几行搞定，而且以后给 `Shape` 加了 `triangle`，所有忘记处理的函数都会被编译器点名。

### 递归构造子：列表和树

```lean
inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
deriving Repr

-- cons 1 (cons 2 (cons 3 nil)) 就是 [1,2,3]
def myListEx : MyList Nat := .cons 1 (.cons 2 (.cons 3 .nil))
```

标准库 `List α` 就是这个形状（`[]` 与 `::` 是语法糖）。二叉树：

```lean
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α
deriving Repr

def Tree.size : Tree α → Nat
  | .leaf       => 0
  | .node _ l r => 1 + l.size + r.size

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf       => .leaf
  | .node x l r => .node (f x) (l.map f) (r.map f)

def sample : Tree Nat :=
  .node 1 (.node 2 .leaf .leaf) (.node 3 .leaf .leaf)

#eval sample.size           -- 3
#eval (sample.map (· * 10)).size  -- 3
```

### 自然数：归纳类型的祖师爷

```lean
-- 标准库里的 Nat 本质如此（示意）
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

`zero` 是 0，`succ zero` 是 1，`succ (succ zero)` 是 2……**皮亚诺公理**。你写的 `5` 只是语法糖。

为什么这重要？因为**数学归纳法不是外加技巧，而是由定义自动生成的**：要证明性质对所有 `Nat` 成立，只需证 `zero` 情形和「若对 `n` 成立则对 `succ n` 成立」。每个归纳类型都会自动生成**归纳原理**（recursor / 递归子），这就是 `induction` 策略的来源（第 9 章详述）。

### 参数 vs 指标（先混个脸熟）

```lean
-- α 是参数：整个定义里固定
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α

-- n 是指标（index）：不同构造子可以落到不同的 n
-- 见后文 Vec
```

日常可以先记：**参数像泛型参数，指标像「类型里的值标签」**。

---

## 5.3 Option 和 Except：把「可能失败」写进类型

```lean
-- 标准库（示意）
inductive Option (α : Type) where
  | none : Option α
  | some : α → Option α
```

`Option α` = 要么有值 `some x`，要么没有 `none`。它是 Lean 对付「空指针」的武器——**函数可能没结果，从类型上就一目了然，编译器逼你处理**：

```lean
def describeHead (xs : List Nat) : String :=
  match xs.head? with
  | none   => "空的！"
  | some x => s!"首元素是 {x}"

#eval describeHead [10, 20]  -- 首元素是 10
#eval describeHead ([] : List Nat)  -- 空的！
```

### Option 上的组合（不用 Monad 也能写）

```lean
def Option.map (f : α → β) : Option α → Option β
  | none   => none
  | some x => some (f x)

def Option.andThen (x : Option α) (f : α → Option β) : Option β :=
  match x with
  | none   => none
  | some v => f v

-- 链式：取头再取「头的一半」（偶数才成功）
def halfHead (xs : List Nat) : Option Nat :=
  xs.head? |>.andThen fun n =>
    if n % 2 == 0 then some (n / 2) else none
```

第 7 章会看到：`andThen` 其实就是 monadic bind `>>=`，`do` 记法让链式更漂亮。

### Except：带错误信息

```lean
def parsePositive (s : String) : Except String Nat :=
  match s.toNat? with
  | none   => .error s!"'{s}' 不是数字"
  | some 0 => .error "必须是正数"
  | some n => .ok n

#eval parsePositive "42"   -- Except.ok 42
#eval parsePositive "0"    -- Except.error "必须是正数"
#eval parsePositive "ab"   -- Except.error ...
```

| 类型 | 失败时 | 适用 |
|------|--------|------|
| `Option α` | 只有「无」 | 查找、可选配置 |
| `Except ε α` | 带错误值 `ε` | 解析、校验、可诊断失败 |
| `IO`（第 7 章） | 真实世界副作用 | 文件、网络 |

### 回到第 4 章的 Expr：安全除法

```lean
inductive Expr where
  | num : Int → Expr
  | add : Expr → Expr → Expr
  | div : Expr → Expr → Expr
deriving Repr

def Expr.eval? : Expr → Option Int
  | .num n   => some n
  | .add a b =>
      match a.eval?, b.eval? with
      | some x, some y => some (x + y)
      | _, _           => none
  | .div a b =>
      match a.eval?, b.eval? with
      | some x, some y => if y == 0 then none else some (x / y)
      | _, _           => none

#eval (Expr.div (.num 10) (.num 2)).eval?  -- some 5
#eval (Expr.div (.num 10) (.num 0)).eval?  -- none
```

---

## 5.4 依赖类型：Lean 的超能力（初体验）

到目前为止的类型（`Nat`、`List α`、`Shape`）在其他函数式语言里也有。Lean 真正的杀手锏是**依赖类型**（dependent types）：**类型可以依赖于值**。

### 定长向量 Vec

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```

注意 `Vec α n` 的 `n` 是**类型的一部分**：`Vec Nat 3` 和 `Vec Nat 4` 是不同的类型！

```lean
def v2 : Vec Nat 2 := .cons 10 (.cons 20 .nil)

-- 类型错误：右边是 Vec Nat 1，左边要 Vec Nat 2
-- def bad : Vec Nat 2 := .cons 1 .nil
```

安全的「取头」——空向量根本没有这个方法的类型：

```lean
def Vec.head : Vec α (n + 1) → α
  | .cons x _ => x

#eval Vec.head v2   -- 10
-- Vec.head (Vec.nil : Vec Nat 0)  -- 类型检查失败，漂亮！
```

`map` 保持长度关系写在类型里：

```lean
def Vec.map (f : α → β) : Vec α n → Vec β n
  | .nil       => .nil
  | .cons x xs => .cons (f x) (xs.map f)
```

普通语言的类型系统只能管「形状对不对」，Lean 能管「**长度关系对不对**」。到第 8 章我们会把这条路线推到底：类型 → 命题，类型检查 → 证明检查。

### Fin：小于 n 的自然数

```lean
-- 概念上：Fin n ≃ { i : Nat // i < n }
#check (2 : Fin 5)   -- 可以
-- #check (5 : Fin 5) -- 不行，5 < 5 为假
```

用 `Fin n` 做下标，越界在类型层就被拒绝。第 14 章验证软件时会大量用这类技巧。

### 依赖函数类型（Π 类型）一眼

```lean
-- 普通函数：返回类型固定
#check fun x : Nat => x + 1

-- 依赖函数：返回类型可以提到参数
-- 例：给定 n，返回「长度为 n 的全 0 向量」
def zeros : (n : Nat) → Vec Nat n
  | 0     => .nil
  | n + 1 => .cons 0 (zeros n)

#eval zeros 3   -- 三个 0
```

`(n : Nat) → Vec Nat n` 读作：「对每个 `n`，给出一个 `Vec Nat n`」。这就是依赖函数类型（也叫 Π 类型）。你已经会写了——只是以前没强调名字。

---

## 5.5 子类型：给类型加约束

另一种精化手段是**子类型**（subtype）——「满足某个性质的那些值」：

```lean
def EvenNat := { n : Nat // n % 2 = 0 }

def four : EvenNat := ⟨4, by decide⟩
--                            ^^^ 必须现场提供「4 是偶数」的证明

#eval four.val    -- 4，取出底层 Nat
```

`{ n : Nat // P n }` 读作「满足性质 `P` 的 `Nat` 所成的类型」。构造时必须**连证明一起给**。mathlib 里到处都是（`Fin n` 就是 `{ i : Nat // i < n }` 的包装）。

初学阶段：

- 会读 `{ x : α // P x }` 这种类型；
- 会用 `⟨值, 证明⟩` 构造；
- 会用 `.val` 取出值。

证明部分用 `by decide` / `by omega` 等「小自动」即可，系统学证明从第 8 章开始。

---

## 5.6 类型宇宙：一分钟讲清 Type 与 Prop

问：`Nat` 的类型是什么？答：`Nat : Type`。
再问：`Type` 的类型是什么？

如果 `Type : Type`，会推出逻辑悖论（类似罗素 / 说谎者悖论）。Lean 的解法是**宇宙层级**：

```
Prop    : Type
Type    : Type 1     -- Type 是 Type 0 的别名
Type 1  : Type 2
Type 2  : Type 3
...
```

| 宇宙 | 住着什么 | 备注 |
|------|----------|------|
| `Prop` | 命题（可被证明/证伪的陈述） | 证明无关性：同一命题的两个证明在运行期不可区分 |
| `Type` / `Type 0` | 普通数据类型 | `Nat`、`List α`、`Point`… |
| `Type 1` 及以上 | 大宇宙 | 装 `Type`、装范畴等大对象 |
| `Sort u` | 统一写法 | `Sort 0 = Prop`，`Sort (u+1) = Type u` |

写泛型时可以用宇宙多态：

```lean
def id' {α : Type u} (x : α) : α := x
```

> 💡 **日常 99% 时间不用操心宇宙**。Lean 会自动推断。只有写很抽象的库、或看到 `universe u` / `Type u` 报错时，再回来查这一节。

> 📖 **和第 8 章的接头**：`Prop` 和 `Type` 分离，使得「证明」可以在编译后擦掉，而「程序数据」保留——这是证明与计算共存的关键设计。

---

## 5.7 踩坑对照

| 症状 | 原因 | 处理 |
|------|------|------|
| `type mismatch` 两个结构体字段一样却不能混用 | 名义类型：名字不同就不同类型 | 显式转换字段，或 `extends` / 写转换函数 |
| 模式匹配 `missing cases` | 漏了构造子 | 补全；或故意用 `@[match_pattern]` 等高级手段（暂不必） |
| `Option` 上直接当有值用 | 忘了解包 | `match` / `\|>.getD default` / monadic `do` |
| `Vec` 长度对不上 | 指标算错 | 看报错里的 `Nat` 等式，改定义或加类型标注 |
| `⟨4, ?_⟩` 证明填不出 | 需要命题证明 | `by decide`、`by omega`、或先学第 8–9 章 |
| `#eval` 显示结构体失败 | 缺 `Repr` | `deriving Repr` |
| `Float` 上用 `decide` 证相等 | 浮点不可判定相等 | 演示用 `Nat`/`Int`；浮点比较要谨慎 |

---

## 5.8 和标准库 / mathlib 对照

| 我们练的 | 库里的地道对应 |
|----------|----------------|
| `MyList` | `List`（`Init.Data.List`） |
| `Tree` | 可自建；mathlib 有更多树与集合结构 |
| `Option` / `Except` | 同名标准库，配套 `map`/`bind`/``do`` |
| `Vec α n` | 数学侧常用 `Vector` / `Fin n → α` / `Matrix`；核心思想一致 |
| `EvenNat` 子类型 | mathlib 大量 `Subtype`、`Finset` 等 |
| `Point` 结构体 | 几何库、物理量封装同一 idiom |

> 去定义处跳转时，你会看到标准库写得更短、更多宇宙多态——先求懂，再求像。

---

## 5.9 迷你项目：带标签的待办与安全队列

把结构体、归纳类型、`Option` 串成一个小模型：

```lean
structure Task where
  title : String
  urgent : Bool
deriving Repr, BEq

inductive Priority where
  | low | medium | high
deriving Repr, BEq, Ord

def Task.priority (t : Task) : Priority :=
  if t.urgent then .high else .medium

/-- 简单 FIFO 队列：用两个列表摊销实现（示意） -/
structure Queue (α : Type) where
  front : List α
  back  : List α
deriving Repr

def Queue.empty : Queue α := ⟨[], []⟩

def Queue.enqueue (q : Queue α) (x : α) : Queue α :=
  { q with back := x :: q.back }

def Queue.dequeue (q : Queue α) : Option (α × Queue α) :=
  match q.front, q.back with
  | x :: xs, b => some (x, ⟨xs, b⟩)
  | [],      [] => none
  | [],      b  =>
      -- 把 back 翻转成 front
      match b.reverse with
      | []     => none
      | x :: xs => some (x, ⟨xs, []⟩)

def demo : Option (Task × Queue Task) :=
  let q := Queue.empty
    |>.enqueue { title := "写第 5 章", urgent := true }
    |>.enqueue { title := "买菜", urgent := false }
  q.dequeue

#eval demo
```

扩展想法：给 `Queue` 加 `length`、`peek`；用 `Vec` 做固定容量缓冲（满则 `Except`）。

---

## 5.10 本章小结

- **`structure`** 打包数据，支持泛型、扩展、函数式更新、`deriving`；
- **`inductive`** 列出所有构造方式：枚举、和类型、递归类型（列表/树/`Nat`）；
- **模式匹配穷尽性**由编译器检查，改类型时旧代码会被追着报错——这是特性；
- **`Option` / `Except`** 把失败写进类型，强迫处理；
- **依赖类型**让类型依赖值：`Vec α n`、`Fin n`、子类型 `{x // P x}`；
- **宇宙**：`Prop : Type : Type 1 : ...`，日常多半自动推断。

---

## 练习

### ⭐ 基础

1. 定义归纳类型 `Color`（红绿蓝），写 `mix : Color → Color → Color`（自定混合规则），`deriving Repr` 后 `#eval`。
2. 为 `Point` 写 `distance : Point → Point → Float`。
3. 用 `Option` 写 `List.last? : List α → Option α`。

### ⭐⭐ 进阶

4. 给第 4 章 `Expr` 加 `div`，实现 `evalSafe : Expr → Except String Int`，除零返回清晰错误信息。
5. 定义 `Tree.depth` 与 `Tree.map`，并对样例树 `#eval`。
6. 实现 `Vec.append : Vec α m → Vec α n → Vec α (m + n)`——让类型报错引导你写对。

### ⭐⭐⭐ 硬核

7. 定义「已排序列表」：`SortedList := { xs : List Nat // isSorted xs }`，先定义 `isSorted : List Nat → Prop`（可用递归命题；证几个小例子 `⟨[1,2,3], by ...⟩`）。
8. 实现 `Vec.zipWith (f : α → β → γ) : Vec α n → Vec β n → Vec γ n`。

---

## 延伸阅读

| 资源 | 读什么 | 关系 |
|------|--------|------|
| [*Theorem Proving in Lean 4*](https://lean-lang.org/theorem_proving_in_lean4/) 第 7 章 Inductive Types | 归纳类型与递归原理 | 比本章更形式 |
| [*Functional Programming in Lean*](https://lean-lang.org/functional_programming_in_lean/) 「Overloading and Type Classes」前的数据结构章 | 结构体与归纳 | 编程视角补充 |
| [*TPIL*](https://lean-lang.org/theorem_proving_in_lean4/) 依赖类型相关章节 | Π 类型、Σ 类型 | 接第 8 章 |
| Language Reference · Inductive types | 精确语法 | 查阅用 |

---

⬅️ [第 4 章](04-functional-programming.md) ｜ ➡️ 下一章：[第 6 章　类型类：Lean 的「接口」](06-typeclasses.md)
