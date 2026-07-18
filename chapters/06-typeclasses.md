# 第 6 章　类型类：Lean 的"接口"

> 本章目标：掌握类型类（type class）——Lean 实现"多态"和"运算符重载"的机制，也是 mathlib 组织整个数学大厦的脚手架。

## 6.1 问题：`+` 到底有多少种？

自然数能加，整数能加，浮点数能加，字符串不能加（用 `++`）……`+` 这个符号背后是不同的实现。Java 用接口 + 重载，Python 用鸭子类型，C++ 用运算符重载——Lean 的答案是**类型类**。

一个类型类就是一句话：

> "凡是属于这个类的类型，都提供这样一组操作。"

看最核心的例子之一：

```lean
class Add (α : Type) where
  add : α → α → α
```

读法：类型 `α` 是 `Add` 类的一个**实例**，当且仅当我们给出了 `α → α → α` 的实现。你天天写的 `x + y`，实际上是通过标准库中 `Add` 的实例解析出具体加法。

## 6.2 定义类型类与实例

我们自己定义一个类型类："可以被转换成字符串展示"。

```lean
class Show (α : Type) where
  show : α → String

-- 给 Nat 一个实例
instance : Show Nat where
  show n := s!"数字 {n}"

-- 给 Bool 一个实例
instance : Show Bool where
  show b := if b then "真" else "假"

#eval Show.show 42     -- 数字 42
#eval Show.show true   -- 真
```

然后写**对任意 Show 类型都成立**的泛型函数：

```lean
def display [Show α] (x : α) : String :=
  "内容是：" ++ Show.show x

#eval display 7       -- 内容：数字 7
#eval display false   -- 内容：假
```

`[Show α]` 是**实例隐参**（用方括号）：意思是"这个函数对任何类型 `α` 都能用，只要 `α` 有 `Show` 实例"。调用时你**不需要**手动传入实例——Lean 的**类型类推断**（type class inference）会自动去"实例库"里找。找不到？编译报错，提醒你先提供实例。

> 💡 和 Java 接口的微妙差别：实例**不属于**类型本身，而是独立注册的全局"配件"。所以你可以给别人的类型（比如标准库的 `Nat`）添加你自己类的实例——这在 Java 里做不到（不能给 `final` 的 `Integer` 加接口），在 Haskell/Lean 里是日常操作。

## 6.3 实例也可以"泛型"

如果 `α` 能 show，那 `List α` 也能 show——把每个元素 show 出来拼起来：

```lean
instance [Show α] : Show (List α) where
  show xs := "[" ++ String.intercalate ", " (xs.map Show.show) ++ "]"

#eval display [1, 2, 3]   -- 内容：[数字 1, 数字 2, 数字 3]
```

实例可以带前提（`[Show α]`），类型类推断会**递归地**组装：要 show `List Nat`，先找 `List α` 的实例，发现需要 `Nat` 的实例，再找，找到，收工。这套递归合成机制非常强大——mathlib 里"矩阵的元素是环则矩阵是环"这类层层嵌套的代数结构，全靠它自动组装。

## 6.4 标准库里的常用类型类

Lean 标准库已经预装了一大批类型类，眼熟即可：

| 类型类 | 提供什么 | 例子 |
|--------|----------|------|
| `Add` | `+` | `Nat`、`Int`、`Float` |
| `Mul` | `*` | 同上 |
| `Neg` | `-x`（一元负号） | `Int`、`Float` |
| `BEq` | `==`（布尔相等） | 大多数数据类型 |
| `DecidableEq` | 可判定的 `=` | 证明中常用 |
| `Repr` | 可打印表示（`#eval` 显示用） | `deriving Repr` |
| `ToString` | `toString` | 同上 |
| `Inhabited` | 一个默认值 `default` | `Nat` 的是 `0` |
| `Ord` | 比较（`compare`） | 排序需要 |
| `Hashable` | 哈希 | 哈希表需要 |
| `Functor` | `map` | `List`、`Option` |
| `Monad` | `>>=`、`do` 记法 | 第 7 章主角 |

`deriving` 机制就是为常用类自动生成实例：

```lean
structure Color where
  r g b : Nat
deriving Repr, BEq, Inhabited

#eval ({ r := 1, g := 2, b := 3 } : Color) == default   -- false
```

## 6.5 类型类 vs 结构体：一个常见困惑

新手常问："类型类长得像结构体，到底啥区别？"

- **结构体**是"把数据打包"：你可以有任意多个 `Point` 值，它们互不相关；
- **类型类**是"给类型贴标签"：每个类型对同一个类**至多一个实例**（Lean 强制），实例由编译器自动查找，你几乎从不手动传递。

判断该用哪个的经验法则：**需要编译器自动帮你找到的东西，用类型类；需要手动传来传去的配置，用结构体。**

## 6.6 数学味道的预告：类型类如何支撑 mathlib

本书第四部分会看到，整个 mathlib 的代数大厦是用类型类搭起来的：

```lean
class Zero (α : Type) where zero : α           -- 有零元
class One (α : Type) where one : α             -- 有壹元
class Semigroup (α : Type) extends Mul α where -- 半群：乘法 + 结合律
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
class Monoid (α : Type) extends Semigroup α, One α where  -- 幺半群
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
```

注意 `mul_assoc` 等字段的类型是**命题**——类型类不仅能携带操作，还能携带**定律（证明）**！于是"群的定理自动适用于所有群实例（整数、矩阵、置换……）"。这是把"接口"的概念推到了极致：接口不仅规定操作，还规定操作必须遵守的**公理**。

## 6.7 参数、隐参、实例隐参：三种括号

借此机会彻底理清 Lean 函数的三种参数括号，新手最常在这里迷路：

```lean
def example1 (x : Nat) : Nat := x + 1      -- ( ) 显式参数：调用时必须给
def example2 {α : Type} (x : α) : α := x   -- { } 隐式参数：Lean 自动推断
def example3 [Show α] (x : α) : String := Show.show x  -- [ ] 实例隐参：类型类推断自动填
```

- `( )`：普通的、调用时明确给出的参数；
- `{ }`：能从其他参数/返回值推断出来的，调用时省略（比如 `List.map` 的类型参数）。需要手动给时用 `@`：`@List.map Nat Nat f xs`；
- `[ ]`：类型类约束，由实例搜索自动解决。

## 6.8 本章小结

- 类型类 = "某类型提供某组操作（乃至定律）"的声明；`instance` 注册实例；
- `[Class α]` 标记实例隐参，编译器自动完成**递归实例搜索**；
- 标准库用类型类组织运算符重载（`Add`/`Mul`/`BEq`/`Repr`…）；
- 类型类可以携带**证明字段**——这是 mathlib 代数层级的基石；
- 三种括号 `( )`、`{ }`、`[ ]` 分别对应显式、隐式、实例隐参。

## 练习

1. 定义类型类 `Sized`（提供 `size : α → Nat`），给 `List β`、`String`、`Tree β`（第 5 章定义过）各写一个实例；
2. 写泛型函数 `doubleAll [Add α] : List α → List α`，把列表每个元素变成 `x + x`，分别在 `List Nat` 和 `List Int` 上测试；
3. 定义实例 `instance [Repr α] : Repr (Option α)`，使得 `#eval (some 3 : Option Nat)` 打印 `some 3`；
4. （思考题）为什么 Lean 要限制"每个类型对每个类至多一个实例"？如果允许两个 `Add Nat` 实例（一个普通加法、一个模 7 加法），会出什么问题？（提示：想想自动搜索该怎么办。这也是 `Finset` 等场景需要"包装类型"（type synonym/newtype）的原因。）

## 延伸阅读

- 《Functional Programming in Lean》"Type Classes" 一章；
- 《Mathematics in Lean》第 6 章（代数结构中的类型类实战）。

---

⬅️ [第 5 章](05-types-inductive.md) ｜ ➡️ 下一章：[第 7 章　Monad 与 IO：和真实世界打交道](07-monads-io.md)
