# 第 6 章　类型类：Lean 的「接口」

> 本章目标：掌握类型类（type class）——Lean 实现「多态」和「运算符重载」的机制，也是 mathlib 组织整个数学大厦的脚手架。学完后你能自己定义类与实例，读懂 `[Add α]`，并理解为什么 mathlib 的群/环定理能「一次证明，处处适用」。

## 本章你会做出什么

1. 自定义 `Show` / `Sized` 类，并给 `Nat`、`List` 写实例；
2. 写依赖类型类约束的泛型函数（如 `doubleAll`）；
3. 分清 `( )` / `{ }` / `[ ]` 三种参数；
4. 读懂一段「带定律的代数类型类」伪代码，为第 12 章铺路。

---

## 6.1 问题：`+` 到底有多少种？

自然数能加，整数能加，浮点数能加，字符串一般用 `++`……同一个符号 `+` 背后是不同实现。Java 用接口 + 重载，Python 用鸭子类型，C++ 用运算符重载——Lean 的答案是**类型类**。

一句话：

> 「凡是属于这个类的类型，都提供这样一组操作（有时还包括必须遵守的定律）。」

核心例子：

```lean
class Add (α : Type) where
  add : α → α → α

-- 标准库已为 Nat、Int、Float… 注册了 instance
#eval (3 : Nat) + 4      -- 走 Add Nat
#eval (3 : Int) + 4      -- 走 Add Int
```

你写的 `x + y`，实际是 `Add.add x y`，具体实现由**实例搜索**在编译期填好。

---

## 6.2 定义类型类与实例

自己做一个「能转成字符串展示」的类（教学用；标准库更常用 `Repr` / `ToString`）：

```lean
class Show (α : Type) where
  show : α → String

instance : Show Nat where
  show n := s!"数字 {n}"

instance : Show Bool where
  show b := if b then "真" else "假"

#eval Show.show 42     -- 数字 42
#eval Show.show true   -- 真
```

写**对任意 `Show` 类型都成立**的泛型函数：

```lean
def display [Show α] (x : α) : String :=
  "内容是：" ++ Show.show x

#eval display 7       -- 内容是：数字 7
#eval display false   -- 内容是：假
```

`[Show α]` 是**实例隐参**（方括号）：「对任何 `α` 可用，只要存在 `Show α` 实例」。调用时你**不用**手动传入实例——**类型类推断**（type class synthesis）会去全局实例库里找。找不到就报错，提示你先 `instance`。

> 💡 **和 Java 接口的差别**
>
> 实例**不属于**类型本身，而是独立注册的全局「配件」。你可以给别人的类型（如标准库 `Nat`）添加你自己类的实例——Java 做不到给 `Integer` 事后加接口，Haskell/Lean 里这是日常操作（*orphan instance* 要谨慎，但机制允许）。

### 用投影函数还是开命名空间

```lean
#eval Show.show 1
open Show
#eval show 1          -- 打开后可直接用字段名
```

---

## 6.3 实例也可以「泛型」：递归合成

若 `α` 能 show，则 `List α` 也能 show：

```lean
instance [Show α] : Show (List α) where
  show xs := "[" ++ String.intercalate ", " (xs.map Show.show) ++ "]"

#eval display [1, 2, 3]
-- 内容是：[数字 1, 数字 2, 数字 3]
```

实例带前提 `[Show α]` 时，推断会**递归组装**：

```
需要 Show (List Nat)
  → 找到 [Show α] : Show (List α)，还需 Show Nat
  → 找到 Show Nat
  → 完成
```

mathlib 里「矩阵元素是环 ⇒ 矩阵是环」「有限类型上的函数形成某某代数」全靠这套递归合成。

再嵌一层：

```lean
#eval display [[1, 2], [3]]
-- List (List Nat) → 两次递归
```

---

## 6.4 标准库里的常用类型类

| 类型类 | 提供什么 | 典型类型 |
|--------|----------|----------|
| `Add` / `Sub` / `Mul` / `Div` | `+ - * /` | `Nat`、`Int`、`Float` |
| `Neg` | 一元 `-` | `Int`、`Float` |
| `HAdd` 等 | **异构**运算（如 `Nat + Int`） | 混合算术 |
| `OfNat α n` | 字面量 `0`、`1`、`42` 属于 `α` | 自定义数系 |
| `BEq` | `==` | 多数数据 |
| `DecidableEq` | 可判定的 `=` | 证明与 `decide` |
| `Repr` | `#eval` 打印 | `deriving Repr` |
| `ToString` | `toString` | 日志、拼接 |
| `Inhabited` | `default` | `Nat` 默认 `0` |
| `Ord` | `compare` | 排序 |
| `Hashable` | 哈希 | `HashMap` |
| `Functor` | `Functor.map` | `List`、`Option` |
| `Monad` | `>>=`、`do` | 第 7 章 |
| `Coe α β` | 隐式强制转换 | `Nat` → `Int` |

### `deriving`：自动生成实例

```lean
structure Color where
  r g b : Nat
deriving Repr, BEq, Inhabited, DecidableEq

#eval ({ r := 1, g := 2, b := 3 } : Color) == default   -- false
#eval (default : Color)   -- { r := 0, g := 0, b := 0 }
```

能 `deriving` 就 deriving；不能的再手写 `instance`。

### `OfNat`：让字面量进你的类型

```lean
structure Mod7 where
  val : Nat
deriving Repr

instance : OfNat Mod7 n where
  ofNat := ⟨n % 7⟩

instance : Add Mod7 where
  add a b := ⟨(a.val + b.val) % 7⟩

#eval (3 : Mod7) + (6 : Mod7)   -- { val := 2 }
```

没有 `OfNat`，写 `(3 : Mod7)` 会类型错误——字面量 `3` 默认是 `Nat`。

---

## 6.5 类型类 vs 结构体

| | 结构体 `structure` | 类型类 `class` |
|--|-------------------|----------------|
| 目的 | 打包**数据** | 给类型贴**能力标签** |
| 值的数量 | 同一类型任意多个值 | 每个类型对每个类**通常至多一个**实例 |
| 传递方式 | 手动当参数传 | 编译器自动搜索 |
| 例子 | `Point`、`Config` | `Add`、`Monad`、`Group` |

经验法则：

- **需要编译器自动找到** → 类型类；
- **需要手动配置、可有多份** → 结构体（或以后用 *bundled* 设计，mathlib 两者都用）。

### 为什么「一个类型一个实例」？

若同时有两个 `Add Nat`（普通加法和模 7 加法），写 `1 + 1` 时搜索器不知道选谁——程序含义歧义。解决办法：包一层新类型（如上面的 `Mod7`），给**新类型**写 `Add` 实例。这就是 newtype 模式。

---

## 6.6 三种括号：`( )` `{ }` `[ ]`

新手最常迷路的地方，一次记清：

```lean
def ex1 (x : Nat) : Nat := x + 1
-- ( ) 显式参数：调用必须给

def ex2 {α : Type} (x : α) : α := x
-- { } 隐式参数：从上下文推断；强制手动给时用 @ex2 Nat 1

def ex3 [Show α] (x : α) : String := Show.show x
-- [ ] 实例隐参：类型类搜索填充
```

| 括号 | 名称 | 谁填充 | 强制指定 |
|------|------|--------|----------|
| `(a : T)` | 显式 | 调用者 | 直接写 |
| `{a : T}` | 隐式 | 统一器推断 | `@f 实参 ...` |
| `[C a]` | 实例 | 实例搜索 | `@f ...` 或 `have : C a := ...` |

```lean
#check List.map           -- 类型参数多半是隐式的
#check @List.map          -- @ 展开所有参数
```

---

## 6.7 实例搜索失败时怎么读报错

常见报错：

```text
failed to synthesize
  Show (Nat × Bool)
```

意思是：需要 `Show (Nat × Bool)`，但库里没有（也拼不出来）。

处理步骤：

1. 是否缺 `import`？
2. 是否该类型根本不该 `Show`，而是该用 `Repr`？
3. 自己补：

```lean
instance [Show α] [Show β] : Show (α × β) where
  show
    | (a, b) => s!"({Show.show a}, {Show.show b})"
```

4. 若是 mathlib 代数类，检查前提是否够（缺 `CommRing` 却用了交换律引理）。

调试时可尝试：

```lean
#synth Show (List Nat)    -- 看能否合成，成功会打印实例项
```

---

## 6.8 继承、`outParam` 与强制转换（进阶扫盲）

### 类可以 `extends`

```lean
class MulOneClass (α : Type) extends Mul α, One α where
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
```

子类自动带上父类字段；实例搜索时有子类常能推出父类。

### `outParam`：输出型参数

有时类的某个参数应由实例**决定**而不是由调用者先定死（如「α 的默认生成元类型」）。标准库用 `outParam` 标记。初学见到不慌：表示「这个参数是搜索的结果，不是输入」。

### `Coe`：隐式转换

```lean
#eval (3 : Nat) + (4 : Int)   -- 常靠 Coe / HAdd 等机制混算
```

自定义类型想「自动当成某类型用」可写 `Coe` 实例，但别滥用——隐式转换过多会让类型错误难读。

---

## 6.9 数学味道：类型类如何支撑 mathlib

整个 mathlib 代数大厦用类型类搭建（示意，真实层级更细）：

```lean
class Zero (α : Type) where zero : α
class One (α : Type) where one : α

class Semigroup (α : Type) extends Mul α where
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)

class Monoid (α : Type) extends Semigroup α, One α where
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a
```

注意 `mul_assoc` 的类型是**命题**——类型类不仅携带操作，还携带**定律（证明）**。于是：

> 对任意 `Monoid α` 证明的定理，自动适用于 `Nat` 乘法、矩阵乘法、函数复合……只要它们注册了实例。

这是把「接口」推到极致：**接口规定操作，也规定公理**。第 12 章会在真 mathlib 里碰 `Group`、`Ring`、`Field`。

---

## 6.10 踩坑对照

| 症状 | 原因 | 处理 |
|------|------|------|
| `failed to synthesize Add Foo` | 没写实例 | `instance : Add Foo where ...` |
| 两个模块两个 `Add Foo` 冲突 | 实例不唯一 | newtype 包装；或不要重复 instance |
| `display x` 报错但 `Show` 已写 | 类型太泛，α 未定 | 加类型标注 `(x : Nat)` |
| `deriving` 失败 | 字段里有不能自动推的类型 | 手写 instance |
| 字面量 `0` 不能当 `Foo` | 缺 `OfNat` | 补 `OfNat Foo n` |
| 和 Java 一样在类里「实现接口」 | 模型不对 | 在类型**外**写 `instance` |

---

## 6.11 迷你项目：可打印 + 可度量的配置

```lean
structure ServerConfig where
  host : String
  port : Nat
deriving Repr, BEq

class Sized (α : Type) where
  size : α → Nat

instance : Sized String where
  size s := s.length

instance : Sized ServerConfig where
  size c := c.host.length + c.port   -- 随意度量，示意

instance : Show ServerConfig where
  show c := s!"{c.host}:{c.port}"

def summarize [Show α] [Sized α] (x : α) : String :=
  s!"{Show.show x}（size = {Sized.size x}）"

#eval summarize { host := "localhost", port := 8080 : ServerConfig }
#eval summarize "hello"
```

体会：`summarize` 只要求「能 Show 且能 Sized」，不绑定具体类型——这就是类型类多态。

---

## 6.12 本章小结

- **类型类** =「某类型提供某组操作（及定律）」的声明；`instance` 注册；
- **`[Class α]`** 为实例隐参，编译器做**递归实例搜索**；
- 标准库用类型类组织运算符、打印、排序、Monad…；
- **`deriving` / `OfNat` / `Coe`** 是日常三件套；
- 类型类可带**证明字段** → mathlib 代数层级的基石；
- 三种括号：`(显式)` `{隐式}` `[实例]`。

---

## 练习

### ⭐ 基础

1. 定义 `Sized`（`size : α → Nat`），给 `List β`、`String` 写实例。
2. 写 `doubleAll [Add α] (xs : List α) : List α := xs.map (fun x => x + x)`，在 `List Nat` 与 `List Int` 上测试。

### ⭐⭐ 进阶

3. 定义 `instance [Show α] : Show (Option α)`，让 `display (some 3)` 合理输出。
4. 为第 5 章的 `Tree α` 写 `Sized` 与 `[Show α] : Show (Tree α)`（递归实例）。
5. 给 `Mod7` 补 `Mul` 与 `OfNat`，计算 `(3 : Mod7) * (5 : Mod7)`。

### ⭐⭐⭐ 硬核

6. （思考）若允许两个 `Add Nat`，自动搜索与 `simp` 会出什么问题？
7. 尝试 `#synth` 合成 `Add (List Nat)`——若失败，解释为何列表默认没有逐元 `+`，并手写一个 `instance [Add α] : Add (List α)`（对齐拉链相加；长度不同时你如何定义？）。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| [FPIL · Type Classes](https://lean-lang.org/functional_programming_in_lean/) | 程序员视角完整一章 |
| [MIL · Structures](https://leanprover-community.github.io/mathematics_in_lean/) | 代数结构与类型类实战 |
| TPIL 类型类相关节 | 与证明结合的细节 |
| 标准库 `Init.Prelude` 中的 `Add`/`Mul` | 看官方最小定义 |

---

⬅️ [第 5 章](05-types-inductive.md) ｜ ➡️ 下一章：[第 7 章　Monad 与 IO：和真实世界打交道](07-monads-io.md)
