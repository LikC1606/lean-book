# 第 4 章　函数式编程的基本功

> 本章目标：掌握函数式编程的核心思维——函数是一等公民、数据不可变、用组合代替循环。

如果你来自 Python/Java/C++ 的世界，这一章会改变你写程序的方式。函数式编程（FP）不是炫技，而是一套**让程序更容易推理**的纪律。而"容易推理"正是 Lean 能做定理证明的根本原因。

## 4.1 函数是一等公民

在 Lean 里，函数和数字、字符串一样，是普通的值。你可以：

**把函数赋给变量：**

```lean
def double : Nat → Nat := fun n => 2 * n
#eval double 5   -- 10
```

`fun n => 2 * n` 是匿名函数（lambda），读作"接收 n，返回 2*n"。

**把函数当参数传：**

```lean
def applyTwice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

#eval applyTwice double 3      -- 12（翻倍两次：3→6→12）
#eval applyTwice (· + 1) 3     -- 5（加一两次）
```

**把函数当返回值：**

```lean
def makeAdder (k : Nat) : Nat → Nat := fun n => n + k

def add5 := makeAdder 5
#eval add5 10   -- 15
```

`makeAdder 5` 生成了一个"加 5 专用函数"。这种"函数工厂"是 FP 的常用套路，术语叫**闭包**（closure）——返回的函数记住了 `k` 的值。

### 类型注解：`Nat → Nat` 怎么读

`f : Nat → Nat` 读作"f 是从自然数到自然数的函数"。`→` 是**右结合**的：

```
Nat → Nat → Nat   等价于   Nat → (Nat → Nat)
```

所以 `add : Nat → Nat → Nat` 实际是"接收一个 Nat，返回一个 Nat→Nat 函数"——这就是柯里化的类型表达。

## 4.2 不可变性：一旦出生，永不改变

```lean
def xs := [1, 2, 3]
def ys := xs ++ [4]   -- 拼接出新列表

#eval xs   -- [1, 2, 3]，原列表纹丝不动
#eval ys   -- [1, 2, 3, 4]
```

Lean 里没有 `xs.push(4)` 这种"原地修改"。所有操作都返回**新值**。

> 🤔 **这样不是很浪费内存吗？**
> 不用担心。Lean 的运行时使用**持久化数据结构**（persistent data structures）：新列表和旧列表**共享**没变的部分。而且 Lean 4 有独特的**就地更新**优化（functional but in-place）：当编译器能证明旧值此后不再被使用时，会直接复用其内存——纯函数式的外表，C 语言的性能。这是 Lean 4 论文的招牌技术之一。

不可变性带来的好处是实打实的：

- **没有意外的副作用**：函数拿到什么就是什么，不会被别的代码偷偷改掉；
- **并发天然安全**：不可变数据随便多线程共享，不需要锁；
- **可以"等式推理"**：`f x = f x` 永远成立——这是做数学证明的基石。

## 4.3 三板斧：map、filter、fold

命令式语言用循环做的事，FP 用三个高阶函数解决 80%：

```lean
def nums := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

-- map：每个元素变一变
#eval nums.map (· * 2)          -- [2, 4, 6, ..., 20]

-- filter：留下满足条件的
#eval nums.filter (· % 2 == 0)  -- [2, 4, 6, 8, 10]

-- fold：把所有元素"折叠"成一个值
#eval nums.foldl (· + ·) 0      -- 55（累加）
```

`foldl` 的类型值得细看：

```lean
List.foldl : (β → α → β) → β → List α → β
```

读法：给一个"把累计值和新元素合成新累计值"的函数、一个初始累计值、一个列表，返回最终累计值。求和、求积、找最大、拼字符串……都是 fold。

三者经常串联成**管道**：

```lean
-- 1~10 中偶数的平方和
#eval nums.filter (· % 2 == 0) |>.map (· ^ 2) |>.foldl (· + ·) 0
-- 4 + 16 + 36 + 64 + 100 = 220
```

`|>` 是管道符：`x |> f` 就是 `f x`，让代码从左向右流动，可读性极佳。

## 4.4 组合：把小程序拼成大程序

函数式编程的精髓是**组合**（composition）：每个函数只做一件事，然后像乐高一样拼起来。

```lean
def isEven (n : Nat) : Bool := n % 2 == 0
def square (n : Nat) : Nat := n * n

-- 函数组合：先 square 再 isEven
def isEvenSquare := isEven ∘ square

#eval isEvenSquare 4   -- true（16 是偶数）
#eval isEvenSquare 3   -- false
```

`∘`（输入 `\circ`）是数学里的复合符号：`(f ∘ g) x = f (g x)`。

一个更实际的例子——统计文本中长度超过 3 的单词数：

```lean
def countLongWords (text : String) : Nat :=
  text.splitOn " "
    |>.filter (fun w => w.length > 3)
    |>.length

#eval countLongWords "the quick brown fox jumps over the lazy dog"
-- 4（quick, brown, jumps, over, lazy → 5？动手验证一下！）
```

（小陷阱留给你：实际结果是 5 还是 4？为什么？动手 `#eval` 一下就知道。）

## 4.5 递归：函数式编程的"循环"

没有 for/while（其实 Lean 有，见第 7 章，但纯函数式风格首选递归），重复靠递归表达：

```lean
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

#eval factorial 5   -- 120
```

Lean 会**检查递归终止**：每次调用的参数必须"变小"。对列表递归时，参数从 `x :: xs` 变成 `xs`；对自然数递归时，从 `n + 1` 变成 `n`——都是严格变小的，编译器才放行。

有些递归"变小"的方式不那么显然，比如：

```lean
def gcd (a b : Nat) : Nat :=
  if b = 0 then a else gcd b (a % b)
termination_by b
```

`termination_by b` 告诉 Lean："请盯着 `b`，它每次都在变小"（因为 `a % b < b`）。这套**终止性论证**机制保证了 Lean 里每个函数都会停机——对数学证明至关重要（会后面会看到，能死循环的逻辑系统可以"证明"任何东西，那就毫无价值了）。

## 4.6 惰性求值与严格求值

Lean 默认是**严格求值**（像大多数语言）：参数先算好再进函数。需要惰性（比如处理潜在无穷的数据流）时，用 `Thunk`（`Thunk.mk fun _ => ...`）把计算"包起来"，需要时再 `Thunk.get`。日常代码里用得不多，知道有这回事即可。

## 4.7 实战：写一个 JSON 风格的求值器

把本章知识串起来，写一个表达式求值器：

```lean
inductive Expr where
  | num : Nat → Expr            -- 数字字面量
  | add : Expr → Expr → Expr    -- 加法
  | mul : Expr → Expr → Expr    -- 乘法
deriving Repr

def eval : Expr → Nat
  | .num n   => n
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b

def exampleExpr : Expr := .mul (.add (.num 1) (.num 2)) (.num 3)  -- (1+2)*3

#eval eval exampleExpr   -- 9
```

`inductive`（归纳类型）下一章会细讲，这里先感受：**用一小套构造规则描述语法，用模式匹配递归地赋予语义**——这是编程语言理论的看家本领，也是 Lean 最擅长的领域（毕竟 Lean 自己的编译器就是这么写的）。

## 4.8 本章小结

- 函数是值：可以传递、返回、组合；`fun x => ...` 创建匿名函数；
- 数据不可变：所有"修改"都是创建新值，运行时靠结构共享和就地更新保证性能；
- `map` / `filter` / `fold` + 管道符 `|>` 是日常数据处理的主力；
- 递归必须有**终止性论证**，Lean 强制检查；
- 组合优于循环，小函数拼出大程序。

## 练习

1. 用 `foldl` 实现 `myLength : List α → Nat`（不许用 `.length`）；
2. 实现 `compose2 : (β → γ) → (α → β) → α → γ`，即自己写一遍 `∘`；
3. 写一个函数 `primesUpTo (n : Nat) : List Nat`，用"筛法"思路：从 2 开始，每次留下不能被已有素数整除的数（提示：`List.filter` + 递归）；
4. 扩展 4.7 的求值器：加一个 `neg : Expr → Expr` 构造子表示取负，并让 `eval` 返回 `Int`。

## 延伸阅读

- 《Functional Programming in Lean》第 2–3 章；
- 论文 *The Lean 4 Theorem Prover and Programming Language*（CADE-28）中关于 "functional but in-place" 的章节。

---

⬅️ [第 3 章](03-first-steps.md) ｜ ➡️ 下一章：[第 5 章　类型、结构体与归纳类型](05-types-inductive.md)
