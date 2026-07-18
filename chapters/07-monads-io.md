# 第 7 章　Monad 与 IO：和真实世界打交道

> 本章目标：拆掉 Monad 这层"神秘面纱"，学会在 Lean 里写读写文件、打印输出、处理错误的真实程序。

Monad（单子）大概是编程界名声最坏的概念——"Monad 不就是自函子范畴上的幺半群吗"这个梗吓退过无数人。本章用大白话把它讲清楚。先给结论：

> **Monad 是一种"带额外效果的计算"的统一包装。** 不同的 Monad = 不同的效果：`Option` 是"可能失败"，`IO` 是"能碰真实世界"，`State` 是"带着可变状态"。

## 7.1 从一个痛点说起

写一段"查询用户年龄再判断是否成年"的逻辑，每个步骤都可能失败：

```lean
def findUser (id : Nat) : Option String := ...
def parseAge (s : String) : Option Nat := ...
def isAdult (n : Nat) : Option Bool := ...

-- 朴素写法：嵌套地狱
def check (id : Nat) : Option Bool :=
  match findUser id with
  | none   => none
  | some s =>
    match parseAge s with
    | none   => none
    | some a => isAdult a
```

每一层都在重复同一个模式："**上一步失败了就直接失败，否则把值拆出来继续**"。三个步骤就套了三层，十步呢？

Monad 就是把这个模式**抽象出来**：

```lean
def check (id : Nat) : Option Bool := do
  let s ← findUser id     -- 失败则整个计算失败，否则 s = 拆出来的值
  let a ← parseAge s
  isAdult a
```

`do` 记法 + `←`（输入 `\l`）把"拆包装、传接力棒"的样板代码全干掉了。代码重新变得像直线一样好读。

## 7.2 Monad 的定义（别怕，就三样东西）

```lean
class Monad (m : Type → Type) where
  pure : α → m α                    -- 把普通值装进 m
  bind : m α → (α → m β) → m β      -- 接力：拆出值，交给下一步
```

- `pure`：把干净的值包装成"带效果但什么都没发生"的计算。对 `Option` 就是 `some`；
- `bind`（中缀写法 `>>=`）：`x >>= f` 读作"执行 x，把结果值喂给 f"。对 `Option`：x 是 `none` 则整体 `none`，是 `some v` 则 `f v`；
- `do` 记法只是 `>>=` 的语法糖：`let s ← x; rest` 翻译为 `x >>= fun s => rest`。

`Option` 的 Monad 实例（概念上）：

```lean
instance : Monad Option where
  pure a     := some a
  bind x f   := match x with
                | none   => none
                | some a => f a
```

整个"神秘"的 Monad 就这么多。剩下的全是应用。

### 顺手一提：Functor 和 Applicative

Monad 有两个"弟弟"抽象，能力更弱但出现更早：

- **Functor**：只有 `map : (α → β) → m α → m β`（在包装里面映射）；
- **Applicative**：多了 `pure` 和"包装着的函数应用到包装着的值"；
- **Monad**：再多 `bind`，允许**后一步依赖前一步的值**。

日常写代码几乎只用 `do` 记法，这层继承关系了解即可。

## 7.3 IO Monad：触碰真实世界的通行证

纯函数不能读文件、不能打印——否则"纯"就无从谈起。Lean 的方案：**凡是和真实世界交互的计算，都打上 `IO` 的标记。**

```lean
def main : IO Unit := do
  IO.println "你叫什么名字？"
  let stdin ← IO.getStdin
  let name ← stdin.getLine
  IO.println s!"你好，{name.trim}！"
```

要点：

- `main : IO Unit` 是程序入口（`Unit` 类似 `void`，表示"没有有意义的返回值"）；
- `IO α` 读作"一个会产生 `α` 的 IO 动作"；
- 在 `do` 块里，代码看起来**和命令式语言一模一样**——按顺序执行、可以 `let`、可以 `if`；
- 类型系统把"纯"和"不纯"分得清清楚楚：纯函数里**不可能**偷偷做 IO（`IO` 的包装拆不开，除非你在另一个 `IO` 动作里）。

### 读写文件

```lean
def copyFile (src dst : System.FilePath) : IO Unit := do
  let content ← IO.FS.readFile src
  IO.FS.writeFile dst content
  IO.println s!"已复制 {src} → {dst}"
```

### 错误处理：`try / catch`

```lean
def safeRead (path : System.FilePath) : IO String := do
  try
    IO.FS.readFile path
  catch e =>
    IO.println s!"读文件失败：{e}"
    pure ""   -- 返回默认空串
```

### 循环：Lean 也有 `for`

```lean
def countdown : IO Unit := do
  for i in [5, 4, 3, 2, 1] do
    IO.println s!"{i}..."
  IO.println "发射！🚀"
```

Lean 甚至支持**可提早返回**和**局部可变变量**（在 do 块里）：

```lean
def sumUpTo (n : Nat) : IO Nat := do
  let mut total := 0
  for i in [0:n+1] do
    total := total + i
  return total
```

`let mut` + `:=` 看着像可变变量，但请放心——编译器在背后把它翻译成了纯函数式的状态传递（`State` monad 的语法糖），**纯函数的语义一点没破坏**。这是 Lean 4 设计哲学的体现：给程序员命令式的舒适，给证明器纯函数式的保证。

## 7.4 常用 Monad 大观园

| Monad | 效果 | 典型用途 |
|-------|------|----------|
| `Option` | 可能失败（无错误信息） | 查找、解析 |
| `Except ε` | 可能失败（带错误 `ε`） | 需要报错信息的场合 |
| `State σ` | 携带可读写状态 `σ` | 遍历中累积、编译器符号表 |
| `Reader ρ` | 只读环境 `ρ` | 全局配置 |
| `Writer ω` | 追加日志 `ω` | 收集警告、追踪 |
| `IO` | 真实世界交互 | 文件、网络、终端 |
| `EStateM` / `EST` | 状态 + 异常 + IO 的组合 | Lean 编译器内部 |
| `TermElabM`、`TacticM`… | 编译期效果 | 元编程（第 17–19 章） |

看两个例子感受下：

```lean
-- State：维护一个计数器
def tick : StateM Nat Nat := do
  let n ← get          -- 读状态
  set (n + 1)          -- 写状态
  pure n               -- 返回旧值

#eval (do let a ← tick; let b ← tick; pure (a, b)).run 0
-- ((0, 1), 2)：两次取到 0 和 1，最终状态 2

-- Except：带信息的失败
def divide (a b : Nat) : Except String Nat :=
  if b = 0 then throw "除数不能为零" else pure (a / b)

def demo : Except String Nat := do
  let x ← divide 10 2    -- x = 5
  let y ← divide 10 0    -- 抛错，整个计算短路
  pure (x + y)           -- 不会执行到

#eval demo   -- Except.error "除数不能为零"
```

## 7.5 实战：一个单词统计命令行工具

把本章拼起来，写一个真正的程序（可放入 `Main.lean`，`lake exe` 运行）：

```lean
def wordCount (path : String) : IO Unit := do
  try
    let content ← IO.FS.readFile path
    let words := content.splitOn |>.filter (fun w => !w.isEmpty)
    let lines := content.splitOn "\n"
    IO.println s!"行数：{lines.length}"
    IO.println s!"单词数：{words.length}"
    IO.println s!"字符数：{content.length}"
  catch _ =>
    IO.eprintln s!"错误：无法读取文件 {path}"

def main (args : List String) : IO Unit := do
  match args with
  | [path]  => wordCount path
  | _       => IO.eprintln "用法：wc <文件路径>"
```

麻雀虽小，五脏俱全：参数处理、IO、异常捕获、字符串处理——你已经会用 Lean 写日常工具了。

## 7.6 为什么这对"证明"也重要？

你可能以为 Monad 只是编程的事。错了：

1. **Lean 的策略（tactic）系统本身就是 Monad**（`TacticM`），第 18 章你写自己的策略时会和它朝夕相处；
2. **验证有副作用的程序**时（第 14 章），monadic 程序的结构让"对效果做推理"变得可操作；
3. Lean 编译器、mathlib 的自动化工具，全都是大型 monadic 程序。

## 7.7 本章小结

- Monad = 统一包装"带效果的计算"，核心是 `pure` + `bind`，`do` 是糖；
- `Option`/`Except` 处理失败，`IO` 处理真实世界，`State` 处理状态；
- `do` 块里可以写 `let mut`、`for`、`return`、`try/catch`——命令式的外表，纯函数的内核；
- 类型系统把纯与不纯严格隔离，这正是 Lean 能对带效果程序做形式化推理的前提。

## 练习

1. 用 `do` 记法重写：`Option` 版本的"两个数相除再相加"——`divThenAdd : Nat → Nat → Nat → Option Nat`（任何一次除数为 0 返回 `none`）；
2. 用 `StateM (List Nat)` 实现"逆序压栈"：依次 `push 1`、`push 2`、`push 3`，最后状态是 `[3, 2, 1]`（栈顶在前）；
3. 给 7.5 的 wordCount 加功能：统计出现次数最多的 5 个单词（提示：`List.groupBy` 或自己折叠一个 `HashMap`）；
4. （思考题）为什么纯函数里拆不开 `IO α` 这个包装？如果允许 `unsafeRunIO : IO α → α`，Lean 的哪些保证会崩塌？

## 延伸阅读

- 《Functional Programming in Lean》"Monads" 与 "Monad Transformers" 章节（本书略去的 monad transformer 可在此进阶）；
- Lean 标准库文档中的 `IO`、`System` 模块。

---

⬅️ [第 6 章](06-typeclasses.md) ｜ ➡️ 下一章：[第 8 章　命题即类型：证明的本质](08-propositions-as-types.md)
