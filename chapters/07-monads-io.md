# 第 7 章　Monad 与 IO：和真实世界打交道

> 本章目标：拆掉 Monad 的「神秘面纱」，学会在 Lean 里写读写文件、打印输出、处理错误与状态的真实程序。学完后你能用 `do` 写出命令行小工具，并理解为何策略系统也是 Monad。

## 本章你会做出什么

1. 用 `do` 消灭 `Option` 嵌套地狱；
2. 跑通 `main : IO Unit`（打印、读入、文件、异常）；
3. 用 `StateM` / `Except` 各写一个小例子；
4. 完成「单词统计」命令行工具骨架。

先给结论：

> **Monad 是一种「带额外效果的计算」的统一包装。** 不同 Monad = 不同效果：`Option` 是「可能失败」，`IO` 是「能碰真实世界」，`State` 是「带着可变状态」。

---

## 7.1 从一个痛点说起

「查用户 → 解析年龄 → 判断是否成年」，每步都可能失败：

```lean
def findUser (id : Nat) : Option String :=
  if id == 1 then some "18" else none

def parseAge (s : String) : Option Nat :=
  s.toNat?

def isAdult (n : Nat) : Option Bool :=
  some (n ≥ 18)

-- 朴素写法：嵌套地狱
def checkNested (id : Nat) : Option Bool :=
  match findUser id with
  | none   => none
  | some s =>
    match parseAge s with
    | none   => none
    | some a => isAdult a
```

每一层都在重复：**上一步失败就整体失败，否则拆包继续**。三步三层，十步就没法读了。

Monad 把这个模式抽象掉：

```lean
def check (id : Nat) : Option Bool := do
  let s ← findUser id
  let a ← parseAge s
  isAdult a

#eval check 1    -- some true
#eval check 99   -- none
```

`do` + `←`（输入 `\left` 或 `\l`）去掉所有样板。代码重新像直线。

---

## 7.2 Monad 的定义：就三样东西

```lean
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
```

| 组件 | 含义 | 对 `Option` |
|------|------|-------------|
| `pure` | 把普通值装进 `m`，无额外效果 | `some` |
| `bind` / `>>=` | 执行前一步，把值喂给下一步 | `none` 短路，`some v` 则 `f v` |
| `do` | `>>=` 的语法糖 | `let s ← x; rest` ⇒ `x >>= fun s => rest` |

概念上的 `Option` 实例：

```lean
instance : Monad Option where
  pure a := some a
  bind x f := match x with
    | none   => none
    | some a => f a
```

整个「神秘」的 Monad 核心就这些。其余全是应用。

### Functor 与 Applicative（弟弟们）

| 抽象 | 能力 | 一句话 |
|------|------|--------|
| **Functor** | `map` | 在包装里映射纯函数 |
| **Applicative** | `pure` + 包装函数套包装值 | 多路独立效果可组合 |
| **Monad** | 再加 `bind` | **后一步可以依赖前一步的值** |

```lean
#eval Functor.map (· + 1) (some 3)   -- some 4
#eval List.map (· + 1) [1, 2, 3]     -- List 也是 Functor
```

日常写业务几乎只摸 `do`；读库文档时见到这三个词知道层级即可。

### `do` 语法速查

```lean
def demo : Option Nat := do
  let x ← some 3          -- 绑定
  let y := x + 1          -- 纯 let（不拆包装）
  if y > 10 then none     -- 分支
  else pure (y * 2)       -- pure / return 装回
```

- `let x ← mx`：拆 monadic 值；
- `let y := e`：普通绑定；
- `return` / `pure`：包回去（在 `IO` 里更常见 `return`）；
- 最后一个表达式若类型已是 `m β`，可直接作为结果。

---

## 7.3 IO Monad：触碰真实世界的通行证

纯函数不能读文件、不能打印——否则「纯」无从谈起。Lean 的方案：

> **凡是和真实世界交互的计算，都打上 `IO` 标记。**

```lean
def main : IO Unit := do
  IO.println "你叫什么名字？"
  let stdin ← IO.getStdin
  let name ← stdin.getLine
  IO.println s!"你好，{name.trim}！"
```

要点：

- `main : IO Unit` 是可执行入口（`Unit` ≈ void）；
- `IO α` =「做完副作用后产生 `α` 的动作」；
- `do` 里看起来像命令式：顺序、`let`、`if`；
- 纯函数里**拆不开** `IO`——除非你在另一个 `IO` 里组合它。类型把纯与不纯隔开。

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
    IO.eprintln s!"读文件失败：{e}"
    pure ""
```

### 循环、`mut`、提早返回

```lean
def countdown : IO Unit := do
  for i in [5, 4, 3, 2, 1] do
    IO.println s!"{i}..."
  IO.println "发射！"

def sumUpTo (n : Nat) : IO Nat := do
  let mut total := 0
  for i in [0:n+1] do
    total := total + i
  return total
```

`let mut` + `:=` 看起来像可变变量，编译器背后译成**状态传递**（`State` 式语义），**不破坏纯函数根基**。这是 Lean 4 哲学：命令式舒适外表 + 可推理内核。

### 如何运行

```bash
# 在 lake 项目中
lake env lean --run Main.lean
# 或定义 [[lean_exe]] 后
lake exe my_app
```

单文件玩 `IO` 时也可用 `lake env lean --run file.lean`（需有 `main`）。

---

## 7.4 常用 Monad 大观园

| Monad | 效果 | 典型用途 |
|-------|------|----------|
| `Option` | 失败无信息 | 查找、简单解析 |
| `Except ε` | 失败带 `ε` | 可诊断错误 |
| `StateM σ` / `State σ` | 读写状态 `σ` | 计数器、符号表、遍历累积 |
| `ReaderT ρ` | 只读环境 | 全局配置 |
| `Writer` | 追加日志 | 警告收集 |
| `IO` | 真实世界 | 文件、网络、终端 |
| `EIO` / `BaseIO` 等 | IO 变体 | 更细的错误/基础 IO |
| `TermElabM`、`TacticM`… | 编译期效果 | 元编程、策略（第 17–19 章） |

### State：计数器

```lean
def tick : StateM Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

#eval Id.run do
  -- 也可用 StateT.run
  pure ()

#eval (do
  let a ← tick
  let b ← tick
  pure (a, b) : StateM Nat (Nat × Nat)).run 0
-- 结果形如 ((0, 1), 2)：返回值与最终状态
```

（若你的工具链上 `StateM.run` 用法略有差异，以编辑器提示为准；思想都是「状态进、状态出」。）

### Except：带信息失败

```lean
def divide (a b : Nat) : Except String Nat :=
  if b = 0 then throw "除数不能为零" else pure (a / b)

def demo : Except String Nat := do
  let x ← divide 10 2
  let y ← divide 10 0   -- 短路
  pure (x + y)

#eval demo   -- Except.error "除数不能为零"
```

### 手动 bind 对照 do

```lean
def checkBind (id : Nat) : Option Bool :=
  findUser id >>= fun s =>
  parseAge s >>= fun a =>
  isAdult a
-- 与 7.1 的 do 版等价
```

会翻译 `do`，读别人底层代码时不慌。

---

## 7.5 迷你项目：单词统计命令行工具

可放入 `Main.lean`，用 `lake exe` 运行：

```lean
def wordCount (path : String) : IO Unit := do
  try
    let content ← IO.FS.readFile path
    let words := content.splitOn " " |>.filter (fun w => !w.isEmpty)
    let lines := content.splitOn "\n"
    IO.println s!"行数：{lines.length}"
    IO.println s!"单词数：{words.length}"
    IO.println s!"字符数：{content.length}"
  catch _ =>
    IO.eprintln s!"错误：无法读取文件 {path}"

def main (args : List String) : IO Unit := do
  match args with
  | [path] => wordCount path
  | _      => IO.eprintln "用法：wc <文件路径>"
```

麻雀虽小：参数、IO、异常、字符串处理——你已经能用 Lean 写日常工具。

### 扩展：词频 Top-K（练习预告）

思路：

1. `words` 列表 → 折叠进 `Std.HashMap String Nat`；
2. 转列表、按次数排序、`take 5`；
3. 打印。

`HashMap` 需要 `Hashable` / `BEq` 实例（`String` 已有）。这是第 6 章类型类的实战。

---

## 7.6 纯核心 + 薄 IO 壳（工程模式）

验证与测试友好的结构：

```lean
/-- 纯逻辑：可测试、可证明 -/
def countWordsPure (content : String) : Nat × Nat × Nat :=
  let words := content.splitOn " " |>.filter (fun w => !w.isEmpty)
  let lines := content.splitOn "\n"
  (lines.length, words.length, content.length)

/-- 薄壳：只做 IO -/
def wordCount' (path : String) : IO Unit := do
  let content ← IO.FS.readFile path
  let (lc, wc, cc) := countWordsPure content
  IO.println s!"行数：{lc} 单词数：{wc} 字符数：{cc}"
```

第 14 章验证软件时，几乎总是：**证明对着纯核心，IO 壳尽量薄**。

---

## 7.7 为什么这对「证明」也重要？

1. **策略系统本身是 Monad**（`TacticM`）：第 18 章写自定义策略就是写 monadic 程序；
2. **验证带副作用程序**时，monadic 语法让「效果」有结构可循；
3. Lean 编译器、mathlib 自动化，全是大型 monadic 代码库。

所以 Monad 不是学院派摆设——它是 Lean 全栈（运行时 + 编译期）的通用效果接口。

---

## 7.8 踩坑对照

| 症状 | 原因 | 处理 |
|------|------|------|
| 在纯函数里 `IO.println` | 类型是 `IO Unit` 不是 `Unit` | 把逻辑放进 `IO` 或抽纯函数 |
| `let x ← some 1` 在非 do / 非 Monad 上下文 | 缺少 Monad 作用域 | 包进 `do` 且返回类型是 monadic |
| `main` 不跑 | 没 `--run` / 没配 `lean_exe` | 查 lake 配置 |
| `←` 写了 `<-` 半角问题 | 字符不对 | 用 `\l` 输入 `←` |
| `for` 里改外面的 `let` | 不可变 | 用 `let mut` |
| `Option` 与 `Except` 混 `←` | 不同 Monad | `monadLift` 或统一错误类型；初学先别混 |
| 想 `unsafePerformIO` | 破坏纯 | 不要；设计上隔离 IO |

---

## 7.9 本章小结

- **Monad** = 包装「带效果的计算」，核心 `pure` + `bind`，`do` 是糖；
- **`Option` / `Except`** 管失败，**`StateM`** 管状态，**`IO`** 管真实世界；
- `do` 里可用 `let mut`、`for`、`try/catch`——命令式外表、纯内核；
- 工程上 **纯核心 + 薄 IO 壳**；
- 策略与元编程也是 Monad，这是后文的预告片。

---

## 练习

### ⭐ 基础

1. 用 `do` 写 `divThenAdd (a b c : Nat) : Option Nat`：算 `(a/b) + c`，除数为 0 则 `none`。
2. 写 `IO` 程序：打印 1 到 10，再打印它们的和。

### ⭐⭐ 进阶

3. 用 `StateM (List Nat)` 实现：`push` 三次 1、2、3 后状态为 `[3,2,1]`（栈顶在前）。
4. 把 7.5 的 `wordCount` 改成「纯核心 + 薄壳」，并为纯函数写 3 个 `#eval` 测试用例。
5. 用 `Except String` 重写 `divThenAdd`，错误信息区分「除数为零」与其它。

### ⭐⭐⭐ 硬核

6. 给 wordCount 加「出现次数最多的 5 个单词」（`HashMap` + 排序）。
7. （思考）若存在 `unsafeRunIO : IO α → α`，等式推理与「纯函数可缓存」哪些保证会崩？写一段你的论证。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| [FPIL · Monads](https://lean-lang.org/functional_programming_in_lean/) | 系统讲法 + 练习 |
| FPIL · Monad Transformers | 组合多种效果（本书从略） |
| 标准库 `IO`、`System.FilePath` | API 查阅 |
| 第 18 章 | `TacticM` 实战 |

---

⬅️ [第 6 章](06-typeclasses.md) ｜ ➡️ 下一章：[第 8 章　命题即类型：证明的本质](08-propositions-as-types.md)
