# 附录 C　术语表

> 按主题分类编排，每条尽量标注本书相关章节。括号内为英文。读到某章遇到不熟的概念，可来此速查；反过来想找某概念在哪章详讲，也能从分类入口定位。

## C.1 基础理论与逻辑

| 术语 | 英文 | 解释 | 章节 |
|------|------|------|------|
| 柯里-霍华德对应 | Curry-Howard correspondence | 命题=类型、证明=程序的对应关系，Lean 的理论基石 | 第 8 章 |
| 命题即类型 | propositions as types | 把命题当作类型，证明当作该类型的项 | 第 8 章 |
| 证明即程序 | proofs as programs | 同上另一面：构造程序即构造证明 | 第 8 章 |
| 命题 | proposition | `Prop` 类型的元素，即"陈述" | 第 5、8 章 |
| 公理 | axiom | 不证自明引入的常量（如选择公理 `Classical.choice`） | 第 8 章 |
| 排中律 | law of excluded middle | `P ∨ ¬ P`，经典逻辑标志；mathlib 默认可用 | 第 8 章 |
| 选择公理 | axiom of choice | `Classical.choice`，从非空集合选元素 | 第 8 章 |
| 经典逻辑 | classical logic | 容许排中律/选择公理的推理 | 第 8、11 章 |
| 构造主义逻辑 | constructive logic | 不假设排中律，证明即构造；Lean 默认构造，但 mathlib 经典化 | 第 8 章 |
| 决定性 | decidable | 命题可由算法判定真伪，`Decidable` 类型类 | 第 5、10 章 |
| 决定性/可判定命题 | decidable proposition | 可被 `decide` 处理的命题 | 第 10 章 |
| 模式匹配 | pattern matching | 按构造子形状分解数据 | 第 4、5 章 |
| 等式反射 | reflexivity / `rfl` | 证定义性相等，包括 `a = a` | 第 8、9 章 |

## C.2 类型系统

| 术语 | 英文 | 解释 | 章节 |
|------|------|------|------|
| 类型宇宙 | universe | `Prop : Type : Type 1 : ...` 的层级系统，避免自指悖论 | 第 5 章 |
| 宇宙多态 | universe polymorphism | `Type u`：对任意宇宙层级通用的代码 | 第 5 章 |
| 依赖类型 | dependent type | 类型依赖于值（如 `Vec α n`），Lean 的核心能力 | 第 5 章 |
| 归纳类型 | inductive type | 由构造子列表定义的类型 | 第 5 章 |
| 构造子 | constructor | 归纳类型的"构造方式"（如 `Nat.zero`、`Nat.succ`） | 第 5 章 |
| 归纳原理 | induction principle / recursor | 每个归纳类型自动生成的归纳证明/递归定义原理 | 第 5 章 |
| 递归子 | recursor | 同上，`T.rec`，归归纳类型生成的消去原理 | 第 5 章 |
| 结构体 | structure | 命名字段的打包（单构造子归纳类型的糖） | 第 5 章 |
| 记录 | record | 结构体的别称（其他语言术语） | 第 5 章 |
| 子类型 | subtype | `{ x : α // P x }`，"满足性质的那些值" | 第 5 章 |
| 定义性相等 | definitional equality | 按定义展开/计算后相等，`rfl` 能证的相等 | 第 5、9 章 |
| 定义上相等 | definitional / judgmental equality | 同定义性相等 | 第 5、9 章 |
| 命题等价 | propositional equality | 需要（非 `rfl`）证明的相等，`a = b` 作为命题 | 第 8 章 |
| 派生实例 | deriving / `deriving` | 自动生成 `Repr`、`Decidable`、`BEq` 等实例 | 第 5、6 章 |
| 类型类 | type class | "某类型提供某组操作/定律"的抽象机制 | 第 6 章 |
| 实例 | instance | 类型类的具体实现 | 第 6 章 |
| 实例隐参 | instance implicit | `[C α]` 形式的参数，由类型类推断自动填充 | 第 6 章 |
| 类型类层级 | type class hierarchy | 群→半群→幺半群→群…的层级组织 | 第 6、12 章 |
| 类型类法则 | laws | 类型类要求满足的定律（如结合律） | 第 6 章 |
| 函子 | Functor | 可 `map` 的容器抽象 | 第 7 章 |
| 适用函子 | Applicative | Functor + `pure` + 包装应用 | 第 7 章 |
| 单子 | Monad | 统一包装"带效果的计算"的抽象（`pure` + `bind`） | 第 7 章 |

## C.3 编程概念

| 术语 | 英文 | 解释 | 章节 |
|------|------|------|------|
| 一等公民 | first-class | 函数/值可被传递、返回、赋值 | 第 4 章 |
| 匿名函数 | lambda / `fun` | `fun x => e`，又称 lambda 表达式 | 第 4 章 |
| 柯里化 | currying | 多参数函数 = 逐参数返回函数的函数 | 第 4 章 |
| 闭包 | closure | 捕获了环境变量的函数值 | 第 4 章 |
| 高阶函数 | higher-order function | 以函数为参数或返回值的函数 | 第 4 章 |
| 纯函数 | pure function | 无副作用、同输入必同输出的函数 | 第 4 章 |
| 副作用 / 效果 | side effect | IO、状态、异常等，由 Monad 显式标记 | 第 7 章 |
| 不可变性 | immutability | 值一旦创建不再改变；"修改"即新建 | 第 4 章 |
| 持久化数据结构 | persistent data structure | 新旧版本共享结构的不可变数据结构 | 第 4 章 |
| functional but in-place | functional but in-place | Lean 4 的就地更新优化：纯函数外表，C 级性能 | 第 4 章 |
| 惰性求值 | lazy evaluation | 需要时才计算，`Thunk` 实现 | 第 4 章 |
| 严格求值 | strict / eager evaluation | 参数先算好再进函数，Lean 默认 | 第 4 章 |
| 管道符 | pipeline `|>` | `x \|> f` 等价 `f x`，左向右流动 | 第 4 章 |
| 函数组合 | composition `∘` | `(f ∘ g) x = f (g x)` | 第 4 章 |
| map/filter/fold | map / filter / fold | 列表处理三板斧：映射、过滤、折叠 | 第 4 章 |
| 递归 | recursion | 函数调用自身实现重复 | 第 4 章 |
| 互递归 | mutual recursion | 多个函数相互调用定义 | 第 5 章 |
| 终止性检查 | termination check | Lean 强制每个函数可证停机 | 第 4 章 |
| `termination_by` | termination_by | 显式指定递归的"递减度量" | 第 4 章 |
| `do` 记法 | do-notation | monadic 链式计算的命令式语法糖 | 第 7 章 |
| `IO` | IO | 与真实世界交互的单子（读写、环境） | 第 7 章 |
| `ST` / 可变引用 | ST / mutable reference | 局部可变状态，对外仍纯函数 | 第 7 章 |
| `Option` | Option | `some a / none`，建模可能失败的计算 | 第 5、7 章 |
| `Except` | Except | 带错误信息的失败单子 | 第 7 章 |

## C.4 证明与策略

| 术语 | 英文 | 解释 | 章节 |
|------|------|------|------|
| 策略 | tactic | 交互式证明中操作证明状态的命令/程序 | 第 9–10、18 章 |
| 策略模式 | tactic mode | `by` 之后的证明书写方式 | 第 9 章 |
| 项模式 | term mode | 不用 `by`，直接写证明项的方式 | 第 8 章 |
| 内核 | kernel | 检查证明项的最小可信核心 | 第 1、18 章 |
| 精化器 | elaborator | 把高层语法变成内核可检查的项的编译器组件 | 第 1、17–18 章 |
| 元变量 | metavariable | 待填的"洞"（`?m.123`），策略操作的对象 | 第 18 章 |
| 目标 | goal | 当前待证明的命题（`⊢` 之后） | 第 9 章 |
| 局部上下文 | local context | 当前可用的变量与假设集合 | 第 9 章 |
| 假设 | hypothesis | 上下文中已知的命题证据 | 第 9 章 |
| 引理 / 定理 | lemma / theorem | 已证明的命题（Lean 中两者同义，风格之别） | 第 8 章 |
| `sorry` | sorry | 证明占位符，等价于引入 `sorryAx` 公理 | 第 9、10 章 |
| `#print axioms` | print axioms | 检查定理依赖哪些公理（查 `sorryAx` 泄漏） | 第 10、22 章 |
| `calc` | calc | 等式/不等式链式书写 | 第 10、11 章 |
| `conv` | conv | 聚焦目标子表达式做转换 | 第 10 章 |
| 自动化策略 | automation tactic | `omega`/`ring`/`grind`/`aesop` 等自动求解器 | 第 10 章 |
| 重写 | rewriting / `rw` | 用等式在目标/假设中替换 | 第 9–10 章 |
| 化简 | simplification / `simp` | 用引理集自动简化 | 第 10 章 |
| `grind` | grind | Lean 4 新一代通用自动化策略 | 第 10 章 |
| `omega` | omega | Nat/Int 线性算术决策过程 | 第 10 章 |
| 检索增强证明 | retrieval-augmented proving | 从引理库检索相关定理辅助生成策略（ReProver） | 第 20 章 |
| 生成器 + 验证器 | generator + verifier | AI 出候选、内核判对错的范式 | 第 20 章 |

## C.5 元编程与 DSL

| 术语 | 英文 | 解释 | 章节 |
|------|------|------|------|
| 元编程 | metaprogramming | 用 Lean 写操作 Lean 编译过程的程序 | 第 17–19 章 |
| 宏 | macro | 语法树到语法树的编译时变换 | 第 17 章 |
| 卫生宏 | hygienic macro | 自动避免变量捕获的宏系统 | 第 17 章 |
| 准引用 | quotation | `` `( ... ) `` 语法模板记法 | 第 17 章 |
| 记号 | notation | 轻量级语法扩展（文本替换级） | 第 17 章 |
| 语法类别 | syntax category | `declare_syntax_cat` 定义的领域语法族 | 第 17、19 章 |
| 精化命令 | elab | 可运行编译器内部逻辑的语法扩展 | 第 17–18 章 |
| `macro_rules` | macro_rules | 按语法模式递归展开的规则集 | 第 17、19 章 |
| `TacticM` | TacticM | 策略运行的 monad，提供操作证明状态的 API | 第 18 章 |
| `MetaM` | MetaM | 元级 monad，提供表达式构造与合一 | 第 18 章 |
| 抽象语法树 | AST | 语言的树状语义表示 | 第 4、19 章 |
| DSL / EDSL | (embedded) domain-specific language | 领域专用语言 / 内嵌于宿主语言的版本 | 第 19 章 |
| 语义函数 | semantic function | `eval : AST → Env → Result`，赋予 AST 意义 | 第 19 章 |
| 三层架构 | three-layer architecture | 语法层→语义层→定理层的 DSL 蓝图 | 第 19 章 |

## C.6 验证与工程

| 术语 | 英文 | 解释 | 章节 |
|------|------|------|------|
| 形式化验证 | formal verification | 用机器检查的数学证明保证系统性质 | 第 14 章 |
| 形式化 | formalization | 把数学/系统用精确语言写出 | 第 11、13 章 |
| 规格 | specification (spec) | 系统应满足性质的精确陈述 | 第 14 章 |
| 不变量 | invariant | 系统运行中始终保持的性质 | 第 14、15 章 |
| 前置/后置条件 | pre/postcondition | 执行前/后需满足的条件 | 第 14 章 |
| 霍尔逻辑 | Hoare logic | `{P} prog {Q}` 的程序推理体系 | 第 14 章 |
| 精化 | refinement | 抽象规格逐步实现为具体程序 | 第 14 章 |
| 信任基 | trusted base (TCB) | 必须信任而未被验证的部分（内核、编译器、硬件…） | 第 14、22 章 |
| 模型检查 | model checking | 在有限状态空间上自动穷尽验证 | 第 14 章 |
| 差分测试 | differential testing | 同一输入对拍两个实现找分歧 | 第 15 章 |
| SMT | satisfiability modulo theories | 带理论的布尔可满足性求解（Z3 等） | 第 14 章 |
| 可判定性 | decidability | 问题能否被算法判定 | 第 10、14 章 |
| 编译器验证 | compiler verification | 证明编译器对一切源程序保持语义 | 第 22 章 |
| 算术化 | arithmetization | 把计算转成多项式/电路约束（零知识证明） | 第 16 章 |
| R1CS | rank-1 constraint system | 零知识证明常用的约束格式 | 第 16 章 |
| SNARK | succinct non-interactive argument of knowledge | 简洁非交互式知识论证 | 第 16 章 |
| 零知识证明 | zero-knowledge proof | 证明知悉秘密而不泄露秘密的协议 | 第 16 章 |
| zkVM | zero-knowledge VM | 区块链零知识虚拟机电路 | 第 16、21 章 |
| 安全性 / 活性 | safety / liveness | "坏事不发生" / "好事终会发生" | 第 15 章 |
| ISA 语义 | ISA semantics | 指令集架构的形式化语义 | 第 21 章 |
| 蓝图 | blueprint | 把大证明拆成带依赖图的小引理的协作方法 | 第 13、21 章 |

## C.7 生态与工具

| 术语 | 英文 | 解释 | 章节 |
|------|------|------|------|
| mathlib | mathlib | Lean 社区数学库（百万行级） | 第 11–13 章 |
| CSLib | CSLib | Lean 计算机科学库 | 第 13 章 |
| Std / Batteries | Std / Batteries | 标准库扩展（数据结构、工具） | 第 4–7 章 |
| Lake | Lake | Lean 构建工具，随工具链附带 | 第 2 章 |
| elan | elan | Lean 工具链版本管理器 | 第 2 章 |
| Reservoir | Reservoir | Lean 包注册中心 | 第 22 章 |
| Infoview | Infoview | VS Code 插件中显示证明状态的面板 | 第 2、9 章 |
| Lean FRO | Lean Focused Research Organization | 维护 Lean 核心的非营利组织 | 第 1、22 章 |
| Loogle | Loogle | 按类型签名搜定理的引擎 | 第 11 章 |
| LeanSearch / Moogle | LeanSearch / Moogle | 自然语言搜定理的引擎 | 第 11、20 章 |
| LeanDojo | LeanDojo | 让机器程序化访问 Lean 的研究基础设施 | 第 20 章 |
| Pantograph | Pantograph | 底层机器交互接口（表达式级） | 第 20 章 |
| Lean REPL | Lean REPL | 机器可交互的读-求值-印循环 | 第 20 章 |
| AlphaProof | AlphaProof | DeepMind 的自动证明系统 | 第 20 章 |
| Verso | Verso | 用 Lean 写书/文档的原生平台 | 第 21 章 |
| 自然数游戏 | Natural Number Game | Buzzard 制作的 Lean 入门通关游戏 | 第 21 章 |
| Zulip | Zulip | Lean 社区主阵地（含中文频道） | 第 22 章 |
| MWE | minimal working example | 最小可复现例子，提问的标准格式 | 第 22 章 |
| Blueprint 模式 | blueprint collaboration | 大规模形式化协作的拆引理模式 | 第 13、21 章 |
| Lean Together | Lean Together | 年度 Lean 社区会议 | 第 22 章 |

---

⬅️ [附录 B　常用资源与工具清单](appendix-b-resources.md) ｜ 🏠 [返回首页](00-preface.md)