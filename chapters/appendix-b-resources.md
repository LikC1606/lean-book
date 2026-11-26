# 附录 B　常用资源与工具清单

> 这是本书的「索引页」：所有值得收藏的链接、工具、库、社区都在这里。按类别整理，最后附「按学习路径推荐」与「如何提问」两节，帮你快速定位从哪开始。

**本书配套**：仓库 `examples/`（`lake build` 可构建，无 mathlib）；**附录 D** 官方难句白话；**附录 E** 自然数游戏关卡对照。

## B.1 官方资源

| 资源 | 地址/说明 |
|------|-----------|
| Lean 官网 | [lean-lang.org](https://lean-lang.org) |
| 在线运行 | [live.lean-lang.org](https://live.lean-lang.org)（浏览器直接写代码，无需安装） |
| 语言参考手册 | lean-lang.org → Documentation → Language reference |
| VS Code 插件 | 扩展市场搜 `lean4`（发布者 leanprover） |
| elan（版本管理） | `curl https://elan.lean-lang.org/elan-init.sh -sSf \| sh` |
| Lake（构建工具） | 随 Lean 自带，`lake` 命令即用 |
| Reservoir（包仓库） | [reservoir.lean-lang.org](https://reservoir.lean-lang.org) |
| Lean FRO | 维护 Lean 核心的非营利组织，官网 → FRO（路线图、博客、年度报告） |
| 官方博客 | lean-lang.org → Blog（语言/工具链重大变更第一手） |

## B.2 教科书（全部免费在线）

| 书名 | 适合谁 | 本书对应章节 |
|------|--------|--------------|
| *Functional Programming in Lean* (FPIL) | 程序员入门 | 第 2、4–7 章 |
| *Theorem Proving in Lean 4* (TPIL) | 定理证明系统教材 | 第 8–10 章 |
| *Mathematics in Lean* (MIL) | 数学背景者学 mathlib | 第 11–13 章 |
| *The Mechanics of Proof* | 数学系低年级证明课 | 第 8–9 章 |
| *The Hitchhiker's Guide to Logical Verification* | 逻辑验证进阶 | 第 14–15 章 |
| *Metaprogramming in Lean 4* | 元编程进阶 | 第 17–19 章 |
| *Logic and Proof* | 逻辑学基础（用 Lean 教） | 第 8 章 |
| *Concrete Semantics*（Lean 移植版） | 程序语义与验证 | 第 14 章 |
| *Software Foundations*（Coq 经典，思想通用） | 编译器验证 | 第 22 章 |
| Lean Language Reference | 精确查阅用 | 全书 |
| *Functional Programming in Lean* 进阶章 | 应用开发 | 第 7 章 |

> 📚 **使用建议**：这些书与本书互补——本书是"中文导览 + 全景地图"，英文教材是"深度细节"。读本书某章卡住时，去找对应英文书同一章细读，往往豁然开朗。

## B.3 游戏与交互学习

| 名称 | 说明 |
|------|------|
| Natural Number Game | 首选入门游戏：[adam.math.hhu.de](https://adam.math.hhu.de)，从定义自然数开始通关 |
| Lean Game Server | 集合论、Robo、谓词逻辑等更多游戏：同一平台 |
| Set Theory Game | 用游戏形式建立集合论直觉 |
| Robo | 逻辑/命题推理的关卡游戏 |
| live.lean-lang.org | 浏览器版 Lean，配合本网站可边读边练 |

## B.4 搜索工具（找定理必备）

| 工具 | 用法 | 强项 |
|------|------|------|
| Loogle | 按类型签名搜定理：[loogle.lean-lang.org](https://loogle.lean-lang.org) | 类型匹配精准 |
| LeanSearch | 自然语言搜定理：[leansearch.net](https://leansearch.net) | 大白话提问 |
| Moogle | 另一自然语言搜索 | 语义匹配，覆盖广 |
| LeanExplore | 语义化搜索 Lean 声明 | 探索式发现 |
| mathlib 文档站 | [leanprover-community.github.io/mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs) | 全文检索、跳转定义 |
| IDE 内搜索 | `exact?` `apply?` `rw?` `hint` `simp?` | 证明现场即时搜 |
| `#find` | 库内按模式搜引理 | 命令行也可用 |

> 🔍 **找定理工作流**（详见第 11 章）：命名约定猜名 → IDE 补全 → `exact?` → Loogle → LeanSearch → Zulip。

## B.5 AI 与机器接口

| 工具 | 说明 | 本书对应 |
|------|------|----------|
| Lean REPL | 机器可交互的读-求值-印循环（喂策略，返回状态 JSON） | 第 20 章 |
| LeanDojo | 数据抽取 + Gym 式证明环境（AI4Math 研究默认起点） | 第 20 章 |
| Pantograph | 底层机器交互（表达式级，面向 MCTS 搜索） | 第 20 章 |
| Lean4Web | 浏览器版 Lean（可嵌入教学网页） | 第 2 章 |
| AlphaProof / Nexus | DeepMind 的自动证明系统（研究展示） | 第 20 章 |
| ReProver | 检索增强证明模型（LeanDojo 配套） | 第 20 章 |
| 通用 LLM + 验证闭环 | 把 LLM 输出贴回 VS Code 让 Lean 检查 | 第 20 章 |
| [TheoremOS](https://github.com/HuggingMath/theorem-os) | Lean 4 数学研究工作台，可查看候选证明的检查反馈和所有原目标的验收结果。[中文免登录演练](https://app.theoremos.top/practice.html?lang=zh) | 第 20 章 |

## B.6 库与生态

| 库 | 领域 | 本书对应 |
|----|------|----------|
| mathlib4 | 数学（百万行级，社区共建） | 第 11–13 章 |
| CSLib | 计算机科学（算法、复杂度、自动机） | 第 13 章 |
| Std4 / Batteries | 标准库扩展（数据结构、工具） | 第 4–7 章 |
| ArkLib | SNARK/密码学形式化 | 第 16 章 |
| Veil | 分布式协议验证 | 第 15、19 章 |
| Aeneas | Rust → Lean 翻译验证 | 第 15 章 |
| Verso | 用 Lean 写书/文档（本书若用 Verso 写则代码永不过时） | 第 21 章 |
| StatLib | 数理统计库（新兴） | 第 13 章 |
| EconLib | 经济学理论形式化（Axiom 公司发起） | 第 13、21 章 |
| TorchLean | 连接 PyTorch 与 Lean（神经网络计算验证） | 第 13 章 |
| Lakeroad | 硬件电路 DSL / 验证 | 第 19 章 |
| FLT 项目 | 费马大定理形式化（Imperial College） | 第 13 章 |
| PFR 项目 | 多项式 Freiman–Ruzsa 猜想形式化 | 第 13 章 |

> 📦 **找新库**：去 Reservoir 浏览，或看 Zulip `#announce` 频道的新库发布。

## B.7 社区

| 地点 | 说明 |
|------|------|
| Zulip | [leanprover.zulipchat.com](https://leanprover.zulipchat.com)（含 `#Chinese` 中文频道、`#new members` 新手区） |
| GitHub | `leanprover/lean4` · `leanprover-community/mathlib4` · `leanprover-community/cslib` |
| Lean FRO | lean-lang.org → FRO（路线图、博客、年度报告） |
| 会议 | Lean Together（年度社区会议，含线上参与） |
| 视频 | YouTube 官方频道 + 各大学课程录像（搜 "Lean theorem prover"） |
| Xena Project 博客 | Kevin Buzzard 的数学形式化前线观察 |
| 引用 | CADE-28 论文 *The Lean 4 Theorem Prover and Programming Language*（bibtex 见官网） |

> 🤝 **社区文化**：Lean 社区以"友善对待新手"著称。`#new members` 任何问题都欢迎；维护者常亲自回复。学会提问（见 B.9）是融入社区的第一步。

## B.8 按学习路径推荐资源

不同读者的最短路径不同。下面把本书章节与外部资源串成三条主线。

### 路径 A：只想学编程（通用函数式编程）

1. 本书第 1–3 章（环境与上手）
2. 本书第 4–7 章（函数式编程、类型、类型类、Monad/IO）
3. 同步读 *Functional Programming in Lean* (FPIL)
4. 练手：在 Reservoir 找小项目，或写一个命令行小工具（第 7 章 IO）
5. 进阶：第 17 章（宏）让代码更地道

### 路径 B：只想学数学证明

1. 本书第 1–3 章（环境与上手，可略读第 7 章 IO）
2. 通关 *Natural Number Game*（强烈建议）
3. 本书第 8–10 章（命题即类型 + 策略）
4. 同步读 *The Mechanics of Proof*（证明手艺）或 *Mathematics in Lean* (MIL)
5. 本书第 11–13 章（mathlib），动手做 MIL 的练习
6. 进阶：认领 FLT/PFR blueprint 的小引理（第 22 章指引）

### 路径 C：关心工业应用（软件验证、密码学）

1. 本书第 1–3 章 + 第 4–6 章（编程基础必读）
2. 本书第 8–10 章（证明基础，验证需要）
3. 本书第 14–15 章（软件验证 + 工业案例）+ *Hitchhiker's Guide to Logical Verification*
4. 第 16 章（密码学）+ ArkLib 文档
5. 进阶：第 17–19 章（元编程/DSL，做验证工具必备）
6. 关注 Aeneas、Veil、ArkLib 的 GitHub 与论文

> ⏱️ **时间预估**：路径 A ≈ 2–3 周（每天 1–2 小时）；路径 B ≈ 4–6 周；路径 C ≈ 6–8 周。慢一点没关系，Lean 的回报是长期的。

## B.9 如何提问：MWE 与提问礼仪

Lean 社区回复快，但前提是问题问得好。**最有效的提问 = 一个最小可复现例子（MWE）**。

### 什么是 MWE？

一段**完整、可直接粘贴运行**的代码，包含：

1. 必要的 `import`（只 import 真正用到的，别 `import Mathlib` 全家桶）；
2. 触发问题的最小定理/定义；
3. 你的目标与实际报错。

### 反面教材（不要这样问）

> ❌ "我的证明挂了，怎么办？"

没有代码、没有目标、没有报错——没人能帮你。

### 正面示范

> ✅ "我想证下面的引理，`simp` 关不掉目标，报错 `unsolved goal`。请问哪里漏了？
>
> ```lean
> import Mathlib.Data.Nat.Basic
>
> example (n : Nat) (h : n + 1 = 2) : n = 1 := by
>   simp [h]
> ```
> 报错：`unsolved goal: n = 1`。"

这样的提问通常几分钟内就有答复。

### 提问技巧清单

- ✅ 提供完整 MWE（别人复制即可跑）；
- ✅ 说明你期望的结果 vs 实际结果；
- ✅ 说明你已经试过什么（`exact?`/`omega`/查过哪些引理）；
- ✅ 用 Zulip 的代码块格式（` ```lean ... ``` `）；
- ✅ 标题写清主题（"证明 `n + 1 = 2 → n = 1` 时 simp 关不掉"比"救命"好一万倍）；
- ❌ 不要把整个项目贴上去；
- ❌ 不要 `sorry` 完就贴——先把能证的部分证完；
- ❌ 不要在追问里删掉原始上下文（Zulip 用 topic/thread 回复）。

> 💡 Zulip 的 `#new members` 是为新手专门设的——你的"愚蠢"问题，可能正是别人的下一个问题。社区鼓励提问。

## B.10 本书相关命令速查

```bash
# ── 环境与版本 ──
elan default leanprover/lean4:stable   # 设默认 Lean 版本
elan show                               # 查看当前工具链
elan run leanprover/lean4:stable lean  # 临时用指定版本跑
lean --version                          # 查 Lean 版本

# ── 项目管理 ──
lake new my_proj                        # 新项目（纯 Lean）
lake new my_proj math                    # 新项目（带 mathlib 依赖，推荐）
lake new my_proj std                     # 新项目（带 Std 库）
lake build                              # 构建当前项目
lake build Mathlib.Data.Nat.Basic       # 只构建指定模块
lake exe <name>                          # 运行项目里的可执行 target
lake update                             # 更新依赖（更新 lakefile.lock）
lake exe cache get                       # 下载 mathlib 预编译缓存（必做！省数小时）
lake exe cache get -j 8                  # 多线程下载

# ── 单文件试验 ──
lean file.lean                           # 命令行编译/检查单文件
lean --run file.lean                     # 运行含 main 的文件

# ── 数据/工具（社区） ──
lake exe lean4lean-toolname               # 各项目自带工具，见其 README
```

### 常见 lake 问题

| 症状 | 解法 |
|------|------|
| `lake build` 卡在编译 mathlib 几小时 | 忘了 `lake exe cache get`；先跑它 |
| `lake update` 后 `lakefile.lock` 冲突 | 协作时别随意 commit lock；按团队约定 |
| `elan` 找不到 / 命令行无 `lean` | 重装 elan，确认 `~/.elan/bin` 在 `PATH` |
| 切换 mathlib 版本后报错一片 | `lake update` + `lake exe cache get` 重新对齐 |

---

⬅️ [附录 A　常用策略速查表](appendix-a-tactics-cheatsheet.md) ｜ ➡️ [附录 C　术语表](appendix-c-glossary.md)