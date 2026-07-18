# 第 2 章　安装与环境配置

> 本章目标：在你的电脑上装好 Lean 4 开发环境，并跑通第一个程序。我们会把"装好"这件事一次做到位，后面 20 章都不用再为环境分心。

安装 Lean 4 其实只需要记住一个名字：**elan**。它是 Lean 的工具链管理器（类似 Rust 的 rustup、Python 的 pyenv），负责安装和切换 Lean 版本。配合编辑器插件（VS Code 为主）和构建工具 **Lake**，三者构成 Lean 的"开发铁三角"：

```
elan   —— 管 Lean 版本（装哪个版本、切哪个版本）
Lake   —— 管项目（依赖、构建目标、可执行入口）
插件   —— 管交互（实时检查、Infoview、跳转）
```

下面一步一步来。

## 2.1 前置依赖

Lean 4 本身是自包含的，但它的工具链依赖一些系统组件。装 elan 之前，请确认你的系统有：

- **Git**（拉取依赖项目，mathlib 等都托管在 GitHub）；
- **curl**（macOS/Linux）或 **PowerShell**（Windows）用来跑安装脚本；
- 一个能用的**终端**；
- 一个**文本编辑器**（我们用 VS Code）；
- 足够的磁盘空间：装一个带 mathlib 的项目，加预编译缓存，大约要 2–3 GB。

各系统补齐这些工具的方式：

- **macOS**：装好 Xcode Command Line Tools 即可（`xcode-select --install`），里面带 git 和 curl。
- **Ubuntu/Debian**：`sudo apt update && sudo apt install git curl build-essential`。
- **Arch/Fedora**：用各自的包管理器装 `git curl` 即可。
- **Windows**：装 [Git for Windows](https://git-scm.com/download/win)，它会顺带装好 Git Bash——一个能在 Windows 上跑类 Unix 命令的终端，本书命令在 Git Bash 里都能用。

> 💡 **国内用户**：GitHub 拉取 mathlib 可能较慢甚至失败。可提前配置 git 代理（`git config --global http.proxy ...`），或参考 Lean Zulip 中文频道里的镜像方案。先装好 elan 与插件，mathlib 的事第 11 章再操心也不迟。

## 2.2 安装 elan 和 Lean 4

### macOS / Linux

打开终端，运行：

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

按提示回车确认即可。安装脚本会：

1. 下载 elan 二进制；
2. 把 `~/.elan/bin` 加进你的 `PATH`（自动改 `~/.profile` 或 `~/.bashrc`/`~/.zshrc`）；
3. 安装一个默认的 Lean 4 稳定版。

安装完成后，重新打开终端（或执行 `source ~/.profile`），验证：

```bash
$ elan --version
elan 4.x.x
$ lean --version
Lean (version 4.x.x, ...)
```

能看到版本号就说明 Lean 4 已经能用了。

### Windows

方式一（推荐）：用 winget：

```powershell
winget install elan
```

方式二：下载 [elan-init.exe](https://elan.lean-lang.org/elan-init.exe) 双击运行。

Windows 上建议配合 **Git Bash** 或 **PowerShell** 使用。命令行示例和 macOS/Linux 基本一致；个别命令（如 `code` 打开 VS Code）需确保 VS Code 已加入 PATH（安装时勾选"添加到 PATH"即可）。

### 想完全免安装？

有两个选择：

- **Lean 4 Web Playground**：[live.lean-lang.org](https://live.lean-lang.org/)，浏览器里直接写 Lean，适合快速试验或尝鲜；
- **Gitpod / GitHub Codespaces**：把 Lean 项目托管到云端开发环境，免去本地配置。

不过本地环境的响应速度和插件体验最好，建议还是装一个。后面所有章节默认你在本地环境里操作。

## 2.3 安装 VS Code 插件

Lean 4 的官方 IDE 是 **VS Code**（也有 Neovim、Emacs 插件，本书以 VS Code 为准）。

1. 安装 [VS Code](https://code.visualstudio.com/)；
2. 打开扩展市场，搜索 `lean4`，安装官方插件（发布者是 **leanprover**，图标是 ∀ 符号）；
3. 安装完成后，用 VS Code 打开任意 `.lean` 文件，插件会自动激活。

### 你会得到什么？

Lean 的 VS Code 插件体验在定理证明器中是顶尖的：

- **Infoview（信息视图）**：右侧一个面板，实时显示光标处的证明状态（goal）、变量类型、错误信息——这是交互式证明的核心窗口；
- **语义高亮**：变量、定义、假设会用不同颜色区分；
- **悬停查看**：鼠标悬停在任何符号上能看到它的类型和文档；
- **跳转定义**：Ctrl/Cmd + 点击跳到定义处；
- **实时编译**：边写边检查，错误立刻标红。

> 💡 **小技巧**：在 VS Code 里输入 `\a` 会弹出 Unicode 输入，`\a` + 空格得到 `α`，`\to` 得到 `→`，`\and` 得到 `∧`。Lean 代码大量使用数学符号，这套缩写系统（和 LaTeX 一致）会让输入如飞。本书附录 A 有常用符号速查。

### Infoview 详解

Infoview 是写 Lean 证明时盯得最多的面板。理解它能显示什么，会极大提升你的效率：

- **Tactic state（策略状态）**：当前还需要证明的目标（goal），形如 `⊢ n + 0 = n`；上方列出当前可用的假设（context），形如 `n : Nat`、`ih : 0 + k = k`；
- **All goals / Current goal 切换**：当一个证明产生多个子目标时，可以切换查看每一个；
- **Expected type**：光标放在表达式上时，显示它应具有的类型，帮你判断"这里到底缺什么"；
- **Term mode vs Tactic mode**：在 `by` 之后是策略模式（看 goal），在普通表达式里是项模式（看类型）。

写证明时养成习惯：**改一行，看一眼 Infoview**——它就是你证明的"仪表盘"。第 9 章会更系统地讲怎么读它。

### 备选编辑器

如果你不用 VS Code：

- **Neovim**：社区有 [`lean.nvim`](https://github.com/Julian/lean.nvim)，支持 Infoview、跳转、LSP；
- **Emacs**：`lean4-mode`，老牌定理证明社区的首选；
- **JetBrains（IntelliJ/PyCharm 等）**：有第三方 Lean 插件，但体验不如官方 VS Code 插件完整，不推荐作为主力。

初学强烈建议先用 VS Code——它是目前打磨得最好的，本书截图与操作都基于它。

## 2.4 创建你的第一个 Lean 项目

Lean 自带的构建工具叫 **Lake**（"湖"，Lean + Make）。创建一个新项目：

```bash
lake new hello
cd hello
```

项目结构长这样：

```
hello/
├── Hello.lean        # 库的入口（自动 import 所有子模块）
├── Hello/
│   └── Basic.lean    # 库的实际代码
├── Main.lean         # 可执行程序入口
├── lakefile.toml     # 项目配置（依赖、构建目标）
├── lean-toolchain    # 指定 Lean 版本
├── lake-manifest.json # 依赖的精确版本（lake update 后生成）
└── .gitignore
```

看一眼 `Main.lean`：

```lean
import Hello

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

构建并运行：

```bash
lake build
lake exe hello
# 输出: Hello, world!
```

恭喜，你的第一个 Lean 程序跑起来了！

### lakefile.toml 逐项解剖

打开 `lakefile.toml`，你会看到类似这样的内容：

```toml
name = "hello"
version = "0.1.0"

[[lean_lib]]
name = "Hello"

[[lean_exe]]
name = "hello"
root = "Main"
```

- `name`：项目名，也是 Lake 命令里引用它用的名字；
- `version`：语义化版本号；
- `[[lean_lib]]`：声明一个库目标。`name = "Hello"` 表示这个库的根模块是 `Hello.lean`，其下 `Hello/` 目录里的文件都归它；
- `[[lean_exe]]`：声明一个可执行目标。`root = "Main"` 表示从 `Main.lean` 的 `main` 函数开始编译。

加依赖时，在这个文件里加 `[require]` 段（见 2.6 节）。Lake 用 TOML 而非 YAML，是为了让配置可被精确解析、不易出错。

### lean-toolchain 与版本管理

`lean-toolchain` 是一个只有一行的文件，内容形如 `leanprover/lean4:v4.x.x`。它告诉 elan："这个项目用这个版本的 Lean"。当你 `cd` 进一个带 `lean-toolchain` 的目录运行 `lean`/`lake` 时，elan 会**自动切换**到对应版本——你完全不用手动管理版本切换，这正是 elan 的核心价值。

### 关键命令速查

| 命令 | 作用 |
|------|------|
| `lake new <名字>` | 创建新项目 |
| `lake build` | 构建项目 |
| `lake exe <名字>` | 运行可执行目标 |
| `lake update` | 更新依赖、重生成 manifest |
| `lake clean` | 清理构建产物 |
| `elan default leanprover/lean4:stable` | 设置全局默认工具链为稳定版 |
| `elan show` | 查看当前目录生效的工具链 |
| `elan toolchain list` | 列出已装工具链 |
| `elan install <版本>` | 安装指定版本 |

## 2.5 单文件模式：最快的试验方式

学习阶段我们大多数时候不需要建项目——直接创建一个 `.lean` 文件就行：

```bash
mkdir lean-playground && cd lean-playground
touch test.lean
code test.lean   # 用 VS Code 打开
```

写入：

```lean
def double (n : Nat) : Nat := 2 * n

#eval double 21
-- 输出: 42
```

`#eval` 是 Lean 的"求值命令"：保存文件后，VS Code 的信息视图（或终端 `lean test.lean`）就会显示结果 `42`。

> ⚠️ **注意**：没有项目时，只能使用 Lean 标准库。要用 mathlib 等大型库必须建项目并添加依赖（见 2.6 节和第 11 章）。单文件模式适合第 3–10 章绝大部分练习。

为了让单文件也能"记住"用哪个 Lean 版本，你可以在该目录放一个 `lean-toolchain` 文件，内容写 `leanprover/lean4:stable`。这样 elan 进目录会自动选稳定版，避免不同示例互相干扰。

## 2.6 依赖 mathlib 的项目

本书第四部分开始会用到数学库 mathlib。提前了解一下如何配置（到时候再照做也不迟）：

方式一：用 mathlib 提供的模板建项目（推荐）：

```bash
lake new my_project math
```

这会生成一个已经配好 mathlib 依赖、带缓存配置的项目骨架。

方式二：手动在 `lakefile.toml` 中添加依赖：

```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "master"
```

然后：

```bash
lake update                # 拉取 mathlib 到 lake-packages/
lake exe cache get         # 下载预编译缓存（强烈建议！）
lake build                 # 构建
```

> 💡 mathlib 很大（上百万行），但它有完善的**预编译缓存机制**（`lake exe cache get`），正常使用只需下载缓存而不必本地编译。如果你跳过 `cache get` 直接 `lake build`，本地编译可能要数小时甚至更久——这是新手最常踩的坑。具体细节我们在第 11 章展开。

第一次 `lake exe cache get` 会下载几百 MB 到 1 GB+ 的缓存（取决于 mathlib 版本），请耐心等待。后续增量更新会快得多。

## 2.7 多文件项目结构

当你的代码变多，单文件就不够用了。Lean 的模块系统按**目录结构**对应**命名空间**：

```
MyProj/
├── MyProj.lean            # 模块 MyProj，可 import MyProj.Basic
├── MyProj/
│   ├── Basic.lean         # 模块 MyProj.Basic
│   ├── Data/
│   │   ├── List.lean      # 模块 MyProj.Data.List
│   │   └── Tree.lean      # 模块 MyProj.Data.Tree
│   └── Proof/
│       └── Lemmas.lean    # 模块 MyProj.Proof.Lemmas
```

在 `Basic.lean` 里要使用 `Tree`，写：

```lean
import MyProj.Data.Tree
```

模块名与文件路径**严格对应**——这是 Lean 的约定，省去了显式声明文件归属的麻烦。

## 2.8 容器与 CI

有些场景你想用容器化或自动化方式跑 Lean：

- **Docker**：社区维护了带 elan 的镜像，例如 `ghcr.io/leanprover/lean4:stable`。在 CI 里跑测试、或在隔离环境里编译 mathlib 都很方便：
  ```bash
  docker run --rm -v "$PWD":/work -w /work ghcr.io/leanprover/lean4:stable lake build
  ```
- **GitHub Actions**：mathlib 等项目用 [`lean-action`](https://github.com/leanprover/lean-action) 一行配置即可在 CI 里构建、测试、缓存：
  ```yaml
  - uses: leanprover/lean-action@v1
  ```
- **预编译缓存 in CI**：`lean-action` 默认会尝试拉取 mathlib 缓存，避免 CI 跑几小时。

即便你暂时用不到这些，知道它们存在也很有用——等你做自己的项目、想加自动测试时，直接照搬即可。

## 2.9 常见问题（FAQ）

**Q1：`lake build` 报错找不到 toolchain？**
检查 `lean-toolchain` 文件里的版本是否已安装：`elan toolchain list`。缺的话 `elan install <版本>`。最稳的做法是写 `leanprover/lean4:stable` 让 elan 自己选当前稳定版。

**Q2：VS Code 插件没有反应？**
确保你用 VS Code 打开的是**文件夹**（File → Open Folder），而不是单个文件——Lean 插件需要在项目根目录下工作。另外看看 Output 面板中 "Lean: Editor" 频道有无报错，常见原因是 elan 不在 VS Code 进程的 PATH 里（重启 VS Code 或在设置里指定 elan 路径）。

**Q3：Windows 上杀毒软件报警？**
elan 是知名开源工具，属于误报，添加信任即可。如仍不放心，可对照 [elan GitHub 仓库](https://github.com/leanprover/elan) 自行核对来源。

**Q4：公司网络拉不动 GitHub 上的 mathlib？**
配置 git 代理，或使用社区提供的国内镜像（Zulip 中文频道有讨论）。也可以先只学不依赖 mathlib 的部分（第 3–10 章），等网络条件具备再装 mathlib。

**Q5：如何升级 Lean？**
`elan update` 升级 elan 本身；改 `lean-toolchain` 文件指定项目用的 Lean 版本，下次 `lake build` 时 elan 会自动装上并切换。

**Q6：`lake exe cache get` 卡住或失败？**
多半是网络问题。可以加 `--verbose` 看进度，或重试几次。完全离线时只能 `lake build` 本地编译 mathlib（耗时数小时）。

**Q7：多个项目想共享同一份 mathlib 编译产物？**
Lake 目前按项目隔离 `lake-packages/`。可以用符号链接或自定义缓存路径，但最省心的方式仍是每个项目各跑一次 `cache get`——缓存下载比本地编译便宜得多。

**Q8：装完之后 Lean 报一堆 mathlib 相关错误，但我不想用 mathlib？**
确认你的 `lakefile.toml` 里没有 `[require] mathlib` 段；单文件模式默认不引入 mathlib，除非你 `import Mathlib`。

## 2.10 本章小结

- **elan** 管版本，**Lake** 管构建，**VS Code 插件**管交互——三者各司其职；
- 日常试验用单文件 + `#eval` 最快；做正经项目用 `lake new`；
- 用 mathlib 的项目记得 `lake exe cache get` 拿预编译缓存，否则本地编译几小时起步；
- 模块名严格对应目录路径；多文件项目靠 `import` 串起来；
- 遇到问题先看 Infoview 和 Output 面板，再去 Zulip 提问。

## 练习

1. ⭐ 装好环境后，创建一个单文件，写函数 `square (n : Nat) : Nat := n * n`，用 `#eval square 12` 验证输出 `144`；
2. ⭐ 用 `lake new` 建一个项目，修改 `Main.lean` 让它打印你的名字，构建运行；
3. ⭐ 在 VS Code 里练习 Unicode 输入：打出 `∀ x : Nat, x + 0 = x` 这行代码（提示：`\forall`、`\:`、`\to`）；
4. ⭐⭐ 打开你创建项目的 `lakefile.toml`，尝试再声明一个 `[[lean_lib]]`，名字自定，在对应目录建一个 `.lean` 文件写个函数，从 `Main.lean` 里 `import` 并 `#eval` 调用它；
5. ⭐⭐ （可选）配置一个带 mathlib 依赖的项目并成功 `lake exe cache get`，记录耗时，为第 11 章做准备。

## 延伸阅读

- Lean 官方安装指南：lean-lang.org → Install；
- VS Code 插件手册：lean-lang.org → "Lean 4 VS Code Extension Manual"；
- [`lean-action`](https://github.com/leanprover/lean-action) 文档（CI 用）；
- [elan 仓库](https://github.com/leanprover/elan)（工具链管理细节）。

---

⬅️ [第 1 章](01-introduction.md) ｜ ➡️ 下一章：[第 3 章　三十分钟上手 Lean 4](03-first-steps.md)