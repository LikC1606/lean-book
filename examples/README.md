# Lean 4 漫游指南 · 配套示例

不依赖 mathlib 的 Lake 项目，对应书中多章可运行代码。

## 构建

```bash
cd examples
lake build
lake exe examples
```

需要本机已安装 [elan](https://lean-lang.org/install/)（与书第 2 章一致）。`lean-toolchain` 已固定版本。

## 模块对照

| 模块 | 书中章节 |
|------|----------|
| `Examples.Ch03` | 第 3 章 上手 |
| `Examples.Ch04` | 第 4 章 表达式求值器 |
| `Examples.Ch08` | 第 8 章 命题即类型 |
| `Examples.Ch09Add` | 第 9 章 `zero_add` / `add_comm` / `add_assoc` 长证明 |
| `Examples.Ch14` | 第 14 章 `myAdd` / 转账 / `Vec` |
| `Examples.Ch14Sort` | 第 14 章 **插入排序完整证明**（有序 + count） |
| `Examples.Ch15` | 第 15 章 deny 优先策略 |
| `Examples.Ch22` | 第 22 章 编译器正确性 |

CI：仓库根目录 `.github/workflows/examples.yml` 在 `examples/**` 变更时自动 `lake build`。

## 注意

- 以本目录能 `lake build` 的代码为准；书中 Markdown 为教学讲解，个别策略写法可能随版本微调。
- 需要 mathlib 的章节（11–13、部分 16）请按书中 `lake new … math` 自建项目，不放在此包内以免缓存体积过大。
