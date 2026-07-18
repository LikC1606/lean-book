# 第 16 章　密码学与区块链：验证零知识证明

> 本章目标：了解 Lean 在密码学（尤其是零知识证明/SNARK）验证中的角色，认识 ArkLib 项目，并动手形式化一个微型密码协议。

## 16.1 为什么密码学特别需要形式化？

密码学的正确性论证有独特的"毒性"：

1. **概率推理**：安全性定义本身带概率（"攻击者成功的概率可忽略"）——人类审稿极易漏掉边界情形；
2. **微妙的安全性**：一个协议可以功能完全正确、测试全过，同时**安全性证明有个洞**；
3. **代价极端**：零知识证明系统保护的是真金白银（区块链资产），一个 soundness bug 就是印钞机后门。

2010 年代，多个已发表（甚至已标准化）的密码协议被发现证明有误。形式化验证由此成为密码学界的新共识：**论文证明 + 机器检查证明，双保险。**

## 16.2 ArkLib：为 SNARK 建造形式化地基

### SNARK 是什么（60 秒版）

**SNARK**（Succinct Non-interactive Argument of Knowledge，简洁非交互式知识论证）是一种密码协议：

> 证明者可以让验证者相信"我知道某个秘密，使得某个性质成立"——**不泄露秘密本身**，且证明很短、验证很快。

应用遍地都是：zkRollup（以太坊扩容）、隐私交易（Zcash）、可验证计算……

### ArkLib 的使命

**ArkLib**（以太坊基金会资助）是一个 Lean 库生态系统，目标是：

- 把 SNARK 的核心构造（多项式承诺、FRI、求和检查协议 sum-check……）在 Lean 中**机械化**；
- 把这些协议微妙的**概率安全证明**（soundness、zero-knowledge）变成机器检查过的定理；
- 提供**可执行的参考实现**，供 zk 工程师对照。

其意义：目前 SNARK 的安全论证散落在论文里，风格各异、密度极高、细节常有缝隙。ArkLib 把它们统一到 Lean 的严格框架下——**一处形式化，处处可复用**。

### 技术看点（写给好奇者）

- 概率推理建立在 mathlib 的测度论/概率论之上（`PMF`：概率质量函数）；
- 交互式预言机证明（IOP）等新模型需要扩展传统的游戏化安全定义；
- 大量代数结构（有限域、多项式环、椭圆曲线）直接复用 mathlib——再次体现"数学库是所有应用的地基"。

## 16.3 动手：形式化一个微型承诺协议

理论再多不如动手。我们来形式化**密码协议分析的核心套路**：定义协议 → 陈述安全性质 → 证明。用一个玩具版"承诺方案"（commitment scheme）演示结构（真实系统用的是椭圆曲线/哈希，这里用加法模运算示意）。

```lean
import Mathlib

/-!
## 玩具承诺方案

承诺（commitment）协议分两步：
1. 承诺方把秘密 v 和随机数 r 混合，公布承诺值 C；
2. 之后揭示 (v, r)，验证方重算 C 核对。

两条安全性质：
- 隐藏性（hiding）：看 C 推不出 v；
- 绑定性（binding）：承诺方无法事后改口（找到另一对 (v', r') 同样匹配）。
-/

/-- 系统参数：模数 q -/
variable (q : ℕ) [NeZero q]

/-- 承诺值：C = (v + r) mod q —— 玩具版（无安全性，仅演示形式化结构） -/
def commit (v r : ZMod q) : ZMod q := v + r

/-- 验证：重算并比对 -/
def verify (C v r : ZMod q) : Bool := commit q v r == C
```

### 性质一：正确性（诚实参与者总能通过验证）

```lean
theorem verify_correct (v r : ZMod q) : verify q (commit q v r) v r = true := by
  simp [verify, commit]
```

### 性质二：绑定性（玩具版）—— 固定 r 时无法改口

```lean
/-- 若 (v, r) 和 (v', r) 对应同一承诺，则 v = v'。
    即：在相同随机数下，秘密被绑定。 -/
theorem binding (v v' r : ZMod q)
    (h : commit q v r = commit q v' r) : v = v' := by
  simp [commit] at h
  exact add_right_cancel h
```

（`add_right_cancel`：从 `v + r = v' + r` 消去 `r`。）

### 性质三：隐藏性的"理想形式"——r 均匀随机时 C 不泄露 v

这条值得细看，因为它展示了**概率安全如何形式化**：对任意两个秘密 v₀、v₁，当 r 在 ZMod q 上均匀采样时，commit 的分布**完全相同**。

```lean
/-- v + Uniform 与 Uniform 同分布（ZMod 上加法是双射）——
    信息论意义下 C 不含 v 的任何信息。 -/
theorem hiding (v : ZMod q) :
    (PMF.uniformOfFintype (ZMod q)).map (· + v)
      = PMF.uniformOfFintype (ZMod q) := by
  -- 有限群上"平移均匀分布仍是均匀分布"，mathlib 有现成引理
  ext x
  simp [PMF.map_apply, PMF.uniformOfFintype_apply]
  -- 核心：{r | r + v = x} 的基数与 v 无关（恰好 1）
  sorry  -- 留作练习：用 Finset.card 与加法的双射性完成
```

这个玩具例子的骨架与真实密码协议的形式化**完全同构**：真实系统把 `ZMod q` 换成椭圆曲线群，把加法换成 Pedersen 承诺 `g^v · h^r`，把"加法双射"换成更复杂的 hardness 假设——但"定义协议 → 陈述性质 → 机器检查证明"的范式一字不改。

## 16.4 区块链上的 Lean：智能合约验证

区块链是形式化验证的天然市场（不可篡改 + 掌管资产 = bug 代价无穷大）。Lean 生态在这块的布局：

- **ArkLib**：如上，zk 基础设施的验证；
- **Veil**（第 15 章）：共识协议验证；
- **Nethermind 等公司**：用 Lean 验证以太坊相关组件（如验证 RISC-V zkVM 电路的 Lean 形式化项目）；
- 学术项目：EVM 语义、Gas 机制的形式化模型。

趋势判断：随着 zk 技术成为区块链扩容主流路线，**"电路/证明系统的形式化验证"会从加分项变成必选项**——而 Lean 是目前少数能同时承载代数、概率和程序推理的工具。

## 16.5 密码学形式化的方法论要点

1. **区分功能正确性与安全性**：前者是"输入输出对"，后者是"对任意攻击者，成功概率 ≤ 可忽略量"——后者才是密码学的灵魂，也最难；
2. **游戏化定义**（game-based security）：把安全性质写成"挑战者 vs 攻击者"的游戏，然后证明攻击者胜率的上界。Lean 的依赖类型很适合精确表达"攻击者不知道秘密"这类信息论约束；
3. **从教科书协议练手**：Schnorr 协议、Sigma 协议、Fiat-Shamir 变换——ArkLib 都在做，读它的代码是最好的学习路径；
4. **mathlib 的抽象代数是你的朋友**：有限域（`ZMod p`、`GaloisField`）、多项式（`Polynomial`）、群论，全部现成。

## 16.6 本章小结

- 密码学安全证明微妙且代价极端，形式化是行业新共识；
- **ArkLib**（以太坊基金会支持）正在 Lean 中机械化 SNARK 的安全证明，为 zk 生态提供机器检查过的规范与参考实现；
- 动手部分：用 `ZMod q` 形式化了玩具承诺方案的正确性、绑定性、隐藏性——骨架与真实协议验证同构；
- 区块链（共识、zkVM、智能合约）是 Lean 验证快速增长的阵地。

## 练习

1. 完成 16.3 中 `hiding` 定理的 `sorry`（提示：`Finset.card_eq_one`、`ZMod` 上加法双射 `Equiv.addRight`）；
2. 给玩具协议加"揭示阶段"：定义 `open` 函数并证明 `verify q C v r = true ↔ C = commit q v r`；
3. 形式化一个更贴近现实的协议：**Schnorr 身份协议**的功能正确性（给定群生成元 g，秘密 x，公开 h = g^x；协议三步后验证等式 g^s = R · h^c 成立）——用 mathlib 的 `Group`/`ZMod` 表达；
4. （调研）浏览 ArkLib 仓库，找到 sum-check 协议的定理陈述，数一数它的安全定理依赖了 mathlib 的哪些代数模块。

## 延伸阅读

- ArkLib 仓库与文档（GitHub: argumentcomputer/ArkLib……搜索 "ArkLib Lean"）；
- 官网 Use Case 专文：*ArkLib: Formally Verified Arguments of Knowledge in Lean*；
- 入门读物：*A Graduate Course in Applied Cryptography*（Boneh & Shoup，免费）——配合 Lean 形式化食用极佳。

---

⬅️ [第 15 章](15-industry-verification.md) ｜ ➡️ 下一章：[第 17 章　语法扩展与宏：改造 Lean 本身](17-macros.md)
