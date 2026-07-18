# 第 16 章　密码学与区块链：验证零知识证明

> 本章目标：了解 Lean 在密码学（尤其 SNARK）验证中的角色，认识 ArkLib，并动手形式化微型承诺协议。学完后你能陈述正确性/绑定性/隐藏性，并完成玩具协议的部分证明。

## 本章你会做出什么

1. 说明为何密码学特别需要机器检查证明；
2. 知道 ArkLib 在做什么；
3. 实现玩具 `commit`/`verify` 并证正确性与绑定性；
4. 理解隐藏性如何连到概率（`PMF`）叙事。

---

## 16.1 为什么密码学特别吃形式化？

1. **概率安全**：定义带「可忽略概率」——人审易漏边界；
2. **功能对 ≠ 安全对**：测试全过仍可能 soundness 有洞；
3. **代价极端**：zk/链上资产，一个洞 = 印钞后门。

行业新共识：**论文证明 + 机器检查** 双保险。

---

## 16.2 ArkLib：SNARK 的形式化地基

### SNARK 60 秒

证明者让验证者相信「我知道某秘密使性质成立」——**不泄露秘密**，证明短、验证快。应用：zkRollup、隐私交易、可验证计算。

### ArkLib 使命

- 机械化多项式承诺、FRI、sum-check 等；
- 把 soundness / ZK 等概率论证变成定理；
- 提供可执行参考实现。

技术看点：mathlib 概率/代数；IOP 等模型；有限域与多项式复用 mathlib。

---

## 16.3 动手：玩具承诺协议

```lean
import Mathlib

variable (q : ℕ) [NeZero q]

/-- 玩具：C = v + r （无真实安全性，只演示结构） -/
def commit (v r : ZMod q) : ZMod q := v + r

def verify (C v r : ZMod q) : Bool := decide (commit q v r = C)
```

### 正确性

```lean
theorem verify_correct (v r : ZMod q) :
    verify q (commit q v r) v r = true := by
  simp [verify, commit]
```

### 绑定性（固定 r 不可改口）

```lean
theorem binding (v v' r : ZMod q)
    (h : commit q v r = commit q v' r) : v = v' := by
  simpa [commit] using add_right_cancel h
```

### 隐藏性（信息论版叙事）

当 r 均匀随机，`v + r` 的分布与 v 无关（加法是双射）：

```lean
theorem hiding_sketch (v : ZMod q) :
    (PMF.uniformOfFintype (ZMod q)).map (fun r => r + v)
      = PMF.uniformOfFintype (ZMod q) := by
  -- 练习：用加法双射 / 现成均匀分布引理完成
  sorry
```

骨架与真实协议**同构**：把 `ZMod` 换成椭圆曲线群、加法换成 Pedersen `g^v h^r`、双射换成 hardness 假设——范式不变：

```
定义协议 → 陈述性质 → 机器检查证明
```

---

## 16.4 区块链上的 Lean

| 方向 | 角色 |
|------|------|
| ArkLib | zk 基础设施 |
| Veil | 共识协议 |
| 生态项目 | EVM/zkVM/电路相关形式化 |
| 智能合约 | 高代价逻辑的模型+规格 |

趋势：zk 成扩容主流后，**电路/证明系统验证从加分变必选**；Lean 同时扛代数、概率、程序。

---

## 16.5 方法论要点

1. **功能正确 vs 安全**：后者是攻击者优势界；
2. **游戏化定义**：挑战者 vs 攻击者；
3. **从教科书协议练手**：Schnorr、Sigma、Fiat–Shamir；
4. **mathlib 是朋友**：`ZMod`、`Polynomial`、群论。

### 安全性质检查清单（玩具→真实）

| 性质 | 玩具版 | 真实版常要 |
|------|--------|------------|
| Correctness | verify∘commit = ok | 同左 |
| Binding | 固定 r 唯一 v | 计算绑定性（硬度） |
| Hiding | 均匀 + 双射 | 计算隐藏 / 语义安全 |

---

## 16.6 迷你扩展：揭示接口

```lean
def openCommit (C v r : ZMod q) : Bool := verify q C v r

theorem open_iff (C v r : ZMod q) :
    openCommit q C v r = true ↔ C = commit q v r := by
  simp [openCommit, verify, commit]
```

---

## 16.7 踩坑对照

| 症状 | 处理 |
|------|------|
| 以为玩具 commit 可上线 | 仅教学；无哈希/曲线 |
| `PMF` API 版本差 | 查当前 mathlib Probability |
| `ZMod 0` | 需要 `NeZero q` |
| 安全证明全 sorry | 至少正确性+绑定先清零 |

---

## 16.8 本章小结

- 密码安全微妙、代价高 → 形式化成共识；
- ArkLib 机械化 SNARK 论证；
- 玩具承诺：正确性、绑定、隐藏骨架；
- 链上/zk 是快速增长阵地。

---

## 练习

### ⭐ 基础

1. 对 `q = 17` `#eval` 几组 commit/verify。
2. 证 `open_iff`。

### ⭐⭐ 进阶

3. 完成 `hiding_sketch` 的 `sorry`。
4. 增加「错误密钥」反例：不同 `(v,r)` 映射到同 C 是否可能？在玩具加法下讨论。

### ⭐⭐⭐ 硬核

5. Schnorr 功能正确性草图（`g^s = R * h^c`）。
6. 浏览 ArkLib，列出 sum-check 依赖的 3 个 mathlib 模块。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| ArkLib 仓库 / 官网 Use Case | 主线 |
| Boneh–Shoup 应用密码学讲义 | 理论 |
| 第 12、13 章 | 代数与概率后台 |

---

⬅️ [第 15 章](15-industry-verification.md) ｜ ➡️ 下一章：[第 17 章　语法扩展与宏：改造 Lean 本身](17-macros.md)
