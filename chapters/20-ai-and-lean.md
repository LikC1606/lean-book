# 第 20 章　AI 与 Lean：自动定理证明的新时代

> 本章目标：理解为何 AI 数学革命选择 Lean 作「裁判」，认识 LeanDojo、AlphaProof 等标杆，并掌握今天就能用的 AI 辅助工作流。

## 本章你会做出什么

1. 画出「生成器 + 验证器」闭环；
2. 区分 LeanDojo / REPL / Pantograph 的角色；
3. 跑通 LLM + Lean 报错迭代；
4. 用 LeanSearch / Loogle 完成一次真实搜引理。

---

## 20.1 天作之合：AI 出主意，Lean 当裁判

大模型弱点：**幻觉**——错误证明也能写得很优雅。

Lean 的答案：

> **AI 提出候选，Lean 内核裁决。** 不疲劳、不受贿、不看作者名声。

```
┌──────────┐  候选证明  ┌──────────┐  通过/拒绝  ┌────────┐
│  AI 模型  │ ────────▶ │ Lean 内核 │ ─────────▶ │ 反馈    │
└──────────┘            └──────────┘            └────────┘
     ▲                                                │
     └──────── 强化学习 / 搜索 / 重试 ◀───────────────┘
```

优势：

1. **完美奖励信号**——对错由内核判定，无需人工标注；
2. **输出可验证**——过内核的证明对陈述本身 100% 可信；
3. **难度可扩展**——中学代数到前沿引理，同一裁判。

---

## 20.2 标杆系统

### AlphaProof（DeepMind，2024）

IMO 银牌水平（与 AlphaGeometry 2 合作）。自然语言题 → Lean 陈述 → AlphaZero 式搜索，Lean 逐步反馈。DeepMind 强调：选 Lean 因**可扩展与可验证**。

### LeanDojo（Caltech 等）

机器学习访问 Lean 的基础设施：

- 从 mathlib 等抽取状态 / 前提 / 策略轨迹；
- Gym 式环境：动作 = 策略，观测 = 新状态；
- ReProver：检索增强证明。

做 AI4Math 研究几乎默认从这里起步。

### REPL / Pantograph

| 工具 | 角色 |
|------|------|
| Lean REPL | 策略进、状态 JSON 出；多数 LLM 自动证明实验依赖它 |
| Pantograph | 更底层：构表达式、查符号，服务 MCTS 等 |

### 其他玩家

- Harmonic / Aristotle：数学超级智能，Lean 作底座；
- AlphaProof Nexus 等开放能力；
- 开源：Goedel-Prover、DeepSeek-Prover、Kimina-Prover… 月级刷新。

---

## 20.3 今天就能用的工作流

### 工具一：数学搜索引擎

- **LeanSearch / Moogle**：自然语言；
- **Loogle**：类型模式；
- **LeanExplore**：语义声明搜索。

### 工具二：LLM + 验证闭环（最实用）

1. 写好 `theorem ... := by sorry`；
2. 让 LLM 生成候选（允许错）；
3. **贴回 VS Code，Lean 检查**；
4. 把报错 + Infoview 目标喂回 LLM；
5. 迭代至 **No goals**；
6. `#print axioms` 确认无 `sorryAx`。

**铁律：AI 每句话都要过 Lean 才算数。**

### 工具三：符号自动化也是「AI」

`grind`、`omega`、`aesop`、`exact?` = 符号 AI。与神经网络互补 → **neuro-symbolic** 方向。

### 推荐提示词模板

```
你是 Lean 4 助手。只输出可粘贴的 Lean 代码。
当前目标：
... 粘贴 Infoview ...
已有假设：...
刚才报错：...
请给出下一步策略（尽量短），不要编造不存在的引理名；
若不确定引理，写 exact? 或给出 Loogle 查询模式。
```

---

## 20.4 为何 Lean 特别适合 AI

1. **策略即程序**——动作空间结构化；
2. **状态完全可见**——目标 + 上下文可序列化；
3. **mathlib 语料**——百万行已验证推理；
4. **API 开放**——元编程接口人类能用机器也能用；
5. **自举**——工具链本身是 Lean，可被改进。

---

## 20.5 冷静剂

- 竞赛题 / 教科书进展快；**前沿拆引理**仍大量靠人；
- **陈述形式化**仍是瓶颈——证错命题等于白证；
- AI 像结对伙伴：加速查引理、补样板；**架构与抽象**仍属人。

> **懂 Lean 的人 + AI = 超级个体。** AI 不取代你，会用 AI 的会取代不会用的。

---

## 20.6 迷你实验清单（30–60 分钟）

| 步骤 | 动作 |
|------|------|
| 1 | LeanSearch：「composite of continuous is continuous」 |
| 2 | 对 `∀ n, 2 ∣ n*(n+1)` 让 LLM 写证明，数错误次数 |
| 3 | 故意喂错误策略，看你如何把报错整理回提示词 |
| 4 | 对比 `exact?` 与 LLM 建议是否一致 |

---

## 20.7 本章小结

- 范式：生成 + 验证；
- 标杆：AlphaProof、LeanDojo、REPL/Pantograph；
- 实用：搜索引擎 + LLM 闭环 + 符号策略；
- 未来：人机混合；你在学站在机器肩膀上的姿势。

---

## 练习

### ⭐ 基础

1. LeanSearch 找「连续复合」真实定理名。
2. 让 LLM 证 `n + 0 = n`，记录是否一次过。

### ⭐⭐ 进阶

3. 报错循环完成 `∀ n, 2 ∣ n * (n + 1)`。
4. 同一题禁止 LLM 用 `omega`，看它如何归纳。

### ⭐⭐⭐ 硬核

5. 读 LeanDojo 摘要：前提检索解决什么问题？
6. 调研 REPL 一次交互的 JSON 字段含义（文档或仓库）。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| LeanDojo 论文（NeurIPS 2023） | 数据与检索 |
| AlphaProof 博客 | 系统故事 |
| lean-lang.org Tools | REPL / Pantograph / LeanSearch |

---

⬅️ [第 19 章](19-dsl.md) ｜ ➡️ 下一章：[第 21 章　教育、科研与更多领域](21-education-research.md)
