# 第 15 章　工业级案例：AWS、Rust 与分布式协议

> 本章目标：了解 Lean 在工业界的三个标杆——Cedar、Aeneas、Veil，并把「验证驱动开发」落成你能抄的流程。学完后你能写一个玩具权限系统并证明 deny 优先，能向同事讲清对拍与翻译验证。

上一章是方法论；本章看**真金白银**问题怎么解。

## 本章你会做出什么

1. 画出 Cedar 的「Lean 模型 + 证明 + Rust 对拍」图；
2. 一句话解释 Aeneas 为何能「不谈内存」；
3. 理解 Veil 的多模态验证；
4. 亲手完成迷你权限策略的 deny 优先证明。

---

## 15.1 Cedar：AWS 授权大门

### 问题

**Cedar** 是 AWS 开源授权策略语言（Verified Permissions 等）。典型问题：

> Alice 能否对 Photo123 执行 `delete`？

策略错一字 → 数据泄露或全锁死。授权逻辑必须**绝对正确**。

### 做法：verification-guided development

```
┌────────────── Lean 世界 ──────────────┐
│ 1. 可执行模型（求值器、策略语义）        │
│ 2. 证明安全性质：                       │
│    · deny 永远胜过 permit               │
│    · 求值终止、类型安全                 │
│    · 静态分析报安全 ⇒ 运行时不越权       │
└──────────────────┬────────────────────┘
                   │ 差分测试（海量随机对拍）
┌──────────────────▼────────────────────┐
│ 3. 生产 Rust 实现与模型逐行为对齐        │
└───────────────────────────────────────┘
```

可抄作业的点：

| 实践 | 含义 |
|------|------|
| 模型即规范 | 比自然语言准，比生产代码好读 |
| 对拍搭桥 | 证明管不到外部实现时，随机对拍逼近「实现 ≈ 模型」 |
| 性质是真定理 | 内核检查，不是 code review 主观结论 |

---

## 15.2 Aeneas：Rust → Lean 纯函数

### 问题

Rust 已有内存安全；还要**功能正确**时，在验证器里模拟借用极痛苦。

### 做法：翻译，不模拟

> 所有权已保证内存纪律 → 验证功能时**不必谈内存** → 译成 Lean **纯函数**。

```
Rust ──Aeneas──▶ Lean 纯函数（+ 相关定理）
                      │
                      ▼
               第 14 章式定理证明
```

panic/失败 → `Result` 风格；循环 → 带不变量递归。

**成果**：微软用 Aeneas + Lean 验证 **SymCrypt** 中生产密码算法——安全标准极苛刻。

对 Rust 社区：补齐「不段错误」之外的**逻辑正确**拼图。

### 向同事解释的一句话

> Aeneas 相信 Rust 借用检查已经消灭了一类错误，于是只把「算什么」翻译进 Lean，把「内存怎么布局」留给 rustc。

---

## 15.3 Veil：分布式协议

### 问题

共识/复制/事务：并发 × 延迟 × 故障 = 路径爆炸，测试杯水车薪。

### 多模态

```
协议（Veil DSL ⊂ Lean）
    ├── 模型检查（有限实例穷尽）
    ├── SMT（归纳不变量搜索）
    └── 交互证明（Lean 策略兜底）
```

| 卖点 | 说明 |
|------|------|
| DSL 内嵌 | 像论文伪代码，却有精确语义（第 19 章） |
| 自动优先 | 简单不变量自动过 |
| 内核背书 | 结论最终进 Lean 内核，工具 bug 难「偷渡」 |

---

## 15.4 工业化全景信号

- **Lean FRO**：全职维护核心（基金会级投入）；
- **Harmonic / Aristotle**：安全攸关行业的数学智能；
- **以太坊基金会** → ArkLib（第 16 章）；
- **NASA** 形式化会议中的 Lean/CSLib 声音；
- 大众读物 *The Proof in the Code*。

模式：**错的代价 ≫ 验证成本** 的领域，Lean 在渗透。

---

## 15.5 经验带回你的项目

1. **模型先行**：可执行精确模型 = 顶级设计文档；
2. **性质分级**：先证最值钱不变量（钱、权限）；
3. **自动 + 交互**：`grind`/`decide` 打头，策略收尾；
4. **对拍意识**：模型与实现互相印证。

### 个人落地最小路径

```
选一个高代价模块
  → 抽出纯核心 50 行
  → 写 1～3 条 Safety 定理
  → 证明或 sorry 排队
  → 用随机输入对拍生产代码
```

---

## 15.6 迷你项目：deny 优先的权限系统

```lean
inductive Action | read | write | delete
deriving DecidableEq, Repr

structure Policy where
  allow : List Action
  deny  : List Action
deriving Repr

/-- 最终是否允许：在 deny 中则永不允许；否则看 allow -/
def Policy.permits (p : Policy) (a : Action) : Bool :=
  if a ∈ p.deny then false
  else a ∈ p.allow

/-- 安全性质：deny 列表中的动作永远不被允许 -/
theorem deny_overrides (p : Policy) (a : Action) (h : a ∈ p.deny) :
    p.permits a = false := by
  simp [Policy.permits, h]

/-- 若既不在 deny 又在 allow，则允许 -/
theorem allow_if_not_denied
    (p : Policy) (a : Action)
    (hd : a ∉ p.deny) (ha : a ∈ p.allow) :
    p.permits a = true := by
  simp [Policy.permits, hd, ha]
```

扩展：多策略合并「全局 deny 优先」；请求上下文（用户、资源）做成 `structure Request`。

---

## 15.7 踩坑对照（工业叙事）

| 误区 | 纠正 |
|------|------|
| 「证明了 Lean 就等于证明了线上 Rust」 | 还差编译器/对拍/部署配置 |
| 一次证完所有性质 | 分级；先 Safety |
| 只写模型不连实现 | 对拍或代码生成 |
| DSL 过度复杂 | 覆盖 80% 场景即可 |

---

## 15.8 本章小结

- **Cedar**：模型 + 定理 + 对拍；
- **Aeneas**：Rust→纯函数，验证功能；
- **Veil**：协议 DSL + 多模态；
- 抄作业：模型先行、性质分级、对拍。

---

## 练习

### ⭐ 基础

1. 为 `Action` 增加 `admin`，更新定理。
2. 写 `#eval` 测试 3 条策略。

### ⭐⭐ 进阶

3. 读 cedar-spec 仓库中 deny 相关定理陈述（不必跑通全库）。
4. 为你工作中组件写 1 条 `theorem` 类型规格（可不证）。

### ⭐⭐⭐ 硬核

5. 多策略：`List Policy` 合并规则自定，证全局 deny 优先。
6. 用一页纸向同事讲解 Aeneas vs 「在分离逻辑里验证 Rust」。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| lean-lang.org/use-cases | Cedar / Aeneas / Veil |
| *Verification-Guided Development of Cedar* | AWS 论文 |
| Aeneas / Veil GitHub | 实现细节 |

---

⬅️ [第 14 章](14-software-verification.md) ｜ ➡️ 下一章：[第 16 章　密码学与区块链：验证零知识证明](16-crypto-blockchain.md)
