# 第 14 章　软件验证基础：让 bug 无处遁形

> 本章目标：学会软件验证的基本范式——把程序性质写成定理并证明。学完后你能验证自写函数、排序有序性骨架、转账不变量，并建立 `sorry` 纪律。

测试能发现 bug，但只能发现**测到的** bug。Dijkstra：「测试只能证明 bug 存在，不能证明不存在。」

形式化验证：**对所有输入，性质成立——由机器检查的证明背书。**

## 本章你会做出什么

1. 验证 `myAdd` 与内置加法一致；
2. 理解插入排序「有序 + 排列」双规格；
3. 用 `Vec` 做类型层防错；
4. 证明转账总余额守恒；
5. 掌握建模→规格→证明→审计流程。

---

## 14.1 三要素：程序 · 规格 · 证明

```lean
def myAdd : Nat → Nat → Nat
  | m, 0     => m
  | m, n + 1 => (myAdd m n) + 1

theorem myAdd_eq_add (m n : Nat) : myAdd m n = m + n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [myAdd, ih, Nat.add_succ]
```

| 要素 | 本例 |
|------|------|
| 程序 | `myAdd` |
| 规格 | `myAdd m n = m + n` |
| 证明 | 归纳 + 重写 |

正确性不再依赖测试覆盖，而是**数学事实**。

---

## 14.2 验证排序：有序性（完整无 `sorry`）

有序性用标准库 **`List.Pairwise (· ≤ ·)`**（比手写「相邻 ≤」更好用：`Pairwise.cons` 要求「头 ≤ 每一个后继」）。

**可构建全文**（已通过 `lake build`，无 `sorryAx`）：

```bash
cd examples && lake build
# 模块 Examples.Ch14Sort
```

### 程序与规格

```lean
def insert (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def insertionSort : List Nat → List Nat
  | []      => []
  | x :: xs => insert x (insertionSort xs)

def Sorted (xs : List Nat) : Prop := List.Pairwise (· ≤ ·) xs
```

### 引理：`mem_insert`

插入不丢元素、也不多造元素（除了新插入的 `x`）：

```lean
theorem mem_insert (x : Nat) (xs : List Nat) (z : Nat) :
    z ∈ insert x xs ↔ z = x ∨ z ∈ xs := by
  induction xs with
  | nil => simp [insert]
  | cons y ys ih =>
      -- 对 x ≤ y / ¬x ≤ y 分情形，展开 insert 后用 List.mem_cons + ih
      ...  -- 完整分支见 Ch14Sort.lean
```

### 主定理：`sorted_insert` / `sorted_insertionSort`

```lean
theorem sorted_insert (x : Nat) (xs : List Nat) (hs : Sorted xs) :
    Sorted (insert x xs) := by
  induction xs with
  | nil => exact List.pairwise_singleton (· ≤ ·) x
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · -- 结果 x :: y :: ys：Pairwise.cons + ≤ 传递
        have heq : insert x (y :: ys) = x :: y :: ys := by simp [insert, hxy]
        rw [heq]
        refine List.Pairwise.cons ?_ hs
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzys
        · exact hxy
        · exact Nat.le_trans hxy (List.rel_of_pairwise_cons hs hzys)
      · -- 结果 y :: insert x ys
        have hyx : y ≤ x := Nat.le_of_not_le hxy
        have h_ins := ih (List.pairwise_cons.mp hs).2
        have heq : insert x (y :: ys) = y :: insert x ys := by simp [insert, hxy]
        rw [heq]
        refine List.Pairwise.cons ?_ h_ins
        intro z hz
        rcases (mem_insert x ys z).mp hz with rfl | hzys
        · exact hyx
        · exact List.rel_of_pairwise_cons hs hzys

theorem sorted_insertionSort (xs : List Nat) : Sorted (insertionSort xs) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih => exact sorted_insert x (insertionSort xs) ih
```

### 轻量排列性：`count` 不变

```lean
def count (a : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if a = y then 1 else 0) + count a ys

theorem count_insertionSort (z : Nat) (xs : List Nat) :
    count z (insertionSort xs) = count z xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [insertionSort, count, count_insert, ih]
```

对每个 `z`，排序前后出现次数相同 ⇒ 没有凭空增减元素（mathlib 的 `List.Perm` 更强，思想一致）。

`#print axioms sorted_insertionSort` 在示例中仅依赖 `propext` / `Quot.sound`，**无 `sorryAx`**。

---

## 14.3 类型层防错：`Vec`

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.head : Vec α (n + 1) → α
  | .cons x _ => x
```

空表取头**无法通过类型检查**——*make illegal states unrepresentable*。

实战组合：

- 能类型表达 → 放类型；
- 不能（如「有序」）→ 事后定理。

```lean
def Vec.map (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (xs.map f)

theorem Vec.map_map (f : β → γ) (g : α → β) (v : Vec α n) :
    (v.map g |>.map f) = v.map (f ∘ g) := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [Vec.map, ih]
```

---

## 14.4 转账不变量：纯核心

> ⚠️ Lean 里 `from` 是关键字，参数请用 `src` / `dst`（与 `examples/Examples/Ch14.lean` 一致）。

```lean
structure Account where
  balance : Int
deriving Repr

def transfer (src dst : Account) (amount : Int) :
    Option (Account × Account) :=
  if amount ≤ 0 ∨ src.balance < amount then none
  else some ( { src with balance := src.balance - amount },
              { dst with balance := dst.balance + amount } )

theorem transfer_preserves_total
    (src dst : Account) (amount : Int)
    (src' dst' : Account)
    (h : transfer src dst amount = some (src', dst')) :
    src'.balance + dst'.balance = src.balance + dst.balance := by
  simp [transfer] at h
  -- 成功分支被 simp 收成：前提 ∧ 账户结构相等
  rcases h with ⟨_, rfl, rfl⟩
  change (src.balance - amount) + (dst.balance + amount)
      = src.balance + dst.balance
  omega
```

「钱不会凭空产生」——对所有账户、金额成立。

### 失败规格

```lean
theorem transfer_fail_if_nonpos
    (src dst : Account) (amount : Int) (h : amount ≤ 0) :
    transfer src dst amount = none := by
  simp [transfer, h]

theorem transfer_fail_if_insufficient
    (src dst : Account) (amount : Int)
    (h : src.balance < amount) :
    transfer src dst amount = none := by
  simp [transfer]
  -- amount ≤ 0 已失败；否则由 h 推出余额不足分支
  by_cases h0 : amount ≤ 0 <;> simp [h0, h]
```

对照代码：`examples/Examples/Ch14.lean`（`lake build` 已通过）。

---

## 14.5 IO：纯核心 + 薄壳（复习第 7 章）

```
IO 薄壳：读写终端/文件     ← 通常不验证实现细节
纯函数核心：业务逻辑       ← 验证！
```

```lean
def transferPure := transfer   -- 已是纯
def runTransferIO (a b : Account) (n : Int) : IO Unit := do
  match transferPure a b n with
  | none => IO.println "失败"
  | some _ => IO.println "成功"
```

---

## 14.6 工程工作流

```
1. 建模   系统写成 Lean 定义（越纯越好）
2. 定规格 Safety / Liveness / 不变量 → theorem 类型
3. 证明   sorry 打草稿，逐步填
4. 审计   #print axioms；CI 禁 sorry
5. 集成   提取代码或与生产实现对拍（差分测试）
```

差分测试（Cedar 风格）：**证明管模型，对拍管实现忠于模型**。

### `sorry` 纪律

- CI：`grep -R "sorry" src/` 失败即红；
- 关键路径零 sorry；边角可排队；
- 信任基：内核 + 编译器 + 硬件 —— 比「整套测试」小得多。

### 规格分类速查

| 类型 | 例子 |
|------|------|
| 功能正确 | 输出 = 参考实现 |
| 安全不变量 | 总余额守恒、不越权 |
| 活性 | 请求终将得到响应（分布式更难） |
| 精化 | 具体实现 refinement 抽象模型 |

---

## 14.7 踩坑对照

| 症状 | 处理 |
|------|------|
| 证明比代码长 10 倍 | 正常；改规格/谓词/自动化 |
| `if` 难证 | `split_ifs` / `by_cases` |
| Option 难拆 | `cases h` / `injection` |
| 只测了几个例子 | 例子 ≠ 证明；可当 `#eval` 回归 |
| 验证了模型以为验证了 C 代码 | 信任基与对拍要说清 |

---

## 14.8 本章小结

- 三要素：程序、规格、证明；
- 排序双规格；`Vec` 先天防错；
- 不变量是最常见规格；
- 分层验证 IO；工程五步 + sorry 纪律。

---

## 练习

### ⭐ 基础

1. 证 `xs.reverse.reverse = xs`（归纳或库）。
2. 证 `transfer` 在 `amount ≤ 0` 时失败。

### ⭐⭐ 进阶

3. 打开 `examples/Examples/Ch14Sort.lean`，跟读 `sorted_insert` 两个分支，用自己的话解释 `Pairwise.cons` 的前提。
4. `Vec.map_map` 对你的定义重证（见 `Examples.Ch14`）。
5. 为 `insert` 补全 `count_insert` 的手写版（不看答案），再 `#print axioms`。

### ⭐⭐⭐ 硬核

6. 工作中 ≤30 行函数：只写规格类型，列信任假设。
7. 读 Hitchhiker 一章，对照本章工作流。

---

## 延伸阅读

| 资源 | 内容 |
|------|------|
| Hitchhiker's Guide to Logical Verification | 系统课 |
| Software Foundations | 经典思想（Coq） |
| 第 15 章 | 工业落地 |

---

⬅️ [第 13 章](13-mathlib-analysis.md) ｜ ➡️ 下一章：[第 15 章　工业级案例：AWS、Rust 与分布式协议](15-industry-verification.md)
