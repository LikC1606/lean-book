# 第 14 章　软件验证基础：让 bug 无处遁形

> 本章目标：学会软件验证的基本范式——把程序性质写成定理，然后证明它。这是从"写程序"到"写正确程序"的质变。

测试能发现 bug，但只能发现**被测到**的 bug。Edsger Dijkstra 的名言："测试只能证明 bug 存在，不能证明 bug 不存在。"

软件验证（formal verification）给出更强的承诺：**对程序的所有可能输入，数学性质恒成立**——以机器检查的证明为凭。Lean 是目前做这个的最强工具之一。

## 14.1 第一个被验证的函数：加法交换律的"程序版"

热身：我们自己实现一个加法，然后验证它满足交换律。

```lean
-- 自己实现的加法（刻意不用内置 +）
def myAdd : Nat → Nat → Nat
  | m, 0     => m
  | m, n + 1 => (myAdd m n) + 1

-- 规格（specification）：它和内置加法行为一致
theorem myAdd_eq_add (m n : Nat) : myAdd m n = m + n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [myAdd, ih, Nat.add_succ]
```

这段代码浓缩了软件验证的全部精髓：

1. **程序**（`myAdd`）：要验证的对象；
2. **规格**（`myAdd m n = m + n`）：程序应当满足的性质，写成定理类型；
3. **证明**（`induction` + `rw`）：说服内核"规格对一切输入成立"。

从此，`myAdd` 的正确性不再依赖测试覆盖，而是**数学事实**。

## 14.2 验证一个排序算法

来点真格的：插入排序。要证明两件事：

1. **输出是有序的**（有序性）；
2. **输出是输入的排列**（没有元素凭空增减）。

```lean
import Mathlib

-- 程序：插入排序
def insert (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def insertionSort : List Nat → List Nat
  | []      => []
  | x :: xs => insert x (insertionSort xs)
```

**第 1 步：定义"有序"谓词。**

```lean
def Sorted : List Nat → Prop
  | []           => True
  | [_]          => True
  | x :: y :: ys => x ≤ y ∧ Sorted (y :: ys)
```

**第 2 步：证明插入保持有序。**

```lean
theorem sorted_insert (x : Nat) (xs : List Nat) (h : Sorted xs) :
    Sorted (insert x xs) := by
  induction xs with
  | nil => exact trivial
  | cons y ys ih =>
      match ys, h with
      | [], _ =>
          simp [insert, Sorted]
          omega
      | z :: zs, ⟨hyz, htail⟩ =>
          by_cases hxy : x ≤ y
          · simp [insert, hxy, Sorted]; exact ⟨hxy, hyz, htail⟩
          · simp only [insert, hxy, ↓reduceIte]
            push_neg at hxy
            have hyx : y ≤ x := Nat.le_of_lt hxy
            by_cases hxz : x ≤ z
            · constructor
              · exact hyx
              · -- Sorted (insert x (z :: zs))
                constructor
                · exact hxz
                · exact ⟨hyz, htail⟩
            · push_neg at hxz
              have hzx : z ≤ x := Nat.le_of_lt hxz
              have : Sorted (y :: insert x (z :: zs)) := by
                constructor
                · -- y ≤ head of (insert x (z::zs))，即 y ≤ z
                  exact hyz
                · exact ih htail
              convert this using 2
```

（这段证明较长是正常的——验证的成本比写程序高，这就是它换来确定性的代价。实际工程中会用更多自动化和更巧妙的谓词设计来压缩它。）

**第 3 步：主定理。**

```lean
theorem sorted_insertionSort (xs : List Nat) : Sorted (insertionSort xs) := by
  induction xs with
  | nil => exact trivial
  | cons x xs ih => exact sorted_insert x (insertionSort xs) ih
```

排列性（`List.Perm`）的证明思路类似：`insert` 产生排列，排序保持排列，留作练习。两个定理合起来：**插入排序完全正确**——对所有输入，无一例外。

## 14.3 用类型"先天防错"：带索引的向量

第 5 章见过 `Vec α n`。验证的另一流派：**不事后证明，而是让错误根本无法通过类型检查。**

```lean
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

-- 安全的头元素访问：类型层面排除了空向量！
def Vec.head : Vec α (n + 1) → α
  | .cons x _ => x
```

`Vec.head` 不可能"取下标越界"或"取空表头"——**这些非法调用连类型都过不了，程序根本编译不出来**。这叫"使非法状态无法表示"（make illegal states unrepresentable），是验证的"上游治水"。

实战中两派结合：能用类型表达的放类型里，表达不了的（如"输出有序"）用事后定理。

## 14.4 验证 IO 程序：规范的层叠

真实程序有副作用。验证 IO 程序的常用套路是**分层**：

```
┌─────────────────────────────┐
│ IO 薄壳：读输入、打印输出      │ ← 不验证（信任 Lean 运行时）
├─────────────────────────────┤
│ 纯函数核心：所有业务逻辑       │ ← 验证！证明关于它的定理
└─────────────────────────────┘
```

示例：一个"银行转账"核心。

```lean
structure Account where
  balance : Int
deriving Repr

def transfer (from to : Account) (amount : Int) : Option (Account × Account) :=
  if amount ≤ 0 ∨ from.balance < amount then none
  else some ({ from with balance := from.balance - amount },
             { to with balance := to.balance + amount })

-- 关键不变量：转账前后，两个账户的总余额不变（钱不会凭空产生）
theorem transfer_preserves_total (from to : Account) (amount : Int)
    from' to' (h : transfer from to amount = some (from', to')) :
    from'.balance + to'.balance = from.balance + to.balance := by
  simp only [transfer] at h
  split at h
  · contradiction
  · next hcond =>
      injection h with h1 h2
      subst h1; subst h2
      simp; omega
```

"总余额守恒"这个性质对所有金额、所有账户成立——一行 `omega` 收官，因为它本质上就是 `(x - a) + (y + a) = x + y`（在前提约束下）。

## 14.5 验证工作流：工程视角

真实验证项目的标准循环：

```
1. 建模      把系统/算法写成 Lean 定义（越纯越好）
2. 定规格    把"正确"写成定理类型（Safety / Liveness / 不变量）
3. 证明      交互式完成，sorry 打草稿、逐步填坑
4. 审计      #print axioms 确认无 sorry、无多余公理
5. 集成      提取可执行代码，或作为参考实现做差分测试
```

第 5 步"差分测试"值得一提：AWS Cedar 的做法是——Lean 模型证明正确，同时从模型生成随机测试喂给生产 Rust 代码，检查两边行为一致。这样**证明管模型正确，测试管实现忠于模型**，两段论拼出端到端的信心。下一章细讲。

## 14.6 `sorry` 纪律与验证等级

验证项目里 `sorry` 是双刃剑：打草稿离不开它，但漏一个就等于"该性质未证"。工程纪律：

- CI 中加 `grep -r "sorry" src/` 检查；
- 定期 `#print axioms` 审计关键定理；
- 按性质分级：**核心安全性质**必须无 sorry，边角引理允许排队。

另外要有**验证范围意识**：证明针对的是 Lean 里的模型。模型与现实（编译器、硬件、运行时）之间的缝隙由"信任基"（trusted base）覆盖——Lean 的优势是这个信任基很小（内核 + 编译器 + 硬件），远小于"整个测试套件"。

## 14.7 本章小结

- 软件验证三要素：程序、规格（Prop）、机器检查的证明；
- 经典示范：插入排序的"有序性 + 排列性"双定理；
- 依赖类型让部分性质"先天成立"（`Vec.head` 不可能越界）；
- IO 程序靠"纯核心 + 薄壳"分层验证；不变量是最常见的规格形态；
- 工程流程：建模→定规格→证明→公理审计→差分集成。

## 练习

1. 验证 `myReverse`（第 3 章练习）：证明 `theorem reverse_reverse (xs : List Nat) : xs.reverse.reverse = xs`（可用标准库 `List.reverse_reverse`，但试着自己归纳）；
2. 为 `transfer` 再证一条规格："余额不足时转账必然失败"：`from.balance < amount → transfer from to amount = none`；
3. 完成插入排序的排列性证明：`insertionSort xs ~ xs`（`List.Perm`，提示：先证 `insert x xs ~ x :: xs`）；
4. 给 `Vec` 写 `map` 并证明 `Vec.map f (Vec.map g v) = Vec.map (f ∘ g) v`（归纳）；
5. （开放题）找一个你工作中 30 行以内的小函数，试着把它的关键性质写成 Lean 定理——哪怕暂不证明，体会"定规格"这件事本身的价值。

## 延伸阅读

- 《The Hitchhiker's Guide to Logical Verification》——程序验证的系统教材（Lean 版）；
- Software Foundations（《软件基础》）系列——验证领域的经典，思想完全通用（原书用 Coq，Lean 社区有移植版）。

---

⬅️ [第 13 章](13-mathlib-analysis.md) ｜ ➡️ 下一章：[第 15 章　工业级案例：AWS、Rust 与分布式协议](15-industry-verification.md)
