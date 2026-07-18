# 附录 D　官方文档难句白话对照

> 读官网 / Language Reference / TPIL 时，这些句子最容易劝退。左边是「官方味」说法，右边是本书白话。需要精确细节时仍以官方为准。

## D.1 类型与宇宙

| 官方味 | 白话 |
|--------|------|
| `Prop` is impredicative | 命题宇宙里可以对所有命题做量化，仍得到命题（和 `Type` 层级规则不同） |
| proof irrelevance | 同一命题的两个证明在运行期不可区分；证明常被擦掉 |
| universe polymorphism `Type u` | 泛型不只对类型，还对「类型的层级」通用；日常多半自动 |
| `Sort u` unifies `Prop` and `Type` | `Sort 0 = Prop`，更高的是 `Type` |
| non-cumulative universes | Lean 的宇宙**不**自动 `Type ⊂ Type 1`；需要时再提升 |

## D.2 精化与宏

| 官方味 | 白话 |
|--------|------|
| elaborator | 把表面语法变成内核真正认的项（填隐参、解析重载、展开宏） |
| macro hygiene | 宏引入的名字自动改写，避免和用户变量撞车 |
| quotation `` `(…) `` | 语法树模板；`$x` 把变量嵌进去 |
| syntax category | 扩展点类别：`term` / `tactic` / `command` 等 |
| delaboration | 把内部项「打印」回好看的语法 |

## D.3 类型类

| 官方味 | 白话 |
|--------|------|
| typeclass synthesis | 编译器自动在实例库里拼出 `[Add α]` 这类配件 |
| `outParam` | 实例搜索的「输出参数」：由实例决定，不是你先指定 |
| diamond inheritance | 多父类汇合时的实例路径问题；库作者会设计避免歧义 |
| coherent instances | 同一类型同一类通常至多一个实例，否则 `1+1` 含义不定 |

## D.4 证明与归约

| 官方味 | 白话 |
|--------|------|
| definitional equality / `rfl` | 两边按定义算到同一个东西就能过 |
| propositional equality | 需要证明的 `=`，不一定定义上相等（如 `0+n=n`） |
| opaque / irreducible | 故意不让随便展开的定义 |
| trusted kernel | 只有内核的检查必须正确；外面的策略可以有 bug，错了过不了内核 |
| axioms `Classical.choice` 等 | mathlib 常用经典数学设定；`#print axioms` 可审计 |

## D.5 策略与元编程

| 官方味 | 白话 |
|--------|------|
| metavariable | 证明里的「洞」；策略负责填洞 |
| unification | 两边是否能变成同形（`isDefEq`） |
| `TacticM` / `MetaM` / `ElabM` | 写策略/元程序用的效果单子（读环境、改目标、报错） |
| simp set / `@[simp]` | 化简器用的重写规则库 |

## D.6 怎么用本附录

1. 官方段落读不懂 → 在本表搜关键词；
2. 仍不够 → 回本书对应章（第 5–6、8、17–18 章最常相关）；
3. 要写库 / 提 PR → 再读 Reference 原文，别只停在白话。

## 延伸

- [Language Reference](https://lean-lang.org/doc/reference/latest/)
- [TPIL](https://lean-lang.org/theorem_proving_in_lean4/)
- 社区 learn 页 Foundations 一节

---

⬅️ [附录 C　术语表](appendix-c-glossary.md) ｜ ➡️ [附录 E　自然数游戏与本书对照](appendix-e-nng-map.md)
