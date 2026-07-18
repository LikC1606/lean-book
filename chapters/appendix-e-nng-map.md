# 附录 E　自然数游戏与本书对照

> [Natural Number Game](https://adam.math.hhu.de/)（NNG）是最友好的 Lean 入门游戏。通关后常问：「接下来读什么？」本附录把关卡主题映射到本书章节与官方教材。

## E.1 建议玩法

1. 先通 **Tutorial + Addition + Multiplication**（约数小时到两晚）；
2. 与本书 **第 3、8、9 章** 交错，不要求一次打完；
3. 卡住超过 20 分钟 → 看 Infoview 目标，或本书对应策略节；
4. 全部基础世界通关后 → 第 10–11 章 + *Mathematics in Lean*。

## E.2 世界 → 本书章节

| NNG 世界（名称可能随版本微调） | 你在练什么 | 本书 | 再深读 |
|--------------------------------|------------|------|--------|
| Tutorial | 界面、`rw`、`rfl` 直觉 | 第 3、9 章 | TPIL 策略入门 |
| Addition | `0+n`、`succ`、归纳 | 第 3、8、9 章 | 本书 `zero_add` 推演 |
| Multiplication | 分配律、更多归纳 | 第 9–10 章 | FPIL 递归 |
| Power | 指数与复合改写 | 第 9–10 章 | `calc` |
| Implication | `→`、`intro`、`exact`/`apply` | 第 8–9 章 | Mechanics of Proof |
| Advanced Addition / Inequality | `≤`、反证、更细重写 | 第 9–10 章 | `omega` |
| Algorithm / Function | 递归函数与证明交错 | 第 4–5、14 章 | 验证三要素 |
| Set / 其他游戏服世界 | 集合与逻辑 | 第 8、11 章 | MIL 集合论入门 |

> 具体关卡名以游戏内为准；上表按**主题**对齐，不保证关号一一对应。

## E.3 游戏策略 ↔ Lean 策略速查

| 游戏里你常点的 | Lean 里 |
|----------------|---------|
| rewrite / rw | `rw` / `rw [← h]` |
| induction | `induction n with` |
| exact / apply | `exact` / `apply` |
| intro | `intro` |
| use（存在） | `refine ⟨w, ?_⟩` / `exists` |
| cases | `cases` / `rcases` |
| simp（若出现） | `simp` / `simp only` |

## E.4 通关后三条去路

| 你想… | 下一步 |
|-------|--------|
| 继续数学 | 本书第 11–13 章 + [MIL](https://leanprover-community.github.io/mathematics_in_lean/) |
| 继续编程 | 本书第 4–7 章 + `examples/` 里 Ch04 |
| 继续证明手艺 | 本书第 9–10 章 + *Mechanics of Proof* |
| 做项目 | 第 22 章编译器 + `Examples.Ch22` |

## E.5 和本书 `examples/` 的关系

NNG 在浏览器里玩；本地巩固用：

```bash
cd examples && lake build
# 打开 Examples/Ch03.lean、Ch08.lean
```

两边证的是同一类东西（归纳、重写），环境不同而已。

## E.6 其他游戏

同一 [Lean Game Server](https://adam.math.hhu.de/) 上还有集合论、逻辑等游戏。映射原则相同：**游戏建直觉 → 本书给地图 → 英文教材给厚度**。

---

⬅️ [附录 D　官方文档难句白话对照](appendix-d-official-hard.md) ｜ ➡️ （全书完，或回 [SUMMARY](../SUMMARY.md)）
