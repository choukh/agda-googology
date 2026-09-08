# 第二轮：小谓词、归纳生成与见证收集

日期：2026-09-08。状态：完成通用构造层；尚未实例化 Mahlo 记号及其 distinguished-set 理论。

## 1. 本轮落实的构造

| 文件 | 已检查结论 | 尚未提供的输入／结论 |
|---|---|---|
| [Universe/Predicates.agda](Universe/Predicates.agda) | 子宇宙中的自然数谓词代码、全称／存在量化、小索引并及解码方程 | 原论文全部公式的代码翻译 |
| [WellOrder/Accessible.agda](WellOrder/Accessible.agda) | 正归纳生成、构造规则、任意目标层级的归纳与最小性 | 参考记号上的具体 `M(A)`、`τ_A` |
| [Universe/GeneratedCode.agda](Universe/GeneratedCode.agda) | 用现有 Π／Σ／W／等式代码编码上述生成谓词；`sound`、`complete` 和大类目标的消去 | 具体 ordinal 闭包公式及其局部性 |
| [WellOrder/Segments.agda](WellOrder/Segments.agda) | 初始段的并与复合保持初始段性质 | 参考合法记号和顺序的实例化 |
| [WellOrder/SmallCover.agda](WellOrder/SmallCover.agda) | 构造小覆盖 `B ⊆ C ⊆ Global`；由明确的双向初始段刻画推出覆盖的认证 | 真正的 distinguished-set 刻画定理 |

所有模块启用 `--safe --without-K`，仅依赖本项目 Mahlo 模块及 Agda 内建模块。没有新增 postulate、取消终止／正性检查，或引入函数外延性。

## 2. W 编码的实质

给定已编码的候选资格 `M x` 和前驱关系 `Pred x y`，原始 W 树的节点标签携带自然数及资格见证，分支由前驱及其关系见证索引。任意 W 树的子节点标签未必与分支索引吻合，因此额外定义递归的 `valid` 代码，逐条记录标签等式和子树正确性。

`code x` 是根标签为 x 且满足 valid 的树。`sound` 将其解码为索引归纳生成证明；`complete` 将生成证明编码回去。两者证明双向可转换，尚未证明它们互逆。`eliminate` 允许目标谓词处在任意宿主层级。

这表明：**一旦 M 和前驱关系已被编码，归纳生成本身可以留在同一个小子宇宙中。** 此构造没有在 U 中添加索引归纳类型构造子。

## 3. 大小审计

| 表示 | 所在层级 |
|---|---|
| `PredCode = Nat → U` | `Set` |
| 解码后的一个谓词 `A : Nat → Set` | 其类型 `SmallPred` 位于 `Set₁`；每个 `A x : Set` |
| `D A` | 本轮收集定理显式要求其为 `Set` 中的认证类型 |
| `Global x`，对全部小谓词及认证取存在见证 | `Set₁` |
| 把 Global 看作整体谓词时的类型 `Nat → Set₁` | `Set₂` |
| 小输入 B 的收集索引 `Σ Nat B` | `Set` |
| 收集所得 `C x` | `Set` |

收集函数接收 `included : ∀ x → B x → Global x`。其结果带有具体载体、认证和成员见证，因此可按输入成员取出所需小谓词。C 的定义只对小索引 `Σ Nat B` 求和，不对全部小谓词求和。这没有把任意大类缩小，也不要求 B 可判定、可枚举或证明无关。

若未来使用截断的存在性，这个见证提取步骤必须重新审计；当前定义使用未截断的依赖和。

正归纳生成的层级为候选资格与前驱关系层级的并。因此对同级参数，生成操作本身不必提高层级。阶段构造中的其他公式是否同样保持层级，仍未核验；不能据此宣布端点已经统一。

## 4. 文献对应与剩余桥梁

依据 [Setzer 前置论文](https://csetzer.github.io/articles/2papdiss.pdf)：归纳生成对应 §4.10 的规则接口；初始段采用 Definition 4.12 的等价定义。Lemma 4.26 的双向刻画依赖 4.24 的唯一性及先前局部性结果。本轮没有证明这个刻画，而将其两个方向明确列为 `certified-cover` 的参数。

[Mahlo 原文](https://csetzer.github.io/articles/mahlo.pdf) 5.8(c) 引用这一前置结果。当前完成了收集与初始段并的构造步骤；要据此报告 5.8(c) 或 5.10 完成，仍须建立实际记号系统中的刻画，并构造原文实际使用的族算子。

## 5. 下一项可审阅任务

先固定原记号上的有限闭包、`M(A)` 和 `τ_A` 的精确定义，建立局部性接口，再移植 distinguished-set 唯一性及 Lemma 4.26。不能将本轮任意认证参数 D 直接改名为 Ag 就视为完成。

端点审计同时检查 `W_i` 的参数公式及证明能否在固定类型内统一递归。暂不追加更强的宇宙假设。

## 6. 复现

```sh
agda --no-libraries -i src src/Mahlo/Universe/GeneratedCode.agda
agda --no-libraries -i src src/Mahlo/WellOrder/SmallCover.agda
tools/check-src.sh
```

本轮在 Agda 2.8.0 下独立安全检查通过；`tools/check-src.sh` 全部 21 个模块通过，无警告。本地文档链接与 `git diff --check` 通过。原有第一轮的 16 模块统计保留为历史记录。
