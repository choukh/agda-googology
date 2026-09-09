# U0：对象理论与宿主候选

状态：首轮规则实现审计，尚未建立整个 MLM 的形式化解释。2026-09-08。

2026-09-09 补充：[理论探索二](Evidence/EXTRACTION-BRIDGE-2.md)核查了 MLM、带额外宇宙的 MLM⁺ 与 MLMacc 的区别，并审计本地 W 编码仍使用宿主索引归纳证明的边界。当前执行主线见 [EXTRACTION-PLAN.md](EXTRACTION-PLAN.md)；本文件末节保存旧反射路线的下一关，不作为当前编码任务。

目标固定为 Setzer 的 `MLM` 及其记号下的 `α_M = ψ_{Ω₁}(Ω_{M+ω})`。新发现的历史 `probes/OCF/Notation/Mahlo.lagda.md` 含有待证的规范性／共尾性／良基性义务，不能按名字直接当作这个参考系统。

## 1. 已实现的宿主选择

[Universe/External.agda](Universe/External.agda) 使用最底层 Agda `Set` 作为大宇宙代码的候选解释：

| 对象 | 宿主类型 | 作用 |
|---|---|---|
| `V = Set` | `Set₁` | 代码类型；不是新的递归数据类型 |
| `T A = A` | `V → Set` | 解码 |
| `Fam` | `Set₁` | `Σ Set (λ A → A → Set)` |
| `F` | `Fam → Fam` | 任意宿主族算子，作为开放参数 |
| `Close.U F` | `Set` | 对该算子封闭的小子宇宙代码 |
| `Close.El F` | `Close.U F → Set` | 小子宇宙的解码 |
| `u F = Close.U F` | `V` | 把小子宇宙作为大宇宙的一个代码 |
| `s F = Close.El F` | `T (u F) → V` | 小代码到大代码的映射 |

这使 `T (u F) = Close.U F` 按定义成立。构造不分析任意 `Set` 的形状，没有为大宇宙添加通用模式匹配消去器。归纳递归只用于参数化的小代码 `U`。

关键已证等式是 `decode (restrict c) ≡ F (decode c)`，在任意开放参数 `F` 和任意小族 `c` 下成立；不是只验证恒等算子。文件另有依赖输入族两个分量的具体算子实例，以及对原文 §5.9 常值族重编码的实现。

## 2. 原始规则的对应范围

对照 [Setzer 原文 §4](https://csetzer.github.io/articles/mahlo.pdf) 和 [Dybjer–Setzer §2](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf)，当前实现覆盖子宇宙及其解码／限制映射的核心接口，包含有限类型、自然数、和、Π、Σ、W 与同一类型内的等同代码。

当前还没有给出对象理论语法、上下文和推导的解释函数；也没有逐条验证原论文从更早系统继承的全部规则。因此不能把上述接口的编译成功直接升级为 `MLM` 的完整健全解释或 `α_M` 的良序证明。详见 [规则表](RULE-MATRIX.md)。

作者旧辅助文件 `MonomorphicSets.agda` 定义了 K，不能整体作为 `--without-K` 基础导入。这里重新实现所需构造，仅使用 Agda 内建自然数、Σ 和等式，不导入该辅助文件。它与作者的参数化 IR 思路对应，但没有把整个作者仓库视为同一安全配置下的已证依赖。

## 3. 仍需解决的大小问题

这个宿主候选允许大小不同的类型共存，不意味着对象理论所有类型都被翻译为最底层 `Set`。尤其 `V` 和关于 `V` 的量化位于较高层。若后续采用一个统一的语法解释类型，必须明确层级索引或 `Lift`，并证明计算规则在该解释中保持。

首轮不假定“提高一层足以统一所有阶段”，也不把 `Set₁` 的存在等同于目标端点已经可达。端点单独列在 [ENDPOINT.md](ENDPOINT.md)。

## 4. 下一关

将完整推导健全性拆为：基础类型构造／消去、Mahlo 核心规则、代换及转换三部分。先明确原良序证明实际使用哪些规则，再确定采用完整语法解释还是直接移植其证明项。

下一项数学核心仍是 Setzer Lemma 5.10–5.11；本轮尚未实现 distinguished sets，不将小子宇宙构造本身计为该引理已完成。
