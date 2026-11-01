# Mahlo：从类型宇宙规则自动提取基本列

**核心目标**（[CONTRACT.md](CONTRACT.md)）：形式化类型宇宙 → 用通用算法从中提取序数强度 → 得到基本列 → 证明良序 → 得到 \(F_{\alpha_M}\) 与大数。校准目标 \(\alpha_M=\psi_{\Omega_1}\Omega_{\mathrm M+\omega}=|\mathrm{MLM}|\)（Setzer 的一个 Mahlo 宇宙）。

研究内容不参与默认成品发布（Makefile 的 `ARTICLE_DIRS` 不含 `src/Mahlo`）；`tools/check-src.sh` 会检查这里全部 `.agda`／`.lagda.md`。

## 现状（2026-09-12）

| 段 | 状态 |
|---|---|
| 形式化类型宇宙 | **做出**：[Object/Rules](Object/Rules.lagda.md)——Definition 4.1／4.3 逐条转写为数据 |
| 通用算法提取强度 | **半做**：[Object/Extract](Object/Extract.lagda.md) 用句法函数从规则表算出参数 \((\Pi_2,\ \text{度 }2,\ \text{模式},\ \Omega\text{ 无界})\)，规则级扰动机检；参数 → 记号系统仍是人手写的 [Notation/ExtOT](Notation/ExtOT.lagda.md)，无生成函数 |
| 得到基本列 | **做出**：\(\lambda[n]\) 有界搜索，`≺` 全函数可判定（[Notation/](Notation/)；I 层自包含版 [Inacc/FGH](Inacc/FGH.lagda.md)，`λ[n] ≺ λ` 机检） |
| 证明良序 | **I 层做出（方案 A）**：[Se98] §2、§4、§5 全部转写进 [Inacc/](Inacc/README.md)（`--safe --cubical-compatible`），**Theorem 4.41 无条件机检**（[Inacc/Theorem](Inacc/Theorem.lagda.md)）：`wellfounded : ∀ n → OT y → y ≺ ψ_{Ω₁}Ω_{I+n} → Acc y`，大数 `𝔑 : ℕ`；Assumption 4.3 的 58 条句法事实全部已证（[Inacc/FactsImpl](Inacc/FactsImpl.lagda.md)，2026-09-12）。M 层：内部 Mahlo 宇宙被 `--safe` 拒绝，但 Setzer 的证明只需参数化子宇宙（[Probe/MahloParam](Probe/MahloParam.agda) 通过）。计划见 [ROADMAP.md](ROADMAP.md) |

大数 \(N_M=F_{\lambda_M}(8)\) 纸面定义完整；**在 Agda 里尚不是已定义的自然数**（良基性仍是 [Hierarchy/NormFGH](Hierarchy/NormFGH.lagda.md) 的假设字段）。

**当前动作**：2026-09-12 经三轮路线讨论后**决定先走方案 A**——把 [Se98] 转写进 Agda，对 OT_I 证良序，得到真正定义出来的 \(F_{\psi(\Omega_{\mathrm I+\omega})}(k)\)；来龙去脉与理由见 [DECISION.md](DECISION.md)，步骤见 [ROADMAP.md](ROADMAP.md)。三条纲领不改，只多一个良序定理。

## 十分钟接手

1. 本文件 → [DECISION.md](DECISION.md)（为什么走这条路）→ [RESULTS.md](RESULTS.md)（已确立什么，各自可信度）→ [ROADMAP.md](ROADMAP.md)（下一步怎么做）。
2. 文献：`bash Sources/FETCH.sh`，再看 [Sources/README.md](Sources/README.md)——**mahlo.pdf 只能读图**。
3. 编译（仓库根目录）：`for f in Object/Rules Object/Extract Notation/ExtOT Notation/ExtSearch Notation/ExtOrd Hierarchy/NormFGH Hierarchy/Bachmann Hierarchy/OTNorm; do agda --safe src/Mahlo/$f.lagda.md; done`
4. 查某条结论的来龙去脉：[RESEARCH.md](RESEARCH.md) 是按轮次追加的日志，**后面的节推翻前面的**，头部有导航；[SOURCES.md](SOURCES.md) 是逐节的引用边界。

## 目录

| 位置 | 内容 |
|---|---|
| [CONTRACT.md](CONTRACT.md) | 目标与验收（E、C1–C7）。不改 |
| [INPUT.md](INPUT.md) | 被分析理论的纸面规格；形式化版在 Object/Rules |
| [RESULTS.md](RESULTS.md) | **分类的结果摘要**，标机检／纸面／引用 |
| [DECISION.md](DECISION.md) | **路线决定的完整叙述**：三轮讨论、能与不能、为什么选方案 A、与三条纲领的关系 |
| [ROADMAP.md](ROADMAP.md) | **执行计划**：前置、I 层（方案 A）、重构（方案 B）、M 层、并行项、风险 |
| [RESEARCH.md](RESEARCH.md) | 研究日志 §56–§129（§1–§55 在 Archive） |
| [SOURCES.md](SOURCES.md) | 逐节引用边界 |
| [Inacc/](Inacc/README.md) | **方案 A 主线**：OT_I 语法／序／闭包／函数（[Se98] §2）与良序证明（§4–§5）的 Agda 转写，自包含 |
| [Object/](Object/) | `Rules`（MLM 规则系统作为数据）、`Extract`（提取器） |
| [Notation/](Notation/) | `ExtOT`（项系统 OTˣ、范数、SC）、`ExtSearch`（λ[n] 有界搜索）、`ExtOrd`（序 ≺） |
| [Hierarchy/](Hierarchy/) | `NormFGH`（范数基本列上的 FGH，C4）、`Bachmann`（正则性）、`OTNorm`（Setzer length 与 BCW 范数互控） |
| [Probe/](Probe/README.md) | 四个决定性小实验（两个故意失败） |
| [Sources/](Sources/README.md) | 文献缓存与重取脚本（PDF 不入库） |
| [Archive/](Archive/README.md) | 2026-09-09 归档的旧路线（Legacy）＋ 研究日志 §1–§55 |

## Agda 模块

均 `--safe --cubical-compatible`，Agda 2.8.0 + stdlib 2.4，无 postulate、无洞、无终止绕过。

| 模块 | 机检了什么 | 假设了什么 |
|---|---|---|
| `Mahlo.Object.Rules` | MLM 规则表可构造 | 基段消去子形状按标准 ML（[Se93] 待核） |
| `Mahlo.Object.Extract` | `spec mlm` 的四个参数由规则表算出；五条规则级扰动；四条 `≢` | 读出规则的正确性（纸面，C1） |
| `Mahlo.Notation.ExtOT` | 范数重现 BCW 手写七条、`N1′=1`、可加性、`size ≤ 3N+1`、端点范数 7、`SC`、`isReg` | 签名来自纸面推导 §115.2／§117.3 |
| `Mahlo.Notation.ExtSearch` | λ[n] 候选表有限且不漏；`≺` 递归的十条测度 | — |
| `Mahlo.Notation.ExtOrd` | `≺` 全函数、可判定，十七条算例 | 线序、燃料充分性未证 |
| `Mahlo.Hierarchy.NormFGH` | FGH 单调、层级支配、`Acc` 无关 | **良基性是记录字段** |
| `Mahlo.Hierarchy.Bachmann` | Cichon 极大性 ⟹ Bachmann 性质 | — |
| `Mahlo.Hierarchy.OTNorm` | 两范数线性互控，常数 2 | — |
| `Mahlo.Probe.MahloParam`、`SuperIR` | 参数化子宇宙／超宇宙在 `--safe` 可定义 | — |
| `Mahlo.Inacc.Syntax/Order/Closure/Arith` | [Se98] Def 2.2–2.13 逐字：T′、≺′、G_π、Cr′、OT、+、φ、Ω、ã、a⁺…；端点 ∈ OT；50 余条算例 | 线序（`Linear`、`Trans`）、燃料充分性（`OrderProps`）已证 |
| `Mahlo.Inacc.WO.K/Base/CLemmas` | Def 5.1–5.6：K^a、C^a(A)、M、τ、𝒜、`𝒲`（归纳族）；Assumption 4.10、Lemma 5.5、4.13 (a)、4.7 (h)、Remark 4.20 | — |
| `Mahlo.Inacc.WO.Facts` | `record OTFacts`：§4 用到的 58 条句法事实（Assumption 4.3 显式化） | **已构造**（`Inacc.FactsImpl`；证明在 `Inacc.OrderProps/Unfold/Linear/Trans/Lex/Subterm/Facts1/Facts2/Facts2b/Facts3`） |
| `Mahlo.Inacc.WO.OrderLemmas/Lemma47 F` | Lemma 4.7 (a)–(d)、4.9 (a)(b)(c)(e) | 参数 `F : OTFacts`（`Inacc.Theorem` 以 `facts` 实例化） |

## 读法提醒

RESEARCH.md 共 **23 处**更正／撤回，清单在 [RESULTS.md §8](RESULTS.md)。其中三处是**对本项目自己声称的撤回**（§121 的「E 机器检验」、§118.4 的禁令、§122.2 的「无路线」）；读任何一节前先看它后面有没有被改。
