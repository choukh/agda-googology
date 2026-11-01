# 路线决定：先走方案 A（[Se98] 逐实例的良序证明）

2026-09-12。本文件完整记录这次路线变更的来龙去脉、做出决定的理由，以及所选路线与三条纲领的关系。它是叙述性的；技术细节在 [RESEARCH.md](RESEARCH.md) §122–§128，执行步骤在 [ROADMAP.md](ROADMAP.md)。

## 0. 决定

**先走方案 A**：把 Setzer 1998 *Well-ordering proofs for Martin-Löf type theory*（[Se98]，`Sources/setzer1998-wellordering.pdf`）以 V := `Set` 转写进 Agda，对它的记号系统 OT_I 证良序，得到 Agda 里**真正定义出来**的自然数 \(F_{\psi_{\Omega_1}\Omega_{\mathrm I+\omega}}(k)\)。做通后再（i）抽象成 Setzer *Ordinal Systems Part 2* 的 I-OS 接口作重构，（ii）按 mahlo.pdf §5 换 I 为 M，回到原目标 \(\alpha_M\)。

## 1. 出发点：两份契约

**BTBO 的三条纲领**（`src/OCF/BTBO.lagda.md` 原文）：

> 1. 序数先行——先实现序数再折叠成大数；排除很难分析序数上下界的函数以及非序数增长率函数。
> 2. 理想计算机可运行——在以类型论为基础的证明助理中无公理地写出定义。
> 3. 保证停机——通过证明助理的自动停机检查器保证停机。

BTBO 按此做到 ψ(Ω_Ω)，并自述「遵循该纲领，我们目前卡在了 ψ(Ω_Ω)」。

**Mahlo 项目的契约**（[CONTRACT.md](CONTRACT.md)）：从类型宇宙的定义规则中自动提取基本列，用于 Mahlo 宇宙，得到具有严格量级证明的 \(F_{\alpha_M}\)，构造大数；验收项 E、C1–C7；纪律：`--safe --without-K`，不靠 postulate、终止绕过或未证明的目标实例交付结果。

两份契约的公共部分：序数先行、无公理、停机检查。分歧在「序数是什么」：BTBO 说是一棵树，Mahlo 项目说是一个记号系统。

## 2. 换手时的现状（2026-09-12，§122）

用户重述核心目标为四段：形式化类型宇宙 → 通用算法提取序数强度 → 得到基本列 → 证明良序。逐段核实前任的完成度：

| 段 | 实际 |
|---|---|
| 形式化类型宇宙 | 未做——只有签名；`ExtSpec` 的输入是三个人手填的字段 |
| 通用算法提取强度 | 半做——规则→参数是纸面推理，参数→记号系统是人手写的 `ExtOT` |
| 得到基本列 | 已做，机检，但载体是人手写的记号系统 |
| 证明良序 | 未做；`NormFGH` 把良基性当**假设字段**，故 \(N_M\) 在 Agda 里不是已定义的自然数 |

当天补上了第一段（[Object/Rules](Object/Rules.lagda.md)：Definition 4.1／4.3 逐条转写为数据）和第二段的前半（[Object/Extract](Object/Extract.lagda.md)：四个句法函数从规则表算出参数，五条规则级扰动机检）。第四段成为唯一的硬缺口。

## 3. 为什么不能直接证良序：一个实验（§122.2）

Setzer 的良序证明（Theorem 5.14）在 MLM **内**、用 Mahlo 宇宙 V 做归纳。要照做，先得在 Agda 里有 V。实测（`Probe/MahloIR.agda.txt`）：

```
data V : Set where
  û : (f : (a : V) → (T a → V) → V) (g : …) → V
```
> `V is not strictly positive, because it occurs to the left of an arrow in the type of the constructor û`

对给定 `F : Set → Set` 封闭的超宇宙则通过（`Probe/SuperIR.agda`）。这是教科书事实：Mahlo 宇宙非严格正。当时的结论是「`WellFounded _≺_` 到 \(\alpha_M\) 在 `--safe` 下无已知路线」——后来收窄（§123.7）。

## 4. 第一次路线讨论：IIRD 当对象理论（§123）

**提议**：既然 Mahlo 宇宙做不出来，转而提取 IIRD 的证明论强度，把它转成良序的基本列。

**核实**：
- 原则：没有理论能证明自己的证明论序数良基。要让 \(F_{|T|}\) 在 Agda 里是全函数，必须 \(|T|<|\mathrm{Agda}|\)。
- Dybjer–Setzer 2003：外部 Mahlo 宇宙可由 IR 定义，故 **IR 的强度至少是 KPM**；且没有精确的序数分析。所以 IIRD 当对象理论既不比 MLM 弱，也没有校准目标。

**重新框定**：IIRD 不是替代的对象理论，而是 Setzer 证明所需的**元工具**。读 mahlo.pdf §5 的证明：Mahlo 宇宙只在 **Lemma 5.10** 用一次，且只要「对一对给定项 (f,g) 封闭的子宇宙」。把 Definition 4.3 的 \(\widehat{\mathrm U}_{f,g}\)、`Res0/Res1` 与两条计算方程取 V := `Set`、s := `T` 写成对 (f,g) 参数化的 IR——`Probe/MahloParam.agda` **通过 `--safe`**。于是有了**路线 C**：把 [Se98] + §5 转写进 Agda。§5 几乎每条都写 "as in [Se98]"，把 I 换成 M；所以顺序被原文定死：先 I 层（[Se98]），再 M 层。

## 5. 第二次路线讨论：把记号重构成 IR 序数，良基性由停机检查保证（§125–§126）

**提议**：从良序证明得到启示，把序数记号重构为归纳递归定义的序数（如 Brouwer 序数），基本列编码进类型，良基性由停机检查自动保证；先做 I；再由通用算法扩展、折叠成大数。

**与本仓库历史的关系**：这正是 `src/OCF` 五月份的纲领。实测（记忆索引、git 历史 `2ceec77…bf75701`）：不比较的树折叠止于 ψ(Ω_Ω)；有界三分到 ψ(Ω_{Ω₂})；再上撞**无界三分**——LPO 禁忌，四条独立路径共同闭合。I 在 ψ(Ω_{Ω₂}) 之上不知多少层。

**文献里的定理**（Setzer 1998，*An introduction to well-ordering proofs in MLTT*，`Sources/setzer1998-intro-wellordering.pdf`，摘要原话）：

> We define ordinal notation systems **from below** and show that the proof-theoretic strength of theories, in which we can define the accessible part, **cannot be expressed in such systems**.

「从下面来」= 每个记号只引用更小的记号 = 良基性由构造自动成立。定理说：只要理论能定义可达部分（有 W 就能），它的强度就不能被这类系统表达。

**两堵墙要分开**（§126.1）：
- 树上的比较禁忌——封「序数是树」这个设计（定义不出需要比较的 ψ）；
- 从下面来的定理——封「证书由语法自动生成」这个愿望。

**能与不能**（§126.2 全表）。要点：序数是句法记号（可判定 ≺）——能；基本列由范数算出——能；F 对可达性证书结构递归——能；证书**类型**归纳——能；证书**元素**由停机检查自动得到——**不能**；序数是树且到 I——**不能**；燃料代替证书——**不能**。

**最小放宽**（§126.3）：三条纲领一条不改；唯一放宽的是 BTBO 范式的隐含约定「只有定义，没有定理」。序数从「一棵树」变成「一个名字 + 一棵证书树」——名字给可判定性，证书树给良基性。代价是一次良序定理。

**用户接受了这个取舍。** 用户直觉里对的部分有文献名：Setzer *Ordinal Systems*（1999；Part 2: *One Inaccessible*，2000）——把记号重组成带有限被引用集、使良序证明结构化；不免除证明。

## 6. 第三次：I 层证明的两个方案（§127）

| | 方案 A：[Se98] 逐实例 | 方案 B：Ordinal Systems Part 2 通用 |
|---|---|---|
| 证的对象 | Setzer 为 ML₁W 写的那一个 OT | 抽象接口 I-OS（10 元组 + 公理 1–10） |
| 端点 | ψ_{Ω₁}Ω_{I+ω} = \|ML₁W\| | ψ(ε_{I+1}) = \|KPI\|，略低 |
| 证明所在理论 | **已在 MLTT 内**（§5 给出类型论构造） | KP 风格集合论；转进 MLTT 未有人做 |
| 实例 | 内置 | 要自给句法实例并证 I-OS 1–10 |
| Mahlo 衔接 | 直接（mahlo.pdf §5） | 无 M-OS 文献 |
| 通用性 | 不通用 | 接口是生成器与证书器的契约 |

**决定 A 的理由**：
1. A 的技术在 MLTT 内已被原文验证；B 的抽象层能否转写未验，先做 B 的风险是白走。
2. A 直接衔接原目标（M 层）；B 没有 Mahlo 续篇。
3. A 的端点更高（多出 I 之上的 ω 个容许），且正是 CONTRACT 意义下的 \(|\mathrm{ML}_1\mathrm W|\)。
4. B 的价值（通用接口）可以在 A 走通后作为**重构**获得——具体证明会告诉我们接口该长什么样；反过来不行。

## 7. 方案 A 与三条纲领的关系

| 纲领 | 方案 A 如何满足 | 与 BTBO 的差别 |
|---|---|---|
| **序数先行** | 记号系统 OT_I 与可判定 `≺` 先于一切；F 是对它的折叠；端点经校准等于 \(|\mathrm{ML}_1\mathrm W|\)（[Se98] 摘要），量级有严格证明 | BTBO 的序数是树，其量级靠估算；这里的序数有精确校准 |
| **理想计算机可运行（无公理）** | 全程 `--safe --cubical-compatible`；无 postulate、无洞、无终止绕过；良序证明是一个 Agda 项；用到的 IR（子宇宙）是 Agda 核心的一部分 | 相同。多用了 IR（BTBO 未用） |
| **保证停机** | 每个函数都过停机检查：F 对证书结构递归，`≺` 对燃料结构递归，良序证明里的递归对证书或语法结构递归 | **唯一放宽**：BTBO 只有定义，停机检查即全部保证；这里多一个定理——证书的存在由证明给出，不由停机检查给出。证书一旦造出，其后一切仍由停机检查保证 |

一句话：**三条纲领原文一条不改；舍去的是「零定理」这条隐含约定。** 这是 §126 的判决，也是唯一能到 I 的组合（§125 的定理 + 本仓库的三重实证）。

（2026-09-12 晚：I 层已按此路线走通到 `Acc-endpt` 与 `𝔑 : ℕ`，相对 `OTFacts`；同日深夜 `OTFacts` 构造完成，定理无条件（`Inacc.Theorem`，RESEARCH §131）；此后的原创方向见 ROADMAP §9。）

## 8. 方案 A 与 CONTRACT 的关系

A 就是 CONTRACT 的流水线在 \(\mathcal C\) 的成员 ML₁W 上**完整跑通**：
- E：`Extract` 对一个普通宇宙的规则表给 `(noRefl, naDeg, schema, Ω 无界)`（§122.3 的 `oneU`），记号系统层数与之对应——§95.7 风险 1 的正面检验；
- C1：端点校准到 \(|\mathrm{ML}_1\mathrm W|=\psi_{\Omega_1}\Omega_{\mathrm I+\omega}\)（[Se98] 摘要）；
- C2–C4、C7：沿用 [Hierarchy/](Hierarchy/) 的抽象接口；**良基性从假设字段变成定理**；
- 大数：\(F_{\psi(\Omega_{\mathrm I+\omega})}(k)\) 是 Agda 里的自然数。

它**不**做的：参数→记号系统的生成器（OT_I 仍是手抄 [Se98] §2）；这条留给方案 B 的重构阶段。

## 9. 成功标准与后续

**I 层成功**：`Acc` 在端点处有证书；`F` 对它全；数的类型可检（值不可求）。中间检查点见 [ROADMAP.md](ROADMAP.md) §3（B1–B6）。

**之后**：
1. 抽象成 I-OS 接口（方案 B 作重构），使生成器可以以它为目标；
2. M 层：按 mahlo.pdf §5 换 I 为 M，Lemma 5.10 用 `Probe/MahloParam` 的 `Sub f g`；
3. 对 n 一致（ℕ-索引归纳族）——若成，\(\alpha_M\) 以下良基，\(N_M\) 成为已定义的自然数。

**天花板**：这条路不越过 \(\alpha_M\)。

## 10. 来龙去脉索引

| 事 | 在哪 |
|---|---|
| 换手重估、正性实验、对象理论形式化 | RESEARCH §122；`Probe/` |
| IIRD 提议的重新框定、路线 C | §123；`Probe/MahloParam.agda` |
| IR 序数提议、两堵墙、Setzer 定理 | §125；`Sources/setzer1998-intro-wellordering.pdf`；记忆 `from-below-notations-theorem` |
| 能与不能的地图、最小放宽 | §126 |
| 方案 A vs B | §127；`Sources/setzer2000-ordinal-systems-2-inaccessible.pdf` |
| 决定 | §128；本文件 |
| OCF 的历史 | 记忆 `ocf-exploration-index` 等四条；git `2ceec77…bf75701` |
| 文献 | [Sources/README.md](Sources/README.md) |
