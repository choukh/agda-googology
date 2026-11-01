# 执行计划：方案 A（[Se98] 逐实例）→ I 层 → M 层

2026-09-12 重写；同日**决定先走方案 A**（理由与来龙去脉见 [DECISION.md](DECISION.md)）。目标与验收以 [CONTRACT.md](CONTRACT.md) 为准；已确立的结果在 [RESULTS.md](RESULTS.md)；推理与证据在 [RESEARCH.md](RESEARCH.md)。

## 0. 路线一句话

把 Setzer [Se98]（一个宇宙的良序证明）以 V := `Set` 转写进 Agda，对 OT_I 证良序，得到 Agda 里真正定义出来的 \(F_{\psi_{\Omega_1}\Omega_{\mathrm I+\omega}}(k)\)；走通后抽象成 I-OS 接口（方案 B 作重构），再按 mahlo.pdf §5 换 I 为 M 回到 \(\alpha_M\)。

命名：**方案 A／B** 指 I 层良序证明的两种做法（[Se98] 逐实例／Ordinal Systems Part 2 通用，§127）；**I 层／M 层**指两段目标。

## 1. 现状一览

| 段 | 状态 | 位置 |
|---|---|---|
| 形式化类型宇宙 | 做出 | [Object/Rules](Object/Rules.lagda.md) |
| 规则 → 参数 | 做出（句法函数，规则级扰动） | [Object/Extract](Object/Extract.lagda.md) |
| 参数 → 记号系统 | **人手实例**，无生成函数 | [Notation/ExtOT](Notation/ExtOT.lagda.md) |
| `≺`、λ[n] | 全函数可判定；线序未证 | [Notation/ExtOrd](Notation/ExtOrd.lagda.md)、[ExtSearch](Notation/ExtSearch.lagda.md) |
| FGH 与正则性 | 抽象接口机检；良基性是假设 | [Hierarchy/](Hierarchy/) |
| 良序 | **Theorem 4.41 无条件机检**（[Inacc/Theorem](Inacc/Theorem.lagda.md)）：`wellfounded : ∀ n → OT y → y ≺ ψ_{Ω₁}Ω_{I+n} → Acc y`，`𝔑 : ℕ`；`OTFacts` 的 58 条全部已证（[Inacc/FactsImpl](Inacc/FactsImpl.lagda.md)，2026-09-12） | [Inacc/](Inacc/README.md) |

## 2. 前置

| # | 项 | 说明 | 规模 |
|---|---|---|---|
| P1 | **`≺` 的线序**（自反、传递、三分）→ **构造 `OTFacts` 记录**（58 条句法事实：Lemma 2.4、Remark 2.12/2.14/2.15、几条 (≺′i) 读出） | **做出（2026-09-12）**：[Inacc/FactsImpl](Inacc/FactsImpl.lagda.md)，按 §10 的七步；§131 | — |
| P2 | **合式性** | [Se98] §2 的 OT 定义（(OT1)–…）；`C̃_κ(b)` 里 `SC_κ`／`G_κ` 与 `≺` 互递归，分叉判据已推出（§119.1） | 中 |
| P3 | 读 [Se98] §2–§5 | `Sources/setzer1998-wellordering.txt` 可抽取。结构：§2 记号系统（行 458–1259）、§3 在类型论里工作（1259–1544）、§4 良序证明（1544–2499）、§5 类型论构造（2499–） | 读 |

## 3. I 层（方案 A）

| 步 | 内容 | 检查点 |
|---|---|---|
| B1 | 转写 [Se98] §2 的 OT_I（对照 `ExtOT`：K 换成 I，坍缩符号按原文定）；范数、λ[n]、`≺` 照 Notation/ 的做法。命名按 Ordinal Systems Part 2 的 I-OS 结构组织，为日后抽象留路 | **定义部分做出**（`Inacc.Syntax/Order/Closure/Arith`，§129.3）：端点是项、∈ OT，20 条 `≺` 算例。P1（构造 `OTFacts`）已做出（§131）；λ[n] 留到 B6 |
| B2 | V := `Set`：定义 [Se98] §3–§5 的类型论构造——\(\mathcal P(\mathrm N):=\mathrm N\to\mathsf{Set}\)、Ag、W(A)、\(\mathcal A\)、\(\tau\)、distinguished sets／classes | **做出**（`Inacc.WO.K/Base`，§129.1）：`𝒲` 是带参数的归纳族，Assumption 4.10 两条机检；`W` 本身（Def 4.25，对 `Set` 量化）在 4.25 处定义 |
| B3 | Lemma 4.7–4.40（§4 全部；4.17 (c) 与 4.30、4.37 是难点） | **全部做出**（§129.3 系列），`OTFacts` 已构造，故无条件 |
| B4 | **对 n 一致**：`data 𝒲 : ℕ → N → Set`（`suc i` 处引用 `𝒲 i`）——§123.5 的推测，此处验证 | **成立**：`Wi : ℕ → Pred 1ℓ` 由 ℕ 递归定义，Lemma 4.40 对 i 真归纳（`Main.l440`） |
| B5 | Theorem 4.41 ⟹ `∀ β ≺ ψ(Ω_{I+ω}) → Acc β` ⟹ `Acc` 在端点 | **做出，无条件**（`Theorem.wellfounded`、`thm441`） |
| B6 | 接 [Hierarchy/NormFGH](Hierarchy/NormFGH.lagda.md)：`F` 全函数，\(F_{\psi(\Omega_{\mathrm I+\omega})}(k)\) **是 Agda 里的自然数** | **做出**（[Inacc/FGH](Inacc/FGH.lagda.md)）：λ[n] 有界搜索，`F′` 沿 `Acc` 递归，`BIG n = F_{ψΩ₁Ω_{I+n}}(n)`，`𝔑 = BIG 8 : ℕ`；无条件（`Theorem.𝔑`）。候选表完整性另证 |

同时这一步就是 CONTRACT 的流水线在成员 ML₁W 上完整跑通（[DECISION.md](DECISION.md) §8）。

## 4. 重构：抽象成 I-OS 接口（方案 B）

A 走通后，把 B2–B5 的证明抽象到 Setzer *Ordinal Systems Part 2* 的 I-OS 结构（Def 3.1，公理 I-OS 1–10）上：一次通用定理，任何满足接口的系统免费获得证书；生成器（参数 → 记号系统）以该接口为目标。风险：Part 2 §5 在 I-OS 一般性下能否转进 MLTT，未验——由 A 的具体证明来回答。

## 5. M 层（路线 C）

| 步 | 内容 | 检查点 |
|---|---|---|
| C1 | OT(M) = [Notation/ExtOT](Notation/ExtOT.lagda.md)（已有），补 P1、P2 | — |
| C2 | Lemma 5.1（`sc_M`、`C_κ` 性质）、5.2（替换 4.17）、5.3–5.9 | 逐条 |
| C3 | **Lemma 5.10**：对每个 a 构造 (f,g)，用 `Probe/MahloParam` 的 `Sub f g` 作 \(\widehat{\mathrm U}_{f,g}\) | 唯一的 Mahlo 步骤 |
| C4 | Lemma 5.11–5.13，Theorem 5.14 | 每个 n |
| C5 | 对 n 一致（同 B4） | ⟹ \(\alpha_M\) 以下良基 |
| C6 | \(N_M=F_{\lambda_M}(8)\) 成为已定义的自然数 | 目标达成 |

## 6. 并行、正交

| 项 | 说明 |
|---|---|
| 参数 → 记号系统的**生成器** | 以 `Params` 为参数的通用项系统构造；目标接口取 I-OS（§4） |
| 基段消去子核对 [Se93] | `Sources/setzer1993-thesis.pdf` 已取得 |
| E-2（绑定／代换／计算相容） | 定理 S′ 的形式化 |
| C6 反向 | BCW 的 T(M) Corollary 形式（§114.1），须换双指数界（§114.5） |
| Rathjen 1991 | 未取得 |

## 7. 规模与风险

| 风险 | 后果 | 对策 |
|---|---|---|
| B4／C5 的一致性做不出 | 只得每个固定 n；数略小但仍是真数 | 先做固定 n |
| [Se98] 依赖 ML 特有的等式规则 | 转写时在 Agda 里选对应物 | 原文说四个变体强度相同 |
| P1 规模失控 | 阻塞一切 | （已解除：燃料充分性 → 展开 → 线序 → 各字段，§131） |
| 总量 | 几周到几个月 | 按 B1–B6 分检查点，每步可编译 |

## 8. 纪律

- 三条纲领不改：序数先行、无公理（`--safe --cubical-compatible`）、停机检查（每个函数结构递归）。唯一放宽：多一个良序定理（[DECISION.md](DECISION.md) §7）。
- 凡放宽构造以求方便，先问会不会抬高端点（§100.3）。
- 参考系统的表只作**检验**，推导在先、核对在后（§120.3）。
- 已排除项：§92.3 的十一条；IIRD 作替代对象理论（§123.2）；在 `--safe` 定义内部 V（§122.2）；序数是树且到 I（§125）；证书由语法自动生成（§125）。

## 9. 关掉 `OTFacts` 之后：原创方向（2026-09-12 与用户讨论后定）

强度结果（|ML₁W|、|MLM|、IR ≥ KPM）都是 Setzer／Dybyer 的定理，机器里重做不是原创。原创空间在**这条证明在机器里究竟需要什么**，以及**把"通用算法"做成机器对象**。按"再努力一把"的可行性排序：

| # | 方向 | 新在哪里 | 成本 |
|---|---|---|---|
| F1 | 第一个机器检验的 \|KPI⁺\| 级良序证明（**已得**：[Inacc/Theorem](Inacc/Theorem.lagda.md)，2026-09-12） | formalization first：据我们所知公开的机器检验良序证明最强停在 Γ₀～Bachmann–Howard；distinguished-sets 方法从未进过证明助手 | 低（= P1/P2） |
| F2 | **I-ordinal systems 在 MLTT 里的统一良序定理** | Ordinal Systems Part 2 在 KP 风格集合论里证，并明说 MLTT 版本没做。§4 已经以 `OTFacts` 为参数，即"对任意满足 58 条句法公理的系统，MLTT 内部证其良序"；要做的是把 58 条整理成干净接口（可能就是 I-OS 结构 + 少数几条），证 I-OS 公理 ⟹ `OTFacts` | 中 |
| F3 | **生成器**：从 `Object/Extract` 的参数生成记号系统（语法、序、G、OT）并**连带生成**接口公理的证明 | CONTRACT 的流水线第一次成为能运行的机器对象；方法论上把 §126 的判决（坍缩层一个定理 + 从下面来的层由生成器保证）变成实物 | 中高 |
| F4 | M 层（路线 C）形式化 | 观察：下界证明只在 Lemma 5.10 用 Mahlo 宇宙且只对给定 (f,g) 要子宇宙，V := `Set` 下是普通 IR，Mahlo 宇宙的消去规则从未用到——"到底用了多少 Mahlo"的机器答案 | 高 |
| F5 | 附带小结果 | `OTFacts` = Assumption 4.3 的精确清单；转写中的三处简化（4.16 (a) 不需 A ⊆ M(A)、4.30 不需归纳假设、4.17 (c) 的 κ = I 绕开 4.7 (e)）；B4："对 n 一致"要一层额外宇宙（§129.6） | 已在日志 |

建议顺序 F1 → F2 → F3，M 层随后接上（届时应以同样的接口形式出现）。

## 10. P1 的执行计划（关掉 `OTFacts`）——**全部做出（2026-09-12）**

1. ✅ **机器求值的健全性测试**：[Inacc/FactsCheck](Inacc/FactsCheck.lagda.md)，58 条字段的布尔版在 enumT 3／enumT 4／ots 4／ots 5 上逐条 `refl`（13 s）。
2. ✅ **把 (≺′11) 内联**：[Inacc/Order](Inacc/Order.lagda.md)，每次递归调用严格减小 `len s + len t`。
3. ✅ **燃料充分性**：[Inacc/OrderProps](Inacc/OrderProps.lagda.md)（`n ≥ 3·(len s + len t)` 即稳定）；读出引理 [Inacc/Unfold](Inacc/Unfold.lagda.md)（`lt-unfold`）与 `lt-list`。
4. ✅ **Lemma 2.4**：[Inacc/Linear](Inacc/Linear.lagda.md)（不可反、三分）、[Inacc/Trans](Inacc/Trans.lagda.md)（传递）。在**全部 T′** 上成立。
5. ✅ Remark 2.12 (a)(h)：[Inacc/Lex](Inacc/Lex.lagda.md)、[Inacc/Subterm](Inacc/Subterm.lagda.md)、[Inacc/Facts1](Inacc/Facts1.lagda.md)、[Inacc/Facts2](Inacc/Facts2.lagda.md)。
6. ✅ ã、a⁺、κ⁻、mFi、pFi：[Inacc/Facts1](Inacc/Facts1.lagda.md)、[Inacc/Facts2](Inacc/Facts2.lagda.md)、[Inacc/Facts2b](Inacc/Facts2b.lagda.md)。
7. ✅ Remark 2.15 (c)(d)(e)：[Inacc/Facts3](Inacc/Facts3.lagda.md)。

记录装配：[Inacc/FactsImpl](Inacc/FactsImpl.lagda.md)；无条件定理：[Inacc/Theorem](Inacc/Theorem.lagda.md)。下一步按 §9 的 F2。

---
