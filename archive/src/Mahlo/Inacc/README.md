# Inacc/：方案 A 主线——[Se98] 的 Agda 转写（I 层）

Setzer, *Well-ordering proofs for Martin-Löf type theory* (APAL 1998)：一个宇宙 + W 的类型理论 ML₁W，记号系统 OT_I，端点 ψ_{Ω₁}Ω_{I+ω} = |ML₁W|。V := `Set`。**状态（2026-09-12 深夜）**：§2、§4、§5 全部转写，**`OTFacts` 的 58 条句法事实全部已证并装进记录（[FactsImpl](FactsImpl.lagda.md)）**，Theorem 4.41 与 `𝔑 : ℕ` **无条件**机检（[Theorem](Theorem.lagda.md)：`wellfounded : ∀ n → OT y → y ≺ ψ_{Ω₁}Ω_{I+n} → Acc y`，`𝔑 : ℕ`）。自包含，不 import `Notation/`、`Hierarchy/`（参考其做法但重写）。全部 `--safe --cubical-compatible`。

来龙去脉：[../DECISION.md](../DECISION.md)；计划：[../ROADMAP.md](../ROADMAP.md) §3；日志：[../RESEARCH.md](../RESEARCH.md) §129。

## 模块

| 模块 | [Se98] | 内容 |
|---|---|---|
| `Syntax` | Def 2.2 | T′（和为 snoc 表）、子类谓词、`length`、范数、句法相等、`size`、`NZ` |
| `Order` | Def 2.3 | ≺′ 燃料索引结构递归；`_≺_`、`_⪯_`（记录）；算例 |
| `Closure` | Def 2.6–2.9 | `G_π`、`Cr′`、`C̃`、`isOT`、`OT`（记录） |
| `Arith` | Def 2.10, 2.13 | `+`、`·`、`φ`、`Ω`、`Ωⁿ`、`κ⁻`、`tilde`、`plus`、`mFi`、`pFi`、`mI` |
| `BoolLemmas`、`OTLemmas` | — | 布尔拆合；`isOT` 按形状拆合 |
| `Enum` | — | 按 `size` 枚举全部项／OT 项（`enumT`、`ots`） |
| `FactsCheck` | Assumption 4.3 | 58 条字段的布尔版在小集合上逐条 `refl`（\|enumT 3\|=9、\|enumT 4\|=100、\|ots 4\|=20、\|ots 5\|=197；13 s）——健全性测试，不是证明 |
| `OrderProps` | Def 2.3 | **燃料充分性**：`ltT n s t` 在 `n ≥ 3·(len s + len t)` 时稳定；`lt-list`（和的比较 = 分量表字典序）；`lt-prin` |
| `Unfold` | Def 2.3 | `ltP′`：(≺′3)–(≺′11) 右边以 `lt`／`le` 写出；`lt-unfold : lt ⟨p⟩ ⟨q⟩ ≡ if eqP p q then false else ltP′ p q`——此后不再见燃料 |
| `Linear` | Lemma 2.4 | 反对称＋全（对 `size s + size t` 强归纳；跨形状对是 (≺′11) 的 `refl`）⟹ 不可反、三分、`lt-lin`／`le-lin` 互否等式 |
| `Trans` | Lemma 2.4 | 传递（对 `size` 三元和强归纳）：φ 对 G′ 化到子项；G′ 之间用**键** `(lev, fl)` 的字典序刻画（同 π 的 ψ_π 按参数比较是唯一例外） |
| `Lex` | (≺′1)(≺′2) | 真前缀更小、公共前缀可消、`b ≺ d ≺ b + c ⟹ d = b + d′`、`x + 1 = x ▹ 1`、`+1-least`、`≺+1⇒⪯`、单主元项对和 |
| `Subterm` | Remark 2.12 (h) | 结构下降 `s ◁ t`（φ 两参数、Ω′ 参数、ψ 的**层**、和的首分量；**不含 ψ 的参数**）⟹ `s ≺ t`，双重强归纳；全 T′ 上成立 |
| `Facts1` | 2.12 (h)(f)(g)、(≺′i) 读出、κ⁻、+1、Ω 单调 | 形状视图 `FiView`/`CarView`/`GView`/`SucView`/`ΩView`；`Ω-mono′`、`Ω-mono<`；30 条字段 |
| `Facts2`、`Facts2b` | 2.12 (a)、Def 2.13、2.14 | `+`、`φ` 保持 OT；ã 的五条；a⁺ 的六条（`plus x ≡ ⟨Ω′_{y+1}⟩` 且 `Ω y ≡ ã`）；a^{−Fi} 的极大性 `mFi-max′`；2.14 (g)(i) |
| `Facts3` | Remark 2.15 (c)(d)(e) | `u ≺ κ ⟹ (u ∈ C̃_κ(a) ⟺ u ≺ ψ_κ a)`（对 u 结构归纳，κ 两种形状）；ψ_π d ∈ C̃ 的分解 |
| `FactsImpl` | Assumption 4.3 | `facts : OTFacts`——58 条全部有证明 |
| `Theorem` | Theorem 4.41 | 用 `facts` 实例化 `WO/Main` 与 `FGH`：`wellfounded`、`thm441`、`𝔑`，无任何假设 |
| `WO/K` | Def 5.1–5.4 | `⊗`、`↾`、`K^a`、`C`（记录） |
| `WO/Base` | Def 4.5, 4.12, 4.18, 5.6 | `M`、`τ`、`𝒜`、`𝒲`（归纳族）、`⊑`、`Ag`、`Prog`、`⁺`；Assumption 4.10 |
| `WO/CLemmas` | Lemma 5.5 | C^a(A) 四种形状的展开；K 有界；C 单调 |
| `WO/Facts` | Assumption 4.3 | `record OTFacts`：§4 用到的 58 条句法事实（已由 `FactsImpl` 构造） |
| `WO/OrderLemmas F` | Lemma 2.4 推论 | ⪯ 传递、反对称、全性、`tilde-between` |
| `WO/Lemma47 F` | Lemma 4.7 (a)–(d), 4.9 | C^a(A) 对下标的依赖；M(A) 对 +、φ、Ω 封闭 |
| `WO/Lemma413 F` | Lemma 4.13 (b)(c)(d) | W(A) 只依赖 A 的一段；W(A) ∩ Ω₁ ⊑ OT |
| `WO/Dist F` | Lemma 4.21, 4.24 | 突出集上的归纳；唯一性 |
| `WO/Closed F` | Def 4.14 (a)(c), Lemma 4.16, 4.17 (a) | 弱封闭；`RegView`、`ΩView` |
| `WO/Closed2 F` | Def 4.14 (b)(d), Remark 4.15 | `DC`、`UC`；`sizeRec` |
| `WO/CTilde F` | Def 2.7/2.8 推论 | C̃_κ(a) 沿子项分解；ψ_I y ∉ C̃_I(y) |
| `WO/Lemma47ef F` | Lemma 4.7 (e)(f) | C^a(A) 在 ψ_I 之下的稳定性 |
| `WO/Lemma417b F` | Lemma 4.17 (b) | W(A) ∩ κ⁺ 对 +、φ、Ω、I 封闭；`W⁺-DC`、`W⁺-UC` |
| `WO/Lemma417c F` | Lemma 4.17 (c) | W(A) 对 ψ 封闭 |
| `WO/Lemma423 F`、`Lemma423c F` | Lemma 4.23 | 突出集向下／向上封闭、对 ψ 封闭；Ag(A⁺) |
| `WO/Union F` | Def 4.25, Lemma 4.26–4.29 | `𝕎 := ⋃ Ag 集`（对 `Set` 量化）；Ag(𝕎)；𝕎 的封闭性 |
| `WO/Lemma430 F` | Lemma 4.30 | 从集合 B 把 a 拉进 𝕎（Σ 投影 = AC） |
| `WO/Lemma431 F` | Lemma 4.31 | 𝕎 对 Ω 封闭；ψ_I 0、ψ_I(x+1) ∈ 𝕎 |
| `WO/Gamma F`、`Gamma2 F` | Def 4.32–4.36, 5.8, Lemma 4.34–4.38 | Γ 迭代（集合版，ℕ 到宇宙的大消去）；`𝕎 ∩ I ≅ W(𝕎) ∩ I` |
| `WO/Main F` | Def 4.39, Lemma 4.40, **Theorem 4.41** | 突出类 W_i；`Acc-endpt`：端点以下全部可达 |
| `FGH F` | — | 按 size 枚举、范数基本列 λ[n]（λ[n] ≺ λ 机检）、`F′` 沿 Acc、`BIG n`、`𝔑 : ℕ` |

## 约定

- 每个引理名对应原文编号（`C-tilde` = 4.7 (a) 等），文件头注明。
- `≺`、`⪯`、`OT`、`C` 是单字段记录（`lt!`、`le!`、`ot!`、`c!`），不是裸 `≡ true`——否则隐参推不出。
- 互递归的结构归纳里，和 `(b ▹ p)` 的 `b` 整个传给辅助函数（附 `NZ b`），不在 `with` 后重建 `a ▹ q`（终止检查器看不见，§129.2）。
- 层级多态：`Pred ℓ = Tm → Set ℓ`；「集合 P(N)」是 `Pred 0ℓ`。
- 关于 `lt` 的推理一律先经 `lt-unfold`／`lt-list` 化到 `ltP′`／字典序，不碰燃料；`unf`、`unf⁻`（[Trans](Trans.lagda.md)）是 `≡ true` 版本。
- `with` 只放小项（`caseEq (…)`、变量上的 `∨-true`）；含 `unf`、`lt-unfold`、`φ≺Car (carψ zer) …` 这类会归约成大证明项的东西一律先绑定到 `where`／参数再用（否则检查超时或内存被杀，§131）。
- 只由展开后的目标决定的隐参解不出：用显式参数版 `∨ˡ x y`、`∧ⁱ x y`、`leˡ s t`、`≤′ (size X)`、`if-true {b = …} {x = …} {y = …}`。
- 嵌套 `with` 之后外层的兄弟子句要把完整 LHS 重写一遍（`...` 指最内层）。
