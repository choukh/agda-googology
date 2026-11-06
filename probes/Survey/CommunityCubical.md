# 社区 Cubical Agda 项目调研: CuST 与 CuST-DecZero

> 调研日期 2026-11-01. 对象是两个本地快照目录 (无 `.git`, 只读, 未构建):
> `<本地>/agda-cubical-set-theory-main` (下称 **CuST**) 与 `<本地>/agda-cubical-dec-zero-main` (下称 **DecZero**).
> 下文凡说"它们的代码"的地方都给出 `文件:行号`, 路径相对于各自项目根目录; 涉及我方的文件用 `probes/...`/`src/...` 写明.
> 标 **(推断)** 的句子是对意图或来源的推测, 不是从代码直接读出的事实.

## 概要

1. **CuST** (约 2991 个 `.agda` 文件, 约 30.6 万行) 是"在 Cubical Agda 里做 Cantor 式物质集合论"的项目. 它的序数是 HoTT 书式的**商序数**: 良序集按序同构做集合商 (`src/CST/Ordinal/Base.agda:18-45`). 一般的 Veblen、上确界、最小点都以"同层排中律判定器" `PropositionDecider5` 为参数, 并有机器证明说这些后端与该层 LEM 等价. 它的 "agda-googology 接入" (ψ、BTBO、FGH) 基本上是**契约记录**: 数据与证明都由调用者提供, 仓库里没有 FGH 的实现 (`docs/CuSTgoogology总结报告.md:13`). 真正的树型载体只有几种: 有限代码 (`B5Code`、`VeblenTerm5`、`BTBOTerm5`, 极限只能按编号引用)、退役目录里的 `{seed, succ, ω}` 三构造子类型, 以及**照抄我方 `Ordᴰ` 的 `OrdD`** (`src/CST.Old/Ordinal/BTBOCode.agda:16-29`).
2. **DecZero** (约 1471 个文件, 约 15 万行, 依赖 CuST) 的主题是 Conway 博弈、超现实数、超复数的可判等 ("DecZero"). 序数部分约 2.5 万行, 用作选项来源. 其中有一套**严格单调的布劳威尔树** `BoundedTree` (`src/VeblenOrdinal/Controlled/BoundedTree.agda:18-31`). 注释写明它移植自我方 `OCF/BTBO.lagda.md` 的 `BoundedTrich`, 修订号 `9786181` (CC BY-NC-SA 4.0). 在此之上有 ω^α、ε₀, 以及我方**修补前**的 BTBO 程序的逐行移植 (`BTBOSource.agda`). 它还有一个不用判定器的语义解释: 把树映到 CuST 的商序数. 借助这个解释, 它证明了 ω^ε₀ = ε₀ 这一等式的语义版, 也证明了累积和 (cumsum) 会改变序数的值、不保持最小上界 (`BTBOSourceBoundary.agda:21-66`).
3. 两个项目所有源文件都是 `--cubical --safe --guardedness` (部分另加 `--lossy-unification`). 没有 `postulate`、`TERMINATING`、`NO_POSITIVITY_CHECK`, 也没有洞 (全文 grep, 命中只在注释里). 两者的文档都含有 ChatGPT 会话的导出 (CuST `docs/CuST开发计划.md:1`, DecZero `docs/形式化Conway博弈.md:1`). 开发日志里有大量资源闸门与 "Gap/Boundary" 记录. **(推断)** 两个项目主要由 LLM 代理按计划文档推进.
4. **对我方最有用的三点.** (a) DecZero 用另一种基础 (cubical 商序数) **独立复现**了我方 Cumsum 的结论: cumsum 改变值 (`TheoriesNoCumulativeStagewiseLUB`、`TheoriesCumulativeNotAdditive`). (b) DecZero 的 `TheoriesNoRawCommonBound` 与我方 Level §2 的 `lit→ext` 互为镜像. 在严格的 `Ordᴰ` 式下标里, 同值而表示不同的两个 ω 根本**没有公共上界**; 我方的 `Ordᴵ` 允许它们有公共上界, 代价是三歧性只能模 ≅. 这为 Ordᴵ 的设计提供了一个精确的对照理由. (c) CuST 把"外延的 (商) 序数上的比较、最小点、Veblen"都机器证明为等价于 LEM, 并因此把它们参数化. 这正是我方壁垒定理在外延一侧的对应物. 它说明 cubical 商**不能**换回三歧性, 代价是 LEM 加上失去 FGH. 它与我方结论一致, 没有反驳我方.
5. **没有可以让我们跳过的阶段.** 两个项目都没有 Buchholz 式记号的标准形理论、Bachmann 性质、记号与树之间的序对应. 能无条件 (不靠判定器、不靠调用者证书) 到达的最高序数是 DecZero 的 ε₀. 我方的 ψ₀(Ω_Ω) 对角线、`Uniform`、`Bachmann.lagda.md` 的 `Generic` 在它们那里都没有对应物.

---

## 项目一: CuST (`agda-cubical-set-theory-main`)

DecZero 依赖它 (`dec-zero.agda-lib` 的 `depend: cubical cst`), 所以先讲它.

### 1.1 目的、基础、规模、成熟度

- **目的.** `README.md:1-7`: 研究 `hSet` 与 ZFC 小初始段的相似程度, 做"Cantor 谱系的物质集合论"; 计划依次做序数、序数宇宙多态、基数、ℵ/ℶ、不动点、内模型 (`README.md:11-20`, 只有"Levels for Ordinals Universe Polymorphism"一项打勾). `docs/CuST开发计划.CuSTgoogology.md:5` 另立"F 路线": "将 `../agda-googology` 的 Veblen、`WellFormed` 和 `OCF/BTBO` 序数操作接入 CuST 的序数载体". 也就是说, 它明确以**我方 src** 为参照.
- **基础.** Agda 2.8.0、standard-library-2.4、cubical-0.9 (`README.md:22-26`). 库文件写的是 `flags: --cubical --safe --guardedness --lossy-unification` (`agda-cust.agda-lib:4`). 源文件中 2565 个是 `--cubical --safe --guardedness`, 426 个另加 `--lossy-unification`. 用到的 cubical 特性有: 集合商 (`Ordinal` 的定义)、命题截断 (`∥_∥₁`, 遍布序关系)、univalence (由序同构得到良序集相等, 用于从商中取回代表元, `src/CST/Ordinal/OrdinalRepresentativeRecovery5.agda:4-7, 21-31`).
- **规模.** 2991 个文件, 约 306 千行 Agda, 外加约 5 万行计划与日志 (`docs/*.md`). 按目录: `CST/Ordinal` 541 个、`CST.Middle/.../Ordinal` 608 个、退役的 `CST.Old` 约 660 个. 文件名含 BTBO 的 236 个, 含 Veblen 的 170 个, 含 Buchholz 的 95 个. 有 863 个文件出现 `PropositionDecider5`.
- **成熟度与构建声明.** `CST.All` 冷构建 304–345 s、约 3.9 GiB (`docs/CuSTgoogology总结报告.md:165`). 曾出现 47.3 GiB RSS 的接口失败 (同文件 `:164`). "第五代载体"总体**未完成**: 四个概览闸门关闭 0/4, V0 的八项关闭条件 0/8; 已记录热构建超时 654 次 (`docs/CuST开发计划.第5代序数载体覆盖面进度总览3.md:25, 28`). "下一代载体" B/C/D/E 四条路线 (QIIT、归纳-归纳 `Ord+Cmp`、比较博弈、结构化良序) 的正式实现都是 0/5 (`docs/CuSTgoogology总结报告.md:206-215`; `docs/下一代序数载体研究.md:16`).
- **作者与日期.** 快照里没有 git 历史, 也没有 LICENSE 文件. 文档中的日期从 2026-09-26 到 2026-10-26, 本地路径是 `/home/admin-wsl/Agda/agda-cust` (DecZero `docs/CuSTDecZero开发计划A3.md:38`). 作者姓名未见.

### 1.2 序数载体: 精确定义

**(i) 主载体: 商序数.** 良序集 (`WellOrder` 带有**截断的**全序性) 按"存在序同构"做集合商.

```agda
-- src/CST/Order/Relations.agda:33-39
record LinearOrder {ℓA} (A : SetObject ℓA) (ℓR : Level)
                   : Type (ℓA ⊔ lsuc ℓR) where
  field
    partialOrder : PartialOrder A ℓR
    total : (x y : Carrier A)
          → ∥ Relates (_≤_ (preorder (partialOrder))) x y
            ⊎ Relates (_≤_ (preorder (partialOrder))) y x ∥₁
```

```agda
-- src/CST/Ordinal/Base.agda:18-45
record WellOrderedSet (ℓ : Level) : Type (lsuc ℓ) where
  field
    orderedCarrier : SetObject ℓ
    ordering : WellOrder orderedCarrier ℓ

OrderIsomorphic : ∀ {ℓ} → WellOrderedSet ℓ → WellOrderedSet ℓ → PropObject ℓ
OrderIsomorphic X Y =
  ∥ OrderIso (ordering X) (ordering Y) ∥₁ , squash₁
...
OrdinalSet : (ℓ : Level) → SetObject (lsuc ℓ)
OrdinalSet ℓ = RawEquivalenceQuotient (WellOrderedSet ℓ) (WellOrderEquivalence ℓ)

Ordinal : (ℓ : Level) → Type (lsuc ℓ)
Ordinal ℓ = Carrier (OrdinalSet ℓ)
```

序 `OrdinalLe`/`OrdinalLt` 是"存在 (真) 初始段映射"的命题 (`src/CST/Ordinal/Comparison.agda:236, 241`). 这是**外延**的序, 在商上定义.

**(ii) 一般 Veblen 与它的逻辑前提.**

```agda
-- src/CST/Ordinal/WellOrderLeast5.agda:26-27
PropositionDecider5 : (ℓ : Level) → Type (lsuc ℓ)
PropositionDecider5 ℓ = (P : PropObject ℓ) → Dec (Statement P)

-- src/CST/Ordinal/VeblenEnumeration5.agda:29
veblen5 : ∀ {ℓ} → PropositionDecider5 ℓ → Ordinal ℓ → Ordinal ℓ → Ordinal ℓ
```

对应的边界定理 (都是双向的):

```agda
-- src/CST/Ordinal/WellOrderLeastLogicalBoundary5.agda:65, 69
wellOrderLeastPointImpliesLEM5 : ∀ {ℓ : Level} → WellOrderLeastPointBackend5 ℓ → PropositionDecider5 ℓ
lemImpliesWellOrderLeastPoint5 : ∀ {ℓ : Level} → PropositionDecider5 ℓ → WellOrderLeastPointBackend5 ℓ

-- src/CST/Ordinal/DecidablePresentationWeakBoundary5.agda:57, 63
decidablePresentationWeakImpliesLEM5 : ∀ {ℓ : Level} → DecidablePresentationWeakBackend5 ℓ → PropositionDecider5 ℓ
lemImpliesDecidablePresentationWeak5 : ∀ {ℓ : Level} → PropositionDecider5 ℓ → DecidablePresentationWeakBackend5 ℓ
```

第二对定理说: 即使每个良序集自身的元素相等和序都可判定, 判定两个序数之间的 ≤ 仍等价于 LEM. 证明用的是序数 2 与 1+P (`src/CST/Ordinal/FiniteOrdinalWeakDecisionBoundary5.agda:4-6`). 同族索引的上确界同样要判定器 (`src/CST/Ordinal/SmallDeciderIndexedSupremum5.agda:4-7`).

**(iii) 有限代码 (当前活动树).** 极限不存 `ℕ → _`, 只存编号. 注释明说这样做是为了保持严格正性.

```agda
-- src/CST/Ordinal/B5Code.agda:32-40
data LimitCode5 : Type where
  finiteLimit5 : ℕ → LimitCode5

data B5Code : Type where
  seedCode5 : B5Code
  successorCode5 : B5Code → B5Code
  limitCode5 : LimitCode5 → B5Code
```

```agda
-- src/CST/Ordinal/CIGVBTBOCarrier5.agda:20-34
data VeblenTerm5 : Type where
  veblenZero5 : VeblenTerm5
  veblenSuccessor5 : VeblenTerm5 → VeblenTerm5
  veblenPhi5 : ℕ → VeblenTerm5 → VeblenTerm5 → VeblenTerm5
  veblenIndexedPhi5 : LimitRef5 → VeblenTerm5 → VeblenTerm5
  veblenLimit5 : LimitRef5 → VeblenTerm5

data BTBOTerm5 : Type where
  btboZero5 : BTBOTerm5
  btboSuccessor5 : BTBOTerm5 → BTBOTerm5
  btboSum5 : BTBOTerm5 → BTBOTerm5 → BTBOTerm5
  btboOmega5 : ℕ → BTBOTerm5
  btboCollapse5 : CollapseRef5 → BTBOTerm5
```

这些代码的语义 (阶段函数、上确界、严格性) 全部放在外部的"证书"记录里, 由调用者提供 (`src/CST/Ordinal/NextCarrierLimitCode.agda:3-6, 89-97` 的注释与 `LimitCodeSemantics`).

**(iv) 退役目录 `CST.Old` 中的树型载体.** `CST.Old` "never imported by CST.All" (`src/CST/Old.agda:4`), 其中有:

```agda
-- src/CST.Old/Ordinal/NextCarrierBOmegaCore.agda:11-14
data GenBOmega : Type lzero where
  seedBOmega : GenBOmega
  succBOmega : GenBOmega → GenBOmega
  omegaB : GenBOmega
```

```agda
-- src/CST.Old/Ordinal/BTBOCode.agda:13-29  (注释: "A direct CST-owned code for the upstream Ordᴰ shape")
mutual
  data OrdD : Type lzero where
    zeroD : OrdD
    sucD : OrdD → OrdD
    limD : (f : ℕ → OrdD) → monotonic f → OrdD

  data _<_ : OrdD → OrdD → Type lzero where
    less-zero : ∀ {a} → a < sucD a
    less-suc : ∀ {a b} → a < b → a < sucD b
    less-lim : ∀ {a} {f : ℕ → OrdD} {mono : monotonic f}
      → (n : ℕ) → a < f n → a < limD f mono

  monotonic : (ℕ → OrdD) → Type lzero
  monotonic f = ∀ {n m} → n <ᴺ m → f n < f m
```

以及把 `limᵢ` 去函数化的分层项, 代价是失去分支函数:

```agda
-- src/CST.Old/Ordinal/BTBOMapCode.agda:12-29
  data LayerTerm : OrdD → Type where
    layerZero : ∀ {ℓ} → LayerTerm ℓ
    layerSuc : ∀ {ℓ} → LayerTerm ℓ → LayerTerm ℓ
    layerLimNat : ∀ {ℓ} → LayerNatLimitCode ℓ → LayerTerm ℓ
    layerLimIndexed : ∀ {i ℓ} → i < ℓ
      → LayerMapCode i ℓ → LayerTerm ℓ
  ...
  data LayerMapCode : OrdD → OrdD → Type where
    layerMapId : ∀ {ℓ} → LayerMapCode ℓ ℓ
    layerMapLift : ∀ {i ℓ} → i < ℓ → LayerMapCode i ℓ
    layerMapCompose : ∀ {i j k}
      → LayerMapCode j k → LayerMapCode i j → LayerMapCode i k
    layerMapConst : ∀ {i ℓ} → LayerTerm ℓ → LayerMapCode i ℓ
```

总结报告给出的理由是: 把 `LayerTerm i → LayerTerm ℓ` 放进构造子会 `NotStrictlyPositive` (`docs/CuSTgoogology总结报告.md:147`). 这说明它没有采用我方 src 的归纳-递归技巧 (`U` 对证明递归). 那个技巧恰好能让分支函数的定义域是一个先定义好的较小类型.

**(v) BTBO 与 FGH: 只有契约.**

```agda
-- src/CST/Ordinal/FixedPointBTBO5.agda:56-63
record OmegaFixedPointWitness5 {V : Type ℓV}
  (isSetV : isSet V)
  (F : V → V) (seed : V) (chainLimit : (ℕ → V) → V)
  : Type (lsuc ℓV) where
  field
    iteration5 : OmegaIteration5 F seed chainLimit
    limitFixedEvidence5 : Statement
      (FixedPointStatement5 isSetV F (omegaIteration5 iteration5))
```

```agda
-- src/CST/Ordinal/FGHConsumer5.agda:16-28
record FGHConsumerContract5 {Index : Type ℓI} {V : Type ℓV}
  (growth : Index → V → V)
  (limit : (ℕ → V) → V)
  (seed output : V)
  : Type (lsuc (ℓI ⊔ ℓV)) where
  field
    growthIndex5 : Index
    stages5 : ℕ → V
    stageZeroPath5 : stages5 zero ≡ seed
    stageSuccessorPath5 : (n : ℕ)
      → stages5 (suc n) ≡ growth growthIndex5 (stages5 n)
    outputPath5 : limit stages5 ≡ output
```

`certifiedBTBOContract5` (`src/CST/Ordinal/BTBOConstruction5.agda:39-60`) 的 ψ、种子、极限、链、上确界证明、BTBO 值都是**参数**. 文件里没有构造任何具体的 ψ.

### 1.3 序、三歧性与已证内容

- **序.** 商序数上是外延序 (初始段映射). 有限代码上的比较是带"健全性路径"的标签 (`B5Family.decisionB5`, `src/CST/Ordinal/B5Code.agda:93-99`). `OrdD` 上是结构子项序.
- **三歧性.** 商序数上没有一般的三歧性, 等价于 LEM (见 1.2(ii)). `OrdD` 上证了有界三歧 (`src/CST.Old/Ordinal/BTBOCode.agda:41-55`, 等号分支用的是 `subst`, 不是对 refl 做模式匹配). 还证了**无界**三歧可反驳:

```agda
-- src/CST.Old/Ordinal/BTBOUnboundedBoundary.agda:60-64, 89-102
limitNat = limD natD natD-mono
limitShiftedNatD = limD shiftedNatD shiftedNatD-mono
...
record UnboundedOrdDTrichotomy : Type lzero where
  field
    compare : (a b : OrdD)
      → (a < b) ⊎ ((b < a) ⊎ (a ≡ b))

unboundedOrdDTrichotomy-impossible :
  UnboundedOrdDTrichotomy → ⊥
```

  这个反例用的是两个内涵上不同、外延上都等于 ω 的极限. 它与我方 `probes/OCF/Barrier.lagda.md` 的"朴素 Ord₁ 可反驳"属于同一类 (只对内涵等号成立), 比壁垒定理弱: 它不涉及 Ω-共尾元, 也不推出 LPO.
- **无条件到达的强度.** 有限 Veblen 与 ω² 的专用实例 (`docs/CuSTgoogology总结报告.md:9-12`). 有 `ψ(Ω₀)` 的"零层"生产者 (同文件 `:37`). 其余的 ε/ζ/η、ψ、ψ₀、BTBO 都是"给定证书后可用" (同文件 `:64-128`, 第 2 节"有条件可以达成的结果"). Cantor 标准形只到 ω^ω 以下 (`src/CST.Middle/CST/Middle/Ordinal/CantorNormalCode5.agda:22-24`).
- **在判定器参数下.** `veblen5` 接受任意秩, 所以形式上有一切 φ_α(β) (以 LEM 为参数). 未找到 Γ₀、BHO 或其他更高序数的构造 (grep `Gamma0|Γ₀|Feferman|Bachmann-Howard` 无命中).
- **负面结果.** 多数是"自动后端"不可实现的简单反例. 例如任意 `ℕ → Ordinal` 不能都是严格基本列 (常零序列给出 0<0), 任意 `F` 的 ω 迭代不必是不动点 (`docs/CuSTgoogology总结报告.md:131-143`).

### 1.4 对我们遇到的五个问题的处理

| 问题 | CuST 的处理 |
|---|---|
| 严格递增与非严格步进 | 商序数上用"初始段映射链" `IncreasingOrdinalSequence` (`src/CST/Ordinal/ChainLimit.agda:19-38`); 严格性作为证书字段. 不涉及树的步进证据 |
| 层间提升 | 分层只在退役的 `LayerTerm`/`LayerMapCode` 中出现 (去函数化); 活动树里"层"多指 universe level, 用 transport 记录 |
| 下标中的证明相关性 | 商与截断让证明无关 (`isProp`); `OrdD` 的 `monotonic` 证据是相关的, 但只用于退役代码 |
| 下标的可判定比较 | 有限代码用标签加健全性证明; 商序数上等价于 LEM (定理) |
| LPO 壁垒 | 未提及我方的壁垒或 de Jong 等人的文章 (全文 grep 无命中). 外延一侧的对应物是 LEM 边界 |

---

## 项目二: CuST-DecZero (`agda-cubical-dec-zero-main`)

### 2.1 目的、基础、规模、成熟度

- **目的.** 在 Cubical Agda 中形式化 Conway 博弈、超现实数 (AS/TS)、超复数 (ASC/DZSC), 目标是对受控代码得到可计算的四歧比较 (博弈)、三歧比较 (数) 与判零 (`docs/CuSTDecZero开发计划A1.md:1-12`; `docs/CuSTDecZero开发计划A4.md:13-16`). 序数是**选项来源**: Veblen/BTBO 代码构成第 0 层受控博弈 `QG₀` (`docs/CuSTDecZero开发计划A4.md:3-11`). 其余目录 `PrimeAdic`、`Real`、`On-p`、`LoopyGame` 等与本调研无关.
- **基础.** 依赖 cubical 与 CuST, 固定在 CuST 提交 `e67753bf` (`docs/构建工作流.md:6-8`). 库文件 `flags: --lossy-unification` (`dec-zero.agda-lib:4`). 正式检查用 `--no-libraries --cubical --safe --guardedness` (`docs/构建工作流.md:13-14`). 源文件中 1426 个是 `--cubical --safe --guardedness`, 45 个另加 `--lossy-unification`.
- **规模.** 1471 个文件, 约 150 千行. `VeblenOrdinal`/`TrichotomyOrdinal` 两个目录约 25 千行 (含 153 个适配器文件).
- **成熟度与构建声明.** A1 文档记录的是 309 个模块时的冷 gate: 312 s、约 1.2 GiB RSS (`docs/CuSTDecZero开发计划A1.md:37, 50`). 当前文件数已是它的近五倍. A4 的 G0–G8 闸门全部打勾 (`docs/CuSTDecZero开发计划A4.md:283-291`). 但 BTBO 的"来源覆盖" (语义桥) 明确**未完成** (同文件 `:100-104`).
- **作者与日期.** 文档日期 2026-10-13 至 2026-10-30. 无 git 历史, 无 LICENSE. `docs/形式化Conway博弈.md:1` 是 ChatGPT 会话导出.

### 2.2 树型序数: 精确定义

**(i) 严格单调的布劳威尔树 (我方 `Ordᴰ` 的移植).**

```agda
-- src/VeblenOrdinal/Controlled/BoundedTree.agda:3-6 (注释)
-- Algorithm reference: agda-googology, OCF/BTBO.lagda.md, BoundedTrich,
-- revision 9786181208115539beac8af28e2d59d7c76aa530 (CC BY-NC-SA 4.0).
-- This Cubical implementation raises both limit references to a later common
-- stage. It does not transport code indices along an equality of naturals.

-- 同文件 :18-31
mutual
  data BoundedTree : Set where
    treeZero : BoundedTree
    treeSuc : BoundedTree → BoundedTree
    treeLimit : (stages : ℕ → BoundedTree) → srcStrictTreeFamilyQ stages → BoundedTree

  data srcTreeLtQ : BoundedTree → BoundedTree → Set where
    treeStep : ∀ {a} → srcTreeLtQ a (treeSuc a)
    treeNext : ∀ {a b} → srcTreeLtQ a b → srcTreeLtQ a (treeSuc b)
    treeBelowLimit : ∀ {a stages strict} (n : ℕ) → srcTreeLtQ a (stages n)
      → srcTreeLtQ a (treeLimit stages strict)

  srcStrictTreeFamilyQ : (ℕ → BoundedTree) → Set
  srcStrictTreeFamilyQ stages = (m n : ℕ) → m < n → srcTreeLtQ (stages m) (stages n)
```

有界三歧的写法与我方不同. 它不比较 n 与 m, 而是把两边都抬到公共的更后一项 `suc (max n m)` 再递归, 因此不需要在 ℕ 的相等上做模式匹配:

```agda
-- BoundedTree.agda:56-67
funTreeCompareWithin : ∀ {a b bound} → srcTreeLtQ a bound → srcTreeLtQ b bound → TreeComparison a b
funTreeCompareWithin treeStep treeStep = treeEqual refl
funTreeCompareWithin treeStep (treeNext q) = treeGreater q
funTreeCompareWithin (treeNext p) treeStep = treeLess p
funTreeCompareWithin (treeNext p) (treeNext q) = funTreeCompareWithin p q
funTreeCompareWithin {bound = treeLimit stages strict} (treeBelowLimit n p) (treeBelowLimit m q) =
  funTreeCompareWithin {bound = stages (suc (max n m))}
    (TheoriesTreeLtTrans p (strict n (suc (max n m)) ...))
    (TheoriesTreeLtTrans q (strict m (suc (max n m)) ...))
```

良基性 `TheoriesTreeLtWellFounded` (`:38-44`) 用的是 Cubical 库的 `WF`.

**(ii) 算术、ω^α、ε₀ (都在树上构造, 严格性一并证明).** 有 `funTreeAdd` 与它的严格单调性 (`BoundedTreeArithmetic.agda:14-25`). "相邻严格推出处处严格"的 `TheoriesTreeAdjacentStrict` (`:47-55`), 我方称之为"步进". cumsum 单调化:

```agda
-- BoundedTreeArithmetic.agda:61-63, 74-75
funTreeCumulative : (ℕ → BoundedTree) → ℕ → BoundedTree
funTreeCumulative stages zero = stages zero
funTreeCumulative stages (suc n) = funTreeAdd (funTreeCumulative stages n) (treeSuc (stages (suc n)))
...
funTreeCumulativeLimit stages = treeLimit (funTreeCumulative stages) (TheoriesTreeCumulativeStrict stages)
```

ω^α 用"右乘 ω"做后继步 (`BoundedTreeOmegaPower.agda:33-37`). ε₀ 是 ω 塔的极限 (`BoundedTreeEpsilonZero.agda:33-34`).

**(iii) 我方 BTBO 程序的移植 (修补前版本).**

```agda
-- src/VeblenOrdinal/Controlled/BTBOSource.agda:4-8 (注释)
-- Algorithm source: agda-googology, OCF/BTBO.lagda.md, Ord-Ord,
-- revision 9786181208115539beac8af28e2d59d7c76aa530 (CC BY-NC-SA 4.0).
-- Equality of level indices is handled by Cubical transport rather than
-- matching on refl. The source's cumulative Ord-zero to Ord-D transform
-- is retained as such; it is not assumed to preserve every ordinal value.

-- 同文件 :14-26
module _ (level : BoundedTree)
  (Below : (i : BoundedTree) → srcTreeLtQ i level → Set) where
  data SourceTreeLayer : Set where
    sourceZero : SourceTreeLayer
    sourceSuc : SourceTreeLayer → SourceTreeLayer
    sourceLimit : (ℕ → SourceTreeLayer) → SourceTreeLayer
    sourceIndexedLimit : {i : BoundedTree} (below : srcTreeLtQ i level)
      → (Below i below → SourceTreeLayer) → SourceTreeLayer

SourceTreeBelow : {level : BoundedTree} (i : BoundedTree) → srcTreeLtQ i level → Set
SourceTreeBelow i treeStep = SourceTreeLayer i SourceTreeBelow
SourceTreeBelow i (treeNext below) = SourceTreeBelow i below
SourceTreeBelow i (treeBelowLimit n below) = SourceTreeBelow i below
```

折叠的派发:

```agda
-- BTBOSource.agda:82-96
funSourcePsiBelow {i = i} p (sourceIndexedLimit {i = j} q family) = finish (funTreeCompareWithin q p)
  where
  finish : TreeComparison j i → SourceTree i
  finish (treeLess jBelowI) = sourceIndexedLimit jBelowI (λ x → funSourcePsiBelow p
    (family (funSourceCastBelow {i = j} {p = jBelowI} {q = q} x)))
  finish (treeGreater iBelowJ) = funSourceLeastFixed (λ x → funSourcePsiBelow p
    (family (funSourceAsBelow q (funSourceLift iBelowJ x))))
  finish (treeEqual same) = funSourceLeastFixed (λ x → funSourcePsiBelow p
    (family (funSourceAsBelow q (subst SourceTree (sym same) x))))

funSourcePsiZero : {level : BoundedTree} → SourceTree level → SourceTree treeZero
funSourcePsiZero {level = treeZero} code = code
funSourcePsiZero {level = treeSuc level} code = funSourcePsiZero (funSourcePsiBelow treeStep code)
funSourcePsiZero {level = treeLimit stages strict} code = sourceLimit (λ n →
  funSourcePsiZero (funSourcePsiBelow (TheoriesTreeStageBelowLimit stages strict n) code))
```

`treeGreater` 分支是 `lfp (ψ_p ∘ f ∘ ↑)`, `funSourcePsiZero` 是逐层复合加极限层对角. 这与我方 `src/OCF/BTBO.lagda.md` 在修订 `9786181` 时的写法逐行对应. 也就是说, 它正是我方 2026-11-01 四行补丁**之前**的版本 (`git diff 9786181 HEAD -- src/OCF/BTBO.lagda.md` 中被删除的 `lfp (ψ< p ∘ f ∘ coe₀ ∘ ↑ i<j)` 与 `ψ₀ (ψ< zero a)`). 按我方 `probes/OCF/Align/BTBOSemantics.lagda.md` 的分析 (`ψΩ-flat`, 第 208 行起), 这个版本的值**估计**是 ψ₀(Ω_ω) = Buchholz 序数, 不是 ψ(Ω_Ω). DecZero 自己也只声明它是"原始程序", 不声称语义等同 (`docs/CuSTDecZero开发计划A4.md:100-104`).

**(iv) 到商序数的语义解释 (不用判定器).**

```agda
-- src/VeblenOrdinal/Controlled/BoundedTreeSemantics.agda:24-36, 57-62
mutual
  funTreeRepresentative : (ℓ : Level) → BoundedTree → WellOrderedSet ℓ
  funTreeRepresentative ℓ treeZero = emptyWellOrderedSet ℓ
  funTreeRepresentative ℓ (treeSuc code) = appendSuccessor (funTreeRepresentative ℓ code)
  funTreeRepresentative ℓ (treeLimit stages strict) = ChainLimit (funTreeChain ℓ stages strict)

  funTreeChain : (ℓ : Level) (stages : ℕ → BoundedTree) (strict : srcStrictTreeFamilyQ stages)
    → IncreasingOrdinalSequence ℓ
  funTreeChain ℓ stages strict = omegaIndexChainFromStages5 (λ n → funTreeRepresentative ℓ (stages n))
    (λ n → ∣ funTreeStrictMap ℓ (strict n (suc n) ≤-refl) ∣₁)

  funTreeStrictMap : (ℓ : Level) {a b : BoundedTree} → srcTreeLtQ a b
    → ProperInitialSegmentMap (funTreeRepresentative ℓ a) (funTreeRepresentative ℓ b)
...
funTreeValue : (ℓ : Level) → BoundedTree → Ordinal ℓ
funTreeValue ℓ code = ordinalOf (funTreeRepresentative ℓ code)

TheoriesTreeStrictValue : (ℓ : Level) {a b : BoundedTree} → srcTreeLtQ a b
  → Statement (OrdinalLt (funTreeValue ℓ a) (funTreeValue ℓ b))
```

每个代表元的序都可判定 (`funTreeOrderDecision`, `:51-54`). 结构严格序被映为语义严格序. 只证了这一个方向: 没有反映 (reflect) 定理, 也没有"语义相等推出结构 ≅"的定理.

### 2.3 已证内容与到达强度

- **ε₀ 不动点 (语义, 无判定器):**

```agda
-- BoundedTreeEpsilonZeroSemantics.agda:32-33
TheoriesTreeEpsilonZeroFixed : (ℓ : Level)
  → funTreeValue ℓ (funTreeOmegaPower funTreeEpsilonZeroCode) ≡ funTreeValue ℓ funTreeEpsilonZeroCode
```

  ε₀ 是本调研所见**无条件**到达的最高序数. 另有 φ₀ 片段 `PhiZeroCode` (自然数与 ω 两种参数, `src/VeblenOrdinal/Controlled/PhiZero.agda:34-36`), 以及 ω³ 以下的可判定秩 `OmegaCubeRank` (`src/TrichotomyOrdinal/OmegaCubeRank.agda:14-19`).
- **同值不同表示, 且没有原始公共上界:**

```agda
-- BoundedTreeBoundary.agda:41, 52-53, 61-62
TheoriesOmegaAndShiftedHaveDifferentSyntax : ¬ (funTreeOmega ≡ funShiftedTreeOmega)
TheoriesNoRawCommonBound : ¬ (Σ BoundedTree (λ bound →
  srcTreeLtQ funTreeOmega bound × srcTreeLtQ funShiftedTreeOmega bound))
TheoriesShiftedOmegaValue : (ℓ : Cubical.Foundations.Prelude.Level)
  → funTreeValue ℓ funTreeOmega ≡ funTreeValue ℓ funShiftedTreeOmega
```

- **cumsum 改变值:**

```agda
-- BTBOSourceBoundary.agda:21-22, 35-38, 61-63
TheoriesCumulativeZeroLimitPositive : (ℓ : Level)
  → Statement (OrdinalLt (zeroOrdinal {ℓ}) (funTreeValue ℓ (funSourceMonotone funSourceZeroLimit)))
TheoriesNoCumulativeStagewiseLUB : (ℓ : Level) → ¬
  ((stages : ℕ → SourceTree treeZero) (upper : Ordinal ℓ)
    → ((n : ℕ) → Statement (OrdinalLe (funTreeValue ℓ (funSourceMonotone (stages n))) upper))
    → Statement (OrdinalLe (funTreeValue ℓ (funSourceMonotone (sourceLimit stages))) upper))
TheoriesCumulativeNotAdditive : (ℓ : Level) → ¬
  ((a b : SourceTree treeZero) → funTreeValue ℓ (funSourceMonotone (funSourceAdd a b))
    ≡ ordinalAddition (funTreeValue ℓ (funSourceMonotone a)) (funTreeValue ℓ (funSourceMonotone b)))
```

- **一般 Veblen.** 照搬 CuST 的 `veblen5`, 保留判定器参数. 文档登记了"消除判定器"未完成 (`docs/CuSTDecZero开发计划A3.md:86-104`).

### 2.4 对五个问题的处理

| 问题 | DecZero 的处理 |
|---|---|
| 严格递增与非严格步进 | 树的极限要求全对严格 (`srcStrictTreeFamilyQ`), 用相邻严格加 `TheoriesTreeAdjacentStrict` 补齐; 对 ψ 的输出用 cumsum (`funSourceMonotone`) 单调化, 并自证这一步改变值 |
| 层间提升 | `funSourceLift` 对树递归, 遇 `sourceIndexedLimit` 用传递性改写下标 (`BTBOSource.agda:46-51`), 与我方 src 的 `↑` 同构 |
| 下标中的证明相关性 | 族 `SourceTreeBelow` 对推导递归; 不同推导给出的族用路径 `TheoriesSourceBelowPath` 连起来 (`:31-37`), 再 `transport`. 这一步在 `--without-K` 下同样能做 (类型间的 `≡` 由 refl 归纳得到, `subst id` 即可), cubical 不是必需 |
| 下标的可判定比较 | 结构的有界三歧, 包含字面等号分支; 公共上界必须是原始树上的推导. 同值的两个 ω 没有公共上界, 所以无法比较 |
| LPO 壁垒 | 计划中明令排除 `PropositionDecider5`、LPO、Choice 作为生产接口的输入 (`docs/CuSTDecZero开发计划A4.md:30`); 没有涉及 Ω-共尾下标 |

---

## 树序数定义对照表

| 类型 (位置) | 序 | 三歧性 | 基本列单调性 | 提升 | 折叠 | 到达强度 | 基础假设 |
|---|---|---|---|---|---|---|---|
| CuST `Ordinal ℓ` = 良序集 / 序同构 (`CST/Ordinal/Base.agda:41-45`) | 外延 (初始段映射, 截断) | 一般比较 ⇔ LEM (`DecidablePresentationWeakBoundary5.agda:57,63`) | 链由初始段映射给出, 严格性是证书 | universe 间 transport | 无具体 ψ; 只有契约 (`FixedPointBTBO5.agda:56`) | 无条件: 有限 Veblen、ω²; 以 LEM 为参数: 任意秩 φ | cubical 集合商、截断、univalence; LEM 作参数 |
| CuST `B5Code`/`VeblenTerm5`/`BTBOTerm5` (`B5Code.agda:32-40`; `CIGVBTBOCarrier5.agda:20-34`) | 外部给出的标签与健全性 | 有限代码上可判定 (由 family 提供) | 极限只是编号, 无阶段函数 | 无 | 无 (`btboCollapse5` 只存编号) | 语法本身无强度; 语义靠证书 | cubical |
| CuST.Old `OrdD` (`CST.Old/Ordinal/BTBOCode.agda:16-29`) | 结构子项序 | 有界 (字面 ≡); 无界可反驳 | 全对严格 `monotonic` | 无 (只有 `LayerMapCode` 去函数化) | 无 | <Ω (我方 `Ordᴰ` 的抄本) | cubical (实际不需要) |
| CuST.Old `GenBOmega` (`NextCarrierBOmegaCore.agda:11-14`) | 规范比较 | 可判定 | 无极限构造子 | — | — | ω+ω 以下 | — |
| DecZero `BoundedTree` (`BoundedTree.agda:18-31`) | 结构子项序, 另有到商序数的语义 | 有界 (字面 ≡), 公共上界须是原始推导 | 全对严格 | — | — | 构造: ω^α, ε₀; 语义: ε₀ 不动点 | cubical (树本身不需要; 语义需要) |
| DecZero `SourceTree` (`BTBOSource.agda:14-29`) | 继承下标的结构序 | 派发用 `BoundedTree` 的有界三歧 | 层内 `ℕ → _` 无约束; 回到下标时用 cumsum | `funSourceLift` 改写下标 | 我方修补前的 ψ< / ψ₀ (lfp 加复合加对角) | 程序值未证; 我方估计 ψ₀(Ω_ω) | cubical (transport; 实际可用 `subst`) |
| DecZero `OmegaCubeRank` (`TrichotomyOrdinal/OmegaCubeRank.agda:14-19`) | 字典序 | 可判定 | — | — | — | ω³ 以下 | cubical |
| 我方 src `Ordᴰ` + `Ord ℓ` (`src/OCF/BTBO.lagda.md:645-661, 1011-1018`) | 结构子项序 | 有界 (字面) | 全对严格; ψ 输出用 cumsum 回灌 | `↑`/`coe₀` | 四行补丁后的 Buchholz ψ | 估计 ψ₀(Ω_Ω) (补丁后) | `--safe --without-K` |
| 我方 `Ordᴵ` (`probes/OCF/Align/Level.lagda.md` §1) | 字面子项序 `<ᴵ` + 结构互模拟 `≅ᴵ` + 前驱包含 `⊑ᴵ` | 有界, 三支都只模 ≅ᴵ (字面版推出函数外延性实例, §2 `lit→ext`) | 步进 `f n ⊑ᴵ f (suc n)`, 模 ≅ | — | — | 层号来自 `toLevel`, 无填充 | `--safe --without-K` |
| 我方 `Ordᶜ ℓ` (Level §4) | 跨层结构互模拟 ≅, 结构序 ≺ | 不需要 (只在下标层比较) | 证书 `HS` (遗传步进, 模 ≅) | 构造子 `up` (定义性), 加结构搬运 `tr`/`tr⁻` | Buchholz 式 ψ (5Ω 穿透用 `tr⁻`), ψ⁰ | 闭项 `BTBOᴵ`, 外层规则 6 是定理; 遗传标签 γ₁、γ₂ 是定理 | `--safe --without-K` |
| QIITOrd (参照, 我方 `Cumulative.lagda.md` §11) | 外延 (`l≡l` 商掉共尾列) | 外延三歧 ⇒ LPO | 严格 | — | — | — | `--cubical` HIIT; FGH 定义不出 |

---

## 对我们的参考价值

### 3a 可采用或改编的构造

1. **公共后项比较 (DecZero `BoundedTree.agda:61-67`).** 在 `lim`/`lim` 情形把两个推导都抬到 `suc (max n m)` 项再递归, 不分 n<m、n=m、n>m 三种情况. 在 `--safe --without-K` 下可原样使用. 对我方 `<ᴵ-dec` 的意义有限. 我方的 `sim (steps s n<m)` 本来就是单侧搬运, 而 `Ordᴵ` 的步进只给出 `≺ᴵ`, 不是字面 `<ᴵ`. 抬到公共后项仍要两次 `sim`, 结果也只模 ≅ᴵ. 它唯一的好处是省掉 `injᶜ refl` 一支. 不建议改.
2. **相邻严格推出全对严格 (`BoundedTreeArithmetic.agda:52-60`).** 我方已有同类引理 (`steps`, Level §1). 无新意.
3. **语义解释 `funTreeValue` (`BoundedTreeSemantics.agda:24-62`).** 它把严格单调树映到良序集, 严格序映为真初始段, 不需要判定器. 这里的商 (`Ordinal ℓ`)、截断、univalence (`OrdinalRepresentativeRecovery5.agda`) **必须用 `--cubical`**. 在 `--without-K` 下能保留的只有"代表元"一半: 树 → 带可判定序的良序 setoid, 严格序 → 模拟 (simulation). 链极限的余极限要写成 setoid. 对我方而言, 这样一个外延语义的作用只是让"值"层面的陈述有定义. 我方的 `src/WellFormed/CrossTree` 的 ≼/≈ 和 Cumsum 的 `overshoot` 已经在结构层面做到了这一点. **不建议现在做**, 除非 EBO 文章需要一个"值语义"的定理 (见 3d).
4. **去函数化的分层项 `LayerTerm`/`LayerMapCode` (CuST `CST.Old/Ordinal/BTBOMapCode.agda:12-29`).** 能在 `--without-K` 下写, 但表达力不足: 无法表示 ψ 的分支函数. 我方的归纳-递归 `U` (对证明递归) 严格更好. 不采用.
5. **需要 cubical 而不可采用的:** 商序数及其上的一切运算 (`Ordinal ℓ`、`ordinalChainLimit`、`veblen5`); `l≡l` 式的路径构造子. 理由与 `Cumulative.lagda.md` §11 对 QIITOrd 的分析相同: FGH 在商上定义不出. CuST 自己也没有 FGH 实现 (`docs/CuSTgoogology总结报告.md:13`), 只有契约 `FGHConsumerContract5`. 这从实践一侧印证了那条分析.

### 3b 与我方未决问题的关系

- **Buchholz 式记号的标准形理论.** 两个项目中都没有. CuST 的 Cantor 标准形只到 ω^ω 以下 (`CST.Middle/.../CantorNormalCode5.agda:22-24`). 对 `Bachmann.lagda.md` 末尾"γ_{k+2} 还缺三件"(Buchholz 下标上的 NF 谓词、pred/fsn 保持 NF、共尾性) 没有帮助.
- **基本列的共尾性 / Bachmann 性质.** 两个项目中都没有. CuST 的 `ChainLimitCofinality5` 讲的是商序数上链极限的共尾性, 与基本列后代关系无关.
- **记号与树的序对应.** 没有. 最接近的是 DecZero 的 `TheoriesTreeStrictValue` (树 → 语义值的严格保序, 只有一个方向), 以及 CuST 有限代码的 `TriDecision5` (代码比较 → 语义比较的健全性). 两者都不是"标准形上 v <ᵀ u ⟹ ⟦v⟧ ≺ ⟦u⟧"那种记号与树之间的对应.
- **证书式的层号.** 方向相反. CuST 的"证书"是**调用者提供**的外部记录 (`OmegaFixedPointWitness5`、`BTBOContract5`), 它的负面结果说的是"自动后端不可实现" (`docs/CuSTgoogology总结报告.md:131-143`). 我方的 `HS`/`toLevel` 由树**计算**出层号, 而 `Uniform` 是无前提定理. 两者只是同名, 没有可借之处.
- **ψ₀(Ω_Ω) 之后的下一个交替阶段.** 没有. DecZero 移植的 BTBO 是修补前的版本, 停在 BTBO, 而且语义未证.

### 3c 与壁垒定理的关系: 加强还是反驳

1. **没有反驳.** 两个项目里没有任何构造在 Ω-共尾的下标上恢复了有界三歧性. DecZero 的 `BoundedTree` 与我方 `Ordᴰ` 一样 sup ≤ Ω. CuST 的 `OrdD` 是我方 `Ordᴰ` 的抄本.
2. **cubical 商的代价是 LEM (CuST 的机器证明).** `decidablePresentationWeakImpliesLEM5`/`lemImpliesDecidablePresentationWeak5` (`DecidablePresentationWeakBoundary5.agda:57,63`) 与 `wellOrderLeastPointImpliesLEM5` (`WellOrderLeastLogicalBoundary5.agda:65`) 说: 在商序数上, 即使每个代表元都有可判定的序, 序数间的 ≤ 判定仍等价于同层 LEM. 证明用的是以命题为载体的 1+P. 这是我方壁垒在**外延一侧**的对应物. 对 Brouwer 树的像 (可数), de Jong 等人的 Theorem 53 给出的是 LPO. CuST 允许命题载体, 于是升到 LEM. 两边合起来, 结论比我方 Barrier §"结论与边界" 第 1 点的设想更具体: 把等号换成商 (外延相等) **不但没有保住三歧性, 反而把代价从 LPO 抬到 LEM** (在一般良序集上), 同时失去 FGH. 建议在壁垒文章的"与文献的关系"中加一句, 引用上述两处 (见"建议").
3. **字面等号分支与公共上界不可兼得 (DecZero 的 `TheoriesNoRawCommonBound`).** 在 `Ordᴰ` 式的严格树中, ω 与 ω∘suc 外延相等 (`TheoriesShiftedOmegaValue`), 却**没有**原始公共上界 (`BoundedTreeBoundary.agda:52-53`). 证明方法正是对假想的公共上界应用有界三歧: 三支都矛盾. 这与我方 Level §2 的 `lit→ext` 构成一对:
   - `Ordᴰ` (字面步进): 有界三歧可以有字面等号分支, 代价是两种同值表示永远不共处于一个上界之下, 比较的定义域对 ≅ 不封闭;
   - `Ordᴵ` (步进模 ≅): 允许 `s⊑ ω≅ω′ _` 让两种表示共处一个上界之下 (Level §2 的 `F`), 代价是三支都只能模 ≅ᴵ, 字面版推出函数外延性的实例.

   壁垒定理不受影响 (它对任何把 ≡ 换成更粗等价的设计都成立). 但这一对结果精确说明了 `Ordᴵ` 为什么要选"模 ≅": **只有这样, 下标层对 ≅ 才是封闭的.** 这是穿透分支需要 `tr⁻` 的根本原因. 建议在 Level §2 的注释或将来的 EBO 文章中引用 DecZero 的这条定理作对照.
4. **CuST 的 `unboundedOrdDTrichotomy-impossible`** (`CST.Old/Ordinal/BTBOUnboundedBoundary.agda:96-102`) 是我方 Barrier "实例: 朴素 Ord₁" 那种内涵反驳的一个更弱的变体: 不涉及 Ω, 只说明无界三歧加字面等号不成立. 没有新信息.

### 3d 可借鉴到 EBO 文章的想法

1. **用一个外延语义陈述"值"命题.** DecZero 的 `TheoriesNoCumulativeStagewiseLUB`/`TheoriesCumulativeNotAdditive` 用语义值说清了 cumsum 的问题: 它不只是改了基本列, 还改了值. 我方 Cumsum 的 `overshoot` (`probes/OCF/Align/Cumsum.lagda.md:69`) 是结构版本. EBO 文章讲"为什么去掉 cumsum"时, 可以把 DecZero 的定理作为**另一种基础下的独立复现**引用 (注意许可: 那是我方代码的派生作品).
2. **"同值不同表示"的最小例子.** `funTreeOmega` 与 `funShiftedTreeOmega` (DecZero `BoundedTreeBoundary.agda:17-19, 41, 61`) 是讲解"FGH 依赖表示而不依赖值"的现成例子. 我方 Level §2 的 `ωᴵ`/`ω′` (n ↦ n+0) 更极端 (逐点相等, 只是定义性不等), 两者可以并列.
3. **状态标签体系.** CuST 的 🟢/🔵/🟡/⚪/🔴 ("已闭合 / 条件性完成 / 部分 / 未建立 / 路线已排除, 须写明排除范围") (`docs/CuST开发计划.第5代序数载体覆盖面进度总览3.md:5-12`) 与我方"定理 / 估计"二分相近. 若 EBO 文章要列总表, "条件性完成"一档 (例如 `Diagonal` 以 `Uniform` 为模块参数时) 值得单列.
4. **反面教训.** CuST 大量的"契约 + 消费者"模块说明: 不计算的"证书"不增加强度. 我方文章应当强调 `toLevel`/`Uniform` 是**计算出来的**证书, 以示区别.

---

## 从它们自身角度的评价

### CuST

- **长处.**
  - 全部 `--safe`, 没有 postulate.
  - 逻辑边界做得认真: 对 LEM 的等价性给出双向机器证明, 不把经典原则藏进实现.
  - 商序数的代表元恢复利用了 univalence, 无需选择公理 (`OrdinalRepresentativeRecovery5.agda:4-7`), 技术上漂亮.
  - 文档对"条件 / 边界 / 已闭合"的区分诚实, 例如明说没有 FGH 实现、BTBO 没有被自动提升.
- **风险.**
  1. **体量与内容不成比例.** 236 个 BTBO 文件、95 个 Buchholz 文件, 核心却是参数化契约 (`BTBOConstruction5.agda:39-60` 全是参数). 新增模块多为 "Gap/Boundary/Adapter/Evidence" 记录.
  2. **经典依赖面广.** 863 个文件涉及 `PropositionDecider5`, 一般 Veblen 与上确界都以 LEM 为参数.
  3. **构建成本高.** 冷构建约 5 分钟、3.9 GiB; 654 次热构建超时; 曾出现 47 GiB 的接口展开 (`docs/CuSTgoogology总结报告.md:164`).
  4. **完成度低.** 第五代 0/4、V0 0/8; 下一代载体 0/5.
  5. **退役代码仍在树中.** `CST.Old` 通过符号链接 `src/CST/Old → ../CST.Old` 保留, 增加阅读成本.
  6. **(推断) 开发由 LLM 代理按计划文档驱动** (计划文件是 ChatGPT 会话导出). 风险在于优化方向是"闸门通过"而不是数学内容.
- **它在追求什么 (推断).** 在 Cubical Agda 中得到可用的物质集合论: 基数算术、ℵ/ℶ、初始序数. 并把 googology 序数 (Veblen、Buchholz、BTBO、FGH) 作为它的序数运算的"大例子"接入. 但它在语义上选了外延的商序数, 与 googology 需要的基本列结构正好相反.

### DecZero

- **长处.**
  - 目标集中, 有真实构造: 严格树、ω^α、ε₀ 加语义不动点、我方 BTBO 的完整移植、到商序数的无判定器解释.
  - 对 cumsum 的负面结果陈述精确, 并注明"不否定特定 BTBO 程序的值" (`docs/CuSTDecZero开发计划A4.md:103-104`).
  - 有界比较与语义公共上界的区分 (`TheoriesNoRawCommonBound`) 很到位.
- **风险.**
  1. **移植的是修补前的 BTBO.** 按我方分析, 它的值估计只有 ψ₀(Ω_ω), 而它的文档仍拿它与"原始 BTBO 或 Buchholz ψ(Ω_Ω)"比较 (`docs/CuSTDecZero开发计划A4.md:103`).
  2. **语义桥未建.** BTBO 程序的 fixed/least 证明未完成 (`:104`).
  3. **依赖固定提交的 CuST** (`e67753bf`), 并继承它的构建成本.
  4. **受控博弈只有有限层** `QGₙ`, 无界层级明确未做 (`docs/CuSTDecZero开发计划A4.md:292-295`).
  5. **许可.** 移植注释标明来源是 CC BY-NC-SA 4.0, 仓库却没有许可文件, ShareAlike 义务的落实情况不明.
- **它在追求什么 (推断).** 对由序数记号生成的受控博弈与数, 得到"无神谕"的比较与判零算法. 序数只是选项来源, 强度本身不是它的目标.

---

## 从我们角度的评价

1. **可以引用.**
   - DecZero `BTBOSourceBoundary.agda:21-66`: cumsum 改值, 是我方 Cumsum/NoCumsum 动机的独立复现.
   - DecZero `BoundedTreeBoundary.agda:52-62`: 与 Level §2 成对.
   - CuST `DecidablePresentationWeakBoundary5.agda:57,63` 与 `WellOrderLeastLogicalBoundary5.agda:65,69`: 外延一侧的 LEM 边界.
   - 这些都是 `--cubical` 的结果, 引用时应注明基础不同. 我方不导入它们的代码.
2. **可以复用.** 没有需要复用的代码. 所有可移植的构造 (严格树、有界三歧、ω^α、ε₀) 我方都已有, 或者有更强的版本.
3. **应当有意识地区别.**
   - 不用商, 不用外延序做下标 (理由: FGH 与壁垒).
   - 不用调用者提供的"契约"代替计算的证书.
   - 不用 LEM/判定器参数.
   - 这三点是我方纲领的既有选择. 两个项目的经验 (FGH 只能做成契约; Veblen 需要 LEM) 正好是不这样做的后果, 可作反面佐证.
4. **能否去掉假设或跳过阶段.** **不能.** 它们的结果都在 ε₀ 以下 (无条件), 或者以 LEM 为参数, 或者只是契约. 我方当前的缺口 (Buchholz 下标上的 NF、pred/fsn 保持 NF、共尾性 ⟹ γ₃ 起的遗传标签; 下一阶段的种子步与对角对象代表) 在它们那里没有对应物.
5. **它们使用了我方代码.** 两个项目都以 `9786181` 修订的 `src/OCF/BTBO.lagda.md` 为参照. CuST 的 `OrdD` 实质上是我方 `Ordᴰ`; DecZero 的 `BTBOSource` 是我方修补前 `ψ<`/`ψ₀` 的逐行移植. 我方 2026-11-01 的订正 (BTBO 原标签不成立, 值估计 ψ₀(Ω_ω); 四行补丁) 直接影响它们对 `funSourceBTBO` 的标注.

## 建议

1. **不改变基础.** 继续 `--safe --without-K`, 不引入 cubical. 本调研没有发现值得为之改变基础的构造.
2. **(需作者授权) 告知对方 BTBO 的订正.** 内容: `funSourceBTBO` 对应的是修补前的 ψ, 按 `probes/OCF/Align/BTBOSemantics.lagda.md` 估计值为 ψ₀(Ω_ω); 修补后的版本见 `src/OCF/BTBO.lagda.md` (现 HEAD); 无 cumsum 的替代见 `probes/OCF/Align/NoCumsum.lagda.md` §3. 同时可提醒许可文件的问题. 本报告不代为联系.
3. **在壁垒文章中加两条对照 (可选, 需作者另行发起).** (i) "外延 (商) 序数上的比较与最小点等价于 LEM", 引 CuST 的两处定理, 补全"把等号换成商"那一段的另一面; (ii) "`Ordᴰ` 式字面三歧下, 同值表示没有公共上界", 引 DecZero 的 `TheoriesNoRawCommonBound`, 与 Level §2 `lit→ext` 并列, 说明 `Ordᴵ` 为何选"模 ≅".
4. **EBO 文章中讲 cumsum 时**, 并列我方 `overshoot` (结构版) 与 DecZero 的语义版定理.
5. **研究主线不受影响.** 下一步仍是 `Bachmann.lagda.md` 末尾列出的三件事 (Buchholz 式下标上的 NF 谓词、pred/fsn 保持 NF、其上的共尾性), 然后是 γ₃ 起的遗传标签与下一阶段的交替. 两个项目都不提供捷径.
6. **暂不做外延语义探针.** 若将来需要"值"层面的定理 (例如证明两条对角线的值交错, 我方 Diagonal §3 目前是纸面论证), 可以参照 DecZero 的 `funTreeRepresentative`, 做一个 setoid 版的良序解释 (不商化). 届时再评估成本.
