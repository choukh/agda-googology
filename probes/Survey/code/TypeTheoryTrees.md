# 类型论侧的层号、宇宙与序数树: 静态代码阅读报告

> **证据记录, 手册见 [CodeGuide](../CodeGuide.md).** 查结论看手册; 本文是阅读当时的记录, 已知更正记在手册 §3、§6, 原文未改.

> 2026-11-02. **只读代码, 没有构建、运行、类型检查这些仓库的任何东西.** 所有 "sorry/postulate 个数" 都是文本 grep, 除非另有说明. 标注: [读] 我读过该行代码; [推断] 我的判断, 没有机检; [未读] 没打开. 没有读任何 `.claude/` 内容. 行号指钉住的 commit.
>
> 我方上下文: `probes/README.md`, `OCF/Align/InaccTreeBase`, `InaccStrike` 文首, `Level`, `Uniform3Base` 的 `fold`, `Survey/OrdinalNotationsGuide.md` §6.3–6.4.

## 钉住的版本与许可证

| 仓库 | commit | 日期 | 许可 | 选项 (文本 grep) | 主要语言 |
|---|---|---|---|---|---|
| AndrasKovacs/universes | `08e56f2484ed` | 2026-09-05 | 无 LICENSE | 无 `--safe`, 无 `--without-K`, postulate `ext`; 部分 `--rewriting` | Agda 2.6.1 |
| AndrasKovacs/ir-metatheory | `7cb256b987ad` | 2026-01-15 | 无 LICENSE | `PlainIR` 为 `--without-K` | Agda |
| coquand/agda-ordinal-analysis-id1 | `1f977e0920d7` | 2026-11-02 | 无 LICENSE | `--safe --without-K` (README + grep) | Agda 2.8.0 |
| coquand/agda-mahlo-universe | `199a725f56f7` | 2026-10-12 | 无 LICENSE | `--safe --without-K --exact-split` (README, `FixHyp`/`FixCounter` 已见) | Agda 2.9.0 |
| takahashi-yt/czf-in-mahlo | `b8aa846c9787` | 2025-08-19 | MIT | `--cubical-compatible`, 部分 `--safe`, 3 文件有 postulate | Agda |
| BedrockInstitute/QIITOrd | `7def431965eb` | 2026-06-23 | AGPL-3.0-only | `--cubical --safe` | Cubical Agda 2.8.0 |
| hyperpolymath/echo-types | `b0982c44f361` | 2026-10-31 | MPL-2.0 / 文档 CC-BY-SA-4.0 | `--safe --without-K` (骨架) | Agda |
| hyperpolymath/ordinal-notation (清单外, 迁出处) | `deb0131f99f5` | 2026-10-26 | MPL-2.0 | 大多 `--safe --without-K`; `Fidelity` 2 处 postulate | Agda |
| cj-xu/OrdinalNotations | `4690b68f9b64` | 2021-02-21 | GPL-3.0 | `--cubical --safe` | Cubical Agda |
| AzertyWasTaken/Ordinals | `a921bf964289` | 2026-10-31 | MIT | 不适用 | JavaScript |
| Dybjer–Setzer `gitlab.com/setzer/extended-predicative-mahlo-type-theory` | **未取得** | | 未知 | | |

---

## A. AndrasKovacs/universes (CSL 2022 的 Agda 补充)

钉 `08e56f2`. 仓库无 LICENSE 文件 (GitHub API 报 none), 不能默认可搬代码. 读: `agda/IRUniverse.agda` (大部分), `agda/Super.agda` (全), `agda/NatHierInjModel.agda` (前 60 行), `paper.tex` 用 grep 取的段落. 未读: `TTGUModel`, `TTFLModel` 的主体.

**Q1 定义与检查方式.** 层号结构是外给的记录 `LvlStruct` (`IRUniverse.agda:18-26`): 载体 `Lvl : Set`, `_<_`, `<-prop` (任意两个证明相等), 传递 `_∘_`, 以及全局的 `wf : ∀ {i} → Acc _<_ i`. 宇宙 `Uⁱʳ {i} (l : ∀ j → j < i → Set)` (`:42-47`) 是普通 IR, 对 "所有更低宇宙的解释" `l` 取参数; 真正的层次在外面用 `Acc` 打结 (`U<`, `U`, `:89-93`). 所以严格正性是平凡的: `l` 只出现在 `Elⁱʳ (U' p) = l _ p`, 不在 `data` 的负位置; 停机靠 `Acc`. [读]

选项: `IRUniverse`/`Super` **没有** `--safe`, 也没有 `--without-K`. `Lib.agda:31-32` 用模式匹配证 UIP, `Lib.agda:48-49` postulate 了函数外延. 这是一处本质差别, 不是遗漏: `U<-compute` (`IRUniverse.agda:98-99`) 证 "不同 `Acc` 证明给出同一 `U`" 用到 `Acc-prop`, 后者用 `ext` (`Lib.agda:59`). [读] 所以它的 "Acc 打结" 在 `--safe --without-K` 下要付一层代价, 而我方 `Lv` 上结构递归的 `Pre`/`Low` 不用 Acc, 也不用这条等式 (`outL`/`intoL` 是恒等式, 对路径递归). 这一点上我方比他干净. [推断, 依据是两边的定义]

**Q1 比较层号.** 他**从不比较**. 所有跨层操作都消费证据:
- 码 `U' : j < i → Uⁱʳ l` 带证明, `Lift : i < j → U i → U j` (`:101-113`) 带证明, 对码结构递归.
- 唯一需要判定的是 `_⊔_`, 放在单独的 `record Ordinal` (`:241-255`), 字段 `cmp : ∀ i j → i < j ⊎ j < i ⊎ i ≡ j` 与 `<-ext`. 这是假设, 不是定理, 而且只用于可选的 `Π''` (`:298-299`). 论文 `paper.tex:1009-1015` 明说 "trichotomous + extensional = 类型论序数, 排中律下等价于经典序数".

对我方的含义 [推断]: 他的 `Lift` 对应我方 `ψ↓ : Sim k i → …` (目标不低于树层, 从不比较, `InaccTreeBase.lagda.md` §3). **我方需要 `Verdict`/`<ᴵ-dec` 的地方是目标低于树层的折叠, 这在宇宙里没有对应物**: 宇宙没有 "把高层元素压到低层" 的运算. 所以 "比较用证据代替" 这条经验已经在 `ψ↓`、`Simᴵ` 里用尽, 他没有多给什么. `InaccStrike` 文首 "证据消费的折叠不成立" 这句判断在这里没有反例: 他的证据总是在构造时就有, 不是在分支时才需要.

**Q1 外给的层号宇宙.** 两个相关做法 [读]:
1. `IR-Universe (lvl) (A)` 的 `A` 是任意塞进宇宙的类型; `NatHierInjModel.agda:22-58` 先给 `Lvl` 加 `top` (`Lvl+`, `_<+_`), 再 `IR-Universe L+ Lvl` 把 `Lvl` 自己放进宇宙. `wf+` 由 `wf+-lem` 机械得到, 放在 `abstract` 里.
2. `Lvl'`, `_<'_` 是宇宙里的码 (`:53-54`), 层号可以在宇宙内被量化 ("first-class levels"). `idω'` 例子 (`:385`) 对层号与证明一起抽象.

这两点的方向都是 "层号先有, 宇宙后有". 我方 `Lv` 的 `limᴼ : (k : Lv) → (Ordᴸ k → Lv) → Lv` 反过来, 层号由树生成, 还跟树族在同一个 IR 块里, `<` 也不良基 (指南 §6.4 记 `¬WF-L₁`). **他的 `wf` 字段在 `Lv` 上不能满足**, `Ordinal` 记录更不能 (壁垒定理的方向). 所以不能把 `Lv` 直接实例化成 `LvlStruct`. 能实例化的是记号项: `Lvl = NF`, `i < j = cmp i j ≡ lt` (`<-prop` 从布尔的 UIP 来, 无需 K), `wf` 就是记号侧层 3 的 Acc. 见 §总结的第三项.

**Q2 布劳威尔树.** `Super.agda:19-22` 的 `O` 是裸树, 只作下标, 没有等价. 没有 ≅ 方面的东西.

**最近的结构同型: `Super.agda` 的 `OU`.** `U (sup f) = UU {∃ (U ∘ f)} {El ∘ ₂}` (`:132`), `↑sup a = El' (n , a)` (`:148-149`), 是非递归提升. 对照我方: `Pre (lim f) = Σ ℕ λ n → Pre (f n)`, `up : (d : D) → Dr d → Tree` 就是这个 `El'`; `NatU2` (`:102-124`) 是递归提升, 对应我们想要定义性提升时撞到的 `↑ℕ' ≡ ℕ'`. 论文 `paper.tex:643-647` 说超宇宙/Mahlo 能建模超限层次, 但不清楚如何得到 `Lift` 严格保持类型形成子 (Palmgren 叫 recursive sub-universes). 这是我方 `up` 构造子路线与 `lift` 对证明递归路线的对应文献术语. [推断, 映射是我做的]

**Q3 序数强度.** 无序数记号, 无基本列; 例子到 ω·ω 层 (`ℕ*ℕ-example`, `:334` 起, 字典序).

**Q4 复用.**
- 结构模式 `Uⁱʳ {i} (l : ∀ j → j < i → Set)` 对 `Tree P Br D Dr` 没有新东西: 我方已是这个形状 (P=路径, Br=该路径上的低层). 省不了什么.
- 想走 "记号作层号" 时, `LvlStruct` 是最小接口, 15 行. 见总结.
- 术语: "recursive sub-universe" 可用于文档.

## A′. AndrasKovacs/ir-metatheory

钉 `7cb256b`. 无 LICENSE. 读: `README`, `agda/Mahlo.agda` 前 70 行, `PlainIR.agda` 头. [未读] 主体 (`IRCanonicity` 等, 是 IIR 规范性证明, 与层号比较无关, 从文件名与 README 判断).

`Mahlo.agda:9-45` `Std` 模块: 把 `U+ : (A : Set) → (B : A → Set) → Set` 与 `El+` 作模块参数 (外给高阶宇宙算子), 定义 Mahlo 子宇宙 `Ma`, `El`. `New` (`:48-72`) 去掉 `U+'` 规则, 加基类型族 `U0`/`El0`. 无层号结构, 无序数. **对我方: 没用**; 只作 "把算子放模块参数" 的范例, 跟 `Fold (D : Oracle)` 同一写法. 后半 `Derivation` 证两种定义互相可构造, 只扫过.


## B. coquand/agda-ordinal-analysis-id1

钉 `1f977e0` (2026-11-02, 今天还在推). 无 LICENSE 文件 (API 报 none), README 无许可条款, **不能默认可搬代码**, 只能借思路. 作者署名 "Thierry Coquand, with Claude (Anthropic)". README 声称全部 83 模块 `--safe --without-K`, 无 postulate/洞/停机或正性 pragma, 无 funext; 文本 grep: 83 个模块都带 `--safe` 选项行, `postulate|TERMINATING|NO_POSITIVITY` 只出现在 6 个文件的注释里 (`Inf/FO` 把 funext 作模块参数, README 明说它已废弃且无人依赖). 我没有运行检查.

读: `README`, `Inf/Ord` (前 90 行), `Inf/Sum` (前 50 行), `Inf/Veblen` (前 150 行 + 签名), `Inf/AlgOrd`, `BH` (`:1-260`), `BHOrd` (签名与若干段), `VebT`/`VebU` 头, `Inf/BHSound` 的 `Acc`/`WF`. [未读] `Inf/BHCut`, `BHFml`, `BHArith`, `RA*` 主体, `notes/`.

**Q1.** 无层号结构. 下标是记号项, 比较是项上的布尔函数, 不涉及树. 宇宙没出现.

**Q2 无 funext 的树序.** `Inf/Ord.agda:12-14` 明说: "全部用 `leq` 陈述, 从不用 `Eq`, 所以极限情形不需要函数外延". `leq` 五构造子 (`:28-33`), 没有 `<`, 也没有 ≅; 传递性是对证明的结构递归 (`:44-68`). 这跟我方 `⊑` 的路是一条, 但他止步于单层裸树. 他不需要的我们恰恰需要: `VebT.agda:6-9` 明说 "Brouwer 序下做不出 `a<b` 或 `a=b` 的分情况, 所以树上 Veblen 定律留作假设; 换到记号上定律可以读出来". [读] 这是独立来源的同一观察 (对应我方壁垒定理与 `¬SoundAll`).

**`osum` 与 cumsum.** `Inf/Sum.agda:3-21`: 引 Martin-Löf 1972 致 Hancock 信, 他主张以求和而不是极限为原语, 因为基本列自动有 "nesting property". `psum f (suc n) = plus (psum f n) (f n)`, `osum f = olim (psum f)` (`:31-36`), 单调无条件 (`psum_step`, `:42`). 这就是我方已去掉的 cumsum 填充的同一件事, 也给了历史出处. [推断: 对应是我做的] 我方 `Cumsum` 的 `overshoot` 说明它改值, 他的注释没有讨论值的改变. 对 `Lv` 无新东西, 对文档有引用价值.

**Q3 强度.** 这是目前读到的 Agda `--safe --without-K` 下最完整的 Bachmann–Howard 记号实现, 但**没有基本列**:
- 树侧: `Inf/Veblen.agda:98-122` 的 `phi`/`iterPhi`/`chain` 是 Brouwer 树上的二元 Veblen, 互递归结构可过 (`phi a` 只调更小的 `a`, 极限走 `chain f`). `phiEps0Zero` (`:127`) 是树上最高的具名序数. α 可以是任意树, 所以 Γ₀ 可以写成 `olim`, 但这个模块没有定义它 (我只看了签名); 没有折叠. README 与模块注释说定律留作假设, 然后迁移到记号 (`VebT`).
- 记号侧: `BH.agda` 项 `T = omg | th T | sm (List T)` (`:87-90`), 不带标准形; 到 θ(ε_{Ω+1}) (Freund 2022 Def 3.1). 文本 grep `fundamental` 在 `BH*` 里零命中, 所以**没有基本列, 没有 FGH, 没有树翻译**. `Inf/BHCut` 的 `collapse` 是证明论的折叠定理, 不是序数函数的折叠.
- 良基性**没有证**: `Inf/BHSound.agda:64-69` 定义 `Acc`, `WF = (a : T) → Acc a`, 作定理前提. README 明说这一点. 所以他也停在我方 "层 3 未做" 的同一处, 只是位置不同.

**Q1/Q4 最值得看的技巧: 把比较从归纳-归纳里解开.** `BH.agda:16-27`: Freund 的项集、序、`E` 是同时递归 (归纳-归纳), 这里先生成不带标准形条件的更大的项集, 序是**裸项上的全函数**, 标准形是事后加的可判定谓词 `nfT`. 要点有三 [读]:
1. `lt` (`:199-` 互递归块) 结构递归可过. 对 `E(x)` 的量词写成**对项的递归** (`allLtT`, `someGeT`), 而不是先算出列表再遍历 (`:194-197` 注释). 每个调用或减第一参保持第二参, 或保持第一参减第二参. 这正好是 Agda 的词典序停机.
2. 字典序写成析取 `orB (lt a0 b0) (andB (eqT a0 b0) (ltL r s))` (`:234`), 而不是对 `eqT a0 b0` 分支. 注释说这样传递性可以先于反对称性证明 (否则 `a0<b0<c0` 要排除 `a0=c0`).
3. 序律对**任意裸项**成立: `ltTrans`, `ltIrr`, `tri : (x y : T) → Tri x y` (`BHOrd.agda:517, 568, 795`), 用 `msr` 燃料证, 不要标准形. 这解释了他为什么能先证序律再谈标准形. 我方 `Bachmann` 里有 `nf-fail₁₋₃` (裸项上序对应为假), 那是**树与项的序对应**, 不是序律本身; 两者不矛盾 [推断].

对我方 (已核对 `EBO.lagda.md:84-98`): `cmpᵀ` 已经是裸项上的全函数, 而且 Buchholz 式的序**没有 `E` 子句**, `cmpᴾ (ψ u a) (ψ v b)` 就是 `(u, a)` 的字典序; `<ᵀ-trans`, `cmpᵀ-refl`, `<→lt`, `lt→<` 已有 (`Closure`, `Bachmann`). 所以这三点的动因在我方大半不存在, **实际省不了什么**. 它的价值是: 独立旁证 "裸项 + 事后标准形" 这条路在 θ(ε_{Ω+1}) 上也走得通, 且序律可以与标准形解耦.

**Q4 复用.**
- `BH.agda` 的两个写法: 只有将来换成带 `E` 条件的 θ 式记号时才用得上. 现在不省. 无许可证, 不搬代码.
- `Inf/BHSound.agda` 的 `WF` 作前提的写法, 与我方 `Oracle` 作模块参数相同, 无新东西.
- `leq`-only 的 `Inf/Ord` 无新东西.
- **对 `Lv`、`≅`、`<ᴵ-dec`: 没用.**


## C. coquand/agda-mahlo-universe

钉 `199a725`. 无 LICENSE 文件 (API 报 none). README 声称 `--safe --without-K --exact-split`, 199 模块约 47000 行. 没有逐个 grep 选项. 读: `README` 前 60 行, `MAHLO/FixHyp.agda` 头, `MAHLO/FixCounter.agda` (`:78-135`, `:172`). `notes/mahlo-results.tex` 用 grep 看过 "ordinal" 的命中行. [未读] 其余约 195 个模块 (Setzer Mahlo 的元理论: PER 模型、规范化、判定).

**Q1–Q3.** 这是**语法元理论**, 不是序数学. 全部 `*.agda` 里, "ordinal/Brouwer/Veblen" 不分大小写只命中 `MAHLO/FixCounter.agda` (`git grep`). 没有层号结构, 没有基本列, 没有序数记号. 指南 §6.4 "README 未提序数" 属实. Mahlo 不动点存在性是作记录假设的 (`FixHyp`: `FixThm`, `LargeSups`, `PFix`), 不是定理.

**唯一相关的一段: `FixCounter.agda:82-122`.** `Ord : Set1`, `sup : (I : Set) → (I → Ord) → Ord`, 配 `Pred`, `at`, 以及**递归定义**的 (不是数据类型的) 序: `sup I f ≤ y = ∀ i → f i < y`; `x < sup J g = Σ J (λ j → x ≤ g j)`. `≤-trans` 等互递归结构可过, `irrefl` 无需 Acc, `lub` 用 Σ 把分支类型合并 (`:121-122`). 这是 Aczel/W-序数上的标准做法. 无 funext. [读]

对我方 [推断]: 这个序比 `≅` 粗 (序数值, 不是结构), 而且完全不要分支互搬数据 `u`, `v`: `limᴼ k g` 的分支类型 `Ordᴸ k` 不同也能比, 因为 `≤` 只说 "每个前驱低于对方". 所以对 `Lv` 是一个**现成的值前序候选**: 递归定义, 不用 `u`/`v`. 但它是值相等路线. `memory/value-equality-verdict` 已判定值路线不省代价 (ψ⁰ 对高层参数不尊重值). 所以这个不解决判决问题, 也不替代 `≅`; 我把它列在这里只因为它写法极短, 若 `VLab` 那边要跨 `Ordᴸ k` 比较可以直接照这个形状写. 另外注意 `Lv` 的 `lim`/`limᴼ` 混合的分支, 要先压成 W 形.

**Q4.** `FixCounter:82-122` 的递归式 `≤`/`<` 写法 (无许可证, 借思路). 其他: **没用**.


## D. takahashi-yt/czf-in-mahlo

钉 `b8aa846`. MIT (`LICENSE`, 2023 Yuta Takahashi): 可搬代码, 保留版权声明. 选项 `--cubical-compatible`, 其中 `CZFBasics`, `CZFAxioms`, `ExternalMahlo`, `Preliminaries`, `IterativeSetHierarchy`, `TypeHierarchy` 带 `--safe`; 文本 grep `postulate` 命中 `Extensional.agda:18` (funext), `Inaccessibles/Basics.agda:218,232`, `RegularExtensionAxiom.agda:259`, 这些文件不带 `--safe`. 读: `ExternalMahlo` (全), `TypeHierarchy` 前 90 行, `CZFBasics:32-60`, `CZFAxioms:916-923`. [未读] `Inaccessibles/*`, `IterativeSetHierarchy` 主体, `RegularExtensionAxiom`.

**Q1 定义.** 外部 Mahlo: `𝕌 f`/`𝕋 f` (`ExternalMahlo.agda:31-57`) 对算子 `f : Fam → Fam` 参数化, `Set` 自身当外部 Mahlo 宇宙. 高阶算子 `𝕆 n`/`𝔽 n` (`:79-87`) 对 ℕ 互递归. `u𝕄 : 𝔽 1 → 𝕆 1` (`:101-111`) 给 "对一族一阶算子封闭的子宇宙". 超限在 `TypeHierarchy.agda:19-42`:

- `𝕍 = W Set (λ A → A)` (`CZFBasics.agda:32-33`).
- `data Acc : 𝕍 → Set₁`, `prog : ((x : index (tc a)) → Acc (pred (tc a) x)) → Acc a`.
- `𝕍⊆Acc` (`:31-36`) 证**一切** 𝕍 元素可及, 对 `sup A f` 结构递归. 所以 `Acc` 不是假设, 只是为了让停机检查看到 `tc a` 的元素比 `a` 小.
- `ϕ a (prog f) = u𝕄 (index (tc a) , λ x → ϕ (pred (tc a) x) (f x))`: 沿 **传递闭包的全部路径**一次取齐, 不比较任何东西. [读]

**Q1 与我方的对应 (这是本仓库唯一的硬内容).** `index (tc a)` 就是我方 `Pre ℓ` ("所有更低层的路径"), `pred (tc a)` 就是 `at ℓ`, `ϕ` 对全部路径喂给 `u𝕄` 就是我方 `Tree (Pre ℓ) (Low ℓ) …` 把全部低层分支放进一个节点类型. 差别 [推断]: 他走 `Acc` 是因为 `tc a` 经过 `∪` 组装, 停机检查看不透; 我方 `Pre`/`Low`/`at` 对 `Lv` 直接结构递归, 不需要 `Acc`, 比他省. **没有找到比我方现状更短的写法.** 而且 `ϕ` 的层号是 `𝕍`, 外给, 跟树族无互递归, 这正是指南 §6.4 记的 "沿可及性走, 不沿记号走".

**Q2 等价.** `_≐_` (`CZFBasics.agda:51-53`) 是 Aczel 外延相等, **对 𝕍 递归定义**而不是数据类型: `sup A f ≐ sup B g = (∀ x → Σ B λ y → f x ≐ g y) × (∀ y → Σ A λ x → f x ≐ g y)`. refl/sym/trans 都对 𝕍 结构递归 (`:86-97`), 无 funext. 我方 `≅` 文档写的 "Aczel 式" 就是这个 (`o≅` 的 `u`, `v` 就是这两个 Σ 的第一分量). 差别是我方写成 data, 他写成递归函数. 递归写法的好处: `≐bisim` 式的反演是 `refl`; 代价: 跨层时 `Lv` 的 `Ordᴸ k` 不在同一个 W 里. **没有比 `o≅` 更省的东西.**

**Q3.** CZF + 所有超限阶的不可达集在 MLTT + 一个 Mahlo 宇宙 + Acc 中可解释. 无序数记号, 无基本列, 无树的折叠. `Set` 作外部 Mahlo, 所以 `𝕌 f` 过正性检查靠 IR, 与层号无关.

**Q4.** `ϕ`/`𝕍⊆Acc` 的 "总体可及 + 路径一次取齐" 模式: 对 `Lv` 不省 (已结构递归). 若将来走 Ord 经 `tc` 组装的路线可参考. 否则 **没用**.


## E. BedrockInstitute/QIITOrd

钉 `7def431`. **AGPL-3.0-only** (`LICENSE`, 文件头 SPDX): 搬代码会传染, 只能借思路. Cubical Agda 2.8.0 + cubical 0.9, `--cubical --safe`, 部分模块 `--lossy-unification`. 文本 grep `postulate|TERMINATING|sorry|{!` 在 `src/` 只命中说明文字. 读: `README`, `docs/termination.md` (全), `docs/antisym-variant.md` 开头, `Base.lagda.md:60-140`. [未读] `Order/Code*` 的代码本体, `Properties`, `Antisymmetry`.

**Q2 定义.** 单层 QIIT (`Base.lagda.md`): `Ord` 与 `_≤_` 互定义, `lim : MonoSeq → Ord` (`MonoSeq` = `f` + `suc (f n) ≤ f (suc n)`), 路径构造子 `l≡l : fst f ≈ fst g → lim f ≡ lim g` (`≈` 含命题截断 `∃`), `isSetOrd`; `≤` 带 `≤-trans`, `isProp≤`. 源自 Kraus–Nordvall Forsberg–Xu (arXiv 2208.03844) `BrouwerTree/*`, 那边 `Code` 用了 `TERMINATING`.

**他解决的问题 (`docs/termination.md`).** 两个独立的停机障碍: 截断里解出的证据不算结构变小; `≤ᵖ` 对两个参数交叉重入, Agda 的逐位字典序看不到. 解法: `≤ᵖ = fst ∘ elim`, 把定义走**外部消去子** (模块参数化地检查一次), 于是它在当前模块不再递归, 跳出失败的强连通分量 (§3.1). 载体打包单调性 `Σ P (∀ x≤y → P x → P y)`. 传递性 `≤ᶜ-trans` 是对**中间序数优先** `(β,α,γ)` 的嵌套 `elimProp`, 第一参优先不行 (§3.2 有表). §3.4: 走 `Acc _<_` 在 `--safe` 下循环, 因为证 `<` 良基要 `α < lim f → ∃ n. α < f n`, 那要先有 encode-decode. [读文档; 代码本体未读]

**对我方的判断 [推断, 没有机检].** 指南 §6.4 把它记作 "可以过停机检查的序". 这准确, 但它对 `≅` 与判决**都不适用**:

1. **商化摧毁基本列.** `l≡l` 让 FGH 无从定义: `FGH (lim f) n = FGH (f n) n` 不尊重 `l≡l` (同值不同列给不同的数). 我方项目的目标函数就读这个序列. 他的 `Ord` 上, 从 `lim` 取出 `f n` 的函数都要证尊重 `l≡l`, FGH 证不了. 这是决定性的: **层 0 的树不能是这个 QIIT**.
2. **层号也不行.** 把 QIIT 作层号 (`Ordᴵ` 的替代), `Ordᶜ`/`Pre` 这种按层号算类型的消去要进 `hSet`, 而 `isSetOrd` 要求目标是集合, `hSet` 是 1-型. 他的 `≤ᵖ` 进 `hProp` (是集合) 才定义得出来, 层号的类型族没有这个待遇. 要么放弃截断, 要么另找编码. 另外 `ψ⁰` 不尊重值 (`value-equality-verdict`), 分支 `l≡l` 没法填.
3. **`≤` 仍不可判定.** `suc α ≤ᵖ lim f = ∃ n. …` 是截断的存在, 壁垒定理的情况没变. `<ᴵ-dec`/判决不因此而变简单. `lit→ext` 这个问题 (字面 `<` 蕴含 funext) 在 cubical 里自然消失, 但这只把问题从 funext 换成上面两条.
4. **工具链.** `--cubical` 模块只能导入 `--cubical`/`--cubical-compatible` 模块. 我方底座 `--without-K` 不是 `--cubical-compatible`, 要改全部选项, 或者把 Commute 单独搬过去. `Commute` 需要 `Funext` 这一点, `--cubical-compatible` 的模块本身得不到 funext, 必须把用到的模块也改成 `--cubical`. 这是 Funext 问题的正解 (路径给 `funExt` 且计算), 但它只解决 `Commute` 里 "字面树相等" 这一件事, 不需要 QIIT. 跟 §总结排名第 1 项 (`≈S`, 不做字面相等) 是替代关系, 而后者便宜得多.

**有用的是方法, 不是定义:**
- "走外部消去子跳出 SCC" 在没有路径构造子时也成立: 我方若有记录式的消去子 (比如对 `Lv` 的折叠算子放在 `module`), 大块互递归可能拆开. `Tree`/`Lv` 块本身是 IR, 这条帮不了 `ψ` 的类型, 但可能帮 `Commute` 类定理的 `with` 爆炸. 这是猜想.
- 中间优先字典序: `⊑` 类传递性的现成表. 我方已有结构证明, **不省什么**.

**Q3.** 只到 Brouwer 树本身. 无 Veblen, 无折叠. **Q4.** 无可搬代码 (AGPL + cubical). 只有 `docs/termination.md` §3.1–3.2 的方法.


## F. hyperpolymath/echo-types 与其迁出的 hyperpolymath/ordinal-notation

`echo-types` 钉 `b0982c4`; MPL-2.0 (代码), CC-BY-SA-4.0 (文档). `proofs/agda/Ordinal/Buchholz/Syntax.agda` 只有 24 行: `data BT = bzero | bOmega OmegaIndex | bplus BT BT | bpsi OmegaIndex BT` (`:15-19`), `OmegaIndex = fin ℕ | ω` (`Ordinal/OmegaMarkers.agda`), 无序, 无语义. 确实只是骨架. 同目录文档说其余代码 2026-10-20 迁到 `hyperpolymath/ordinal-notation`, 所以我把那边也钉了: `deb0131` (MPL-2.0, README 标 status frozen). 这个仓库不在原清单里, 这部分属于顺带读的. 读: `Buchholz/Fidelity` 头, `Brouwer.agda` 前 85 行, `Brouwer/VeblenBinary:1-30, 84-122, 200-217`, `Buchholz/WellFounded`/`Psi` 头; `echo-types` 的 `docs/bridges/buchholz-rank-obstruction.adoc` 前 60 行. [未读] 约 50 个 `Rank*` 模块、`Veblen*Model`. 没读其中的 `CLAUDE.md`/`GEMINI.md`.

**Q1.** 层号就是 `OmegaIndex`, 只到 ω: 外给的固定标记, 没有 `Lv` 式问题. **无用.**

**Q2.** `Brouwer.agda` 裸树 `oz | osuc | olim`, `α < β = osuc α ≤ β`, 良基对树结构递归. 无等价类. 没有新东西.

**Q3.** 树侧: `VeblenBinary.agda:84-112` `g-tower`, `nextFix g x = olim (g-tower g (osuc x))`, `deriv`, `commonStep`, `φ`, 对首参结构递归返回 `Ord → Ord`, 第二参的递归全在 `deriv` 里, `Γ₀ = olim Γ-tower` (`:200-201`). 这是干净的写法. 我方 `src/Veblen/Multinary.lagda.md:283-284` 已有 `Γ = fixpt λ α → φ α 0`, 新增为零 [未逐行对比].

记号侧: `Buchholz/Order` 的 `_<ᵇ_` 有 `wf-<ᵇ` (`--safe`), **但作者自己的文档说这个序不是序数上正确的**: `<ᵇ-+Ω` 让 `bplus bzero (bOmega (fin 1)) <ᵇ bOmega (fin 0)` 可导 (`buchholz-rank-obstruction.adoc`), 所以任何单调秩都不存在. 这解释了他为什么证得出 WF: 那是个"更粗的"关系, 不是 Buchholz 序. `Buchholz/Fidelity.agda:183, 211` 两处 `postulate` (文本 grep), 把 "序型 = ψ₀(Ω_ω)" 作为公开的开放问题, 不是定理. **没有基本列** (`git grep -il "fundamental seq"` 在 `verification/*.agda` 零命中), 没有折叠函数.

**提醒 [推断].** 单看标题 "Buchholz notation WF, `--safe`" 容易以为它解决了我方记号侧的层 3. 它没有. `<ᵇ` 不是我方 `cmpᵀ` 的序. 他的项目也不声称这一点.

**Q4.** `RankPowMonoRefuted`, `StrictLeftMonoRefuted` 等 "已证伪" 模块可以当记号侧 WF 尝试的反例目录 (文件名判断, [未读]). 其他: **没用**.


## G. cj-xu/OrdinalNotations (Xu & Nordvall Forsberg)

钉 `4690b68` (2021-02). GPL-3.0 (搬代码须 GPL 传染, 借思路即可). `--cubical --safe`; 文本 grep `postulate|TERMINATING` 无命中. 读: `MutualOrd:30-75`, `HITOrd:20-60`, `TransfiniteInduction:16-40, 104-157`, `MutualOrdWithoutNestednessAndRecursion:1-60`. [未读] `Arithmetic`, `Equivalences`, `SigmaOrd`.

**强度.** 只到 ε₀, 三种表示 (Σ 式、归纳-归纳式、HIT) 用泛等互转. 没有基本列, 没有树.

**Q1/Q3 可借鉴的三点 [读].**

1. **内在标准形.** `ω^_+_[_] : (a b) → a ≥ fst b → MutualOrd` (`MutualOrd:37-39`), 项与序、`fst` 同时定义 (归纳-归纳-递归). 所以 `<` 只作用于标准形, 非标准项无法写出. 我方 `Bachmann` 的 `nf-fail₁₋₃` (`1+ω` 与 `ω` 的树既不 ≺ 也不 ≅) 说明序对应只对标准形成立, 现在靠外加 `NF`. 内在化能消去 `NF` 前提, 但 `Coquand BH` (§B) 走相反的路: 裸项 + 事后可判定谓词, 序律对裸项成立. 两者比较: 我方记号 `EBO` 已是后者, 改写代价大 [推断].
2. **Acc 证明 (`TransfiniteInduction:113-150`).** `fstAcc`/`sndAcc` 同时递归, 外层对 `a` 的 `Acc`, 内层对 `b` 的 `Acc`; `WF x` 对项结构递归, 约 30 行. 这是我读到的这些仓库里**唯一完整的 Acc 证明**, 无 Gentzen 跳. 但只适用于 ε₀: 这里 `ω^a + b` 的第一支归结到 `a` 的子项; ψ 记号里 `ψ(a) < ψ(b)` 还要带 `E(a) < ψ(b)` 条件, 下降到的元素不是 `b` 的子项, 所以这个形状不能直接延伸到 ψ [推断]. 我方 `FGH-c1` 等也许只要 ε₀ 片段时能照这个写.
3. **函数的图代替递归函数 (`MutualOrdWithoutNestednessAndRecursion:6-14`, Remark 3.1).** IR 的 `fst` 若只严格正地出现, 就可以换成归纳-归纳定义的图 `_≡fst_`, 把 IIR 化成 II. 这对我方是**具体可试的一条**: `InaccStrike` 文首记 "生成类的 `Gen`/`Run` 互递归不严格正 (编译器拒绝, 试验未保留)". 若 `Run` 在 `Gen` 的构造子里只严格正地出现, 把 `Run` 换成图可能过. 若负出现就不行, 我没有那份试验, 不知道属于哪种.

**Q2.** HIT 只商交换, 不涉及极限. 可判定的 `lt : HITOrd → HITOrd → Bool` (`TransfiniteInduction:64`) 是从 MutualOrd 经泛等搬来的. 与 `≅` 无关.

**Q4.** 第 2 点 (ε₀ 片段 Acc 的 30 行形状) + 第 3 点 (图代替函数). 其余没用.

## H. AzertyWasTaken/Ordinals

钉 `a921bf9`. MIT. 全是 JavaScript 脚本 (`git ls-files`: 无 `.agda`/`.lean`), 按强度分目录 `1_w`, `2_e0`, `3_p(Ww)`, `4_p(Bw)`, 展开序列/hydra 类记号的基本列. README 链接的 `Docs/azocf.md` 在树里不存在. 我只读了文件列表和 README 开头. **Q1–Q3: 不是类型论, 没有定义层号、等价或证明. Q4: 没用** (顶多当基本列的手动对照, 我方已有 `OrdinalNotationsFS`).

## I. Dybjer–Setzer Agda 模型: 没取得

论文 (JLC 34(6), 2024, 开放全文) `:129` 与参考文献 [13] 给出仓库地址 `gitlab.com/setzer/extended-predicative-mahlo-type-theory`. 匿名 `git clone` 要凭证, GitLab 公开 API 返回 404; 网页地址返回 302, 我没有跟进登录. GitHub 搜索也没有副本. **代码未读.** 论文只 grep 了 "Agda/ordinal/well-founded" 的命中行: 提到模型在 Agda 中检查, 上界为 KP 加一个递归 Mahlo 序数与有限多个可容许序数的强度. 这些不足以回答 Q1–Q4. 是否值得找作者要访问权限, 由人决定; 从 Coquand 的同主题仓库看, 我预计与层号比较无关 [推断].

---

## 总结

### Q1 层号: 比较不靠全局三歧的做法

被调查的代码里, 处理层次的方式只有四种, 都不解决我方的问题:

| 方式 | 谁 | 比较如何发生 | 为何不适用 |
|---|---|---|---|
| 证据写进码 | Kovács `U' : j < i → U`, `Lift` | 从不比较 | 只有上行提升. 对应我方 `ψ↓`, 已用尽 |
| 沿全部路径一次取齐 | Takahashi `ϕ` 沿 `tc a` | 从不比较 | 对应我方 `Pre`/`Low`. 不是折叠 |
| 固定标记 | echo-types `fin n`/`ω` | ℕ 比较 | 只到 ω |
| 记号项上的全函数 | Coquand `lt`, cj-xu `<`, 我方 `cmpᵀ` | 语法比较 | 层号不从树来 |

**没有任何一处有 "目标低于节点层、按层号分派的总折叠".** 这是 OCF 独有的算子; 宇宙论文献不需要它 [推断, 依据是上述代码, 不是文献穷举]. `<ᴵ-dec` 的有界三歧也没有对应物: Kovács 的 `cmp` 是全局假设 (`IRUniverse.agda:244`), Coquand 的 `tri` 在项上. **我方 `<ᴵ-dec` 比读到的一切都精细, 没有可以拿来简化它的东西.** `InaccStrike` 的两个阻碍 (只看层号的总比较; 证据消费的折叠) 在这些仓库里没有反例, 也没有绕法.

Kovács 的良基层号: `wf` 全局外给, `<-prop` 外给, 用 `Acc` 打结, 代价是 funext + UIP. `Lv` 既不能也不必这样: `¬WF-L₁` (`InaccTree.lagda.md:68`) 排除了它, 结构递归的 `Pre`/`Low`/`at` 又让它不必要.

### Q2 等价与外延

- **`≅`.** Takahashi 的 `≐` 与 `o≅` 同构 (Aczel), 没有更省的写法. Coquand `FixCounter` 的递归 `≤`/`<` 不要分支互搬, 但是值序, 属于已判定不省代价的值路线.
- **`Commute` 的 `Funext`.** 读到的无 funext 开发都遵守同一条: 极限处不用 `≡`, 用归纳的逐点关系 (`Inf/Ord.agda:12-14` 说得最明白). 见下面排名第 1.
- **QIIT.** 商化破坏 FGH, 不适合我方的树 (§E). `≤` 的计算版本解决的是**路径构造子和截断带来的**停机问题, 我方没有那个问题.
- **可判定片段.** 只在记号上有. 树上都做不到, `VebT.agda:6-9` 是独立的旁证.

### Q3 强度

| 位置 | 树 (带 ℕ-极限) | 记号 | 基本列 | 良基 |
|---|---|---|---|---|
| Coquand id1 | φ, 无折叠 | θ(ε_{Ω+1}), 完整序律 | **无** | 作前提 |
| ordinal-notation | φ, Γ₀ | `BT` 到 ω 标记, 但序不是序数序 | 无 | 对粗关系成立, 序型开放 |
| cj-xu | 无 | ε₀ | 无 | **有, 约 30 行** |
| Takahashi/Coquand Mahlo/Kovács | 裸树作下标 | 无 | 无 | 不适用 |

**没有一个仓库实现了序数折叠函数的树, 也没有一个给 ψ 记号写基本列.** 就读到的范围, 我方树侧 (`Uniform3`, `Lv`) 比它们都高; 这不是说世界上没有, 只是这些仓库里没有. 记号侧基本列的先例仍是指南 §5 的 Lean `ExBuchholz`.

### Q4 排名前三

1. **把 `Commute` 的 `≡` 换成归纳的逐点关系 `≈S`, 去掉 `Funext` 参数.** 来源是原则 (`Inf/Ord.agda:12-14`, `CZFBasics.agda:51-53`), 不是可搬代码. 依据: `fe` 只出现在 `InaccStrikeBase.lagda.md:113` 起的 `Ext` 块 (我读到的是 `cong limS`/`limᵢ-cast` 下) 与 `InaccStrikeCommute.lagda.md:151,154,227,247` (后两处也是 `cong limS (fe …)`), `InaccStrikeCommute:268` 的 `lab : x ≡ S t → … → LabN (dz x) t` 只是逐点下行, `LabN` (`InaccTreeAccept:253-256`) 本身也是逐点的. 所以 `data _≈S_ : St → St → Set` 带 `z/s/l/i` 四个构造子看来就够, `limᵢ` 情形保留 `subst Ordᴸ e`. **预期收益:** `nat-label` 变无条件 (去掉 "只以 `Funext` 为参数"). **风险:** 没有编译; `ψS` 对 `≈S` 的同余要多写一组引理, 规模估计与 `Ext` 块相当. 这个收益只是干净化, 不解决判决问题.
2. **函数的图代替递归函数** (cj-xu `MutualOrdWithoutNestednessAndRecursion:6-14`), 试救 `InaccStrike` 记的 `Gen`/`Run` 不严格正 (选项 (a) 的生成类). 便宜, 一次编译就能知道. 只有 `Run` 严格正出现时才行, 那份试验未保留, 所以成败未知. 现行的 `Gs` 分层已经绕开这个问题, 所以这条的价值是**去掉对 `n` 的分层**.
3. **Kovács `LvlStruct` 当 "记号作层号" 的最小规格** (`IRUniverse.agda:18-26`, 仅思路, 无 LICENSE). 取 `Lvl = NF`, `i < j = cmpᵀ i j ≡ lt`. 这时判决无需寻找: `cmpᵀ` 就是判决, `GV` 按定义成立. 这是 `Certified` 四条出路里 "记号生成层号" 的明确形式. **代价 [推断]:** (a) `limᴼ k g` 的分支输入是第 `k` 层的树, 而这里 `toLv` 无处可去, 分支只能走项, 树就成了记号的展开, 失去 "树与记号独立" (`InaccStrike` 特意让导入链不含 `EBO`); (b) `wf` 字段就是记号侧层 3 的 `Acc`, 未做; 若把 `Pre` 改成对项的路径则可避开 `Acc`, 但我没验证. 所以这是一个设计分岔, 不是省事的办法. 需要作者判断.

排名之外: cj-xu 的 `fstAcc`/`sndAcc` (ε₀ 片段 `𝔼` 的 `Acc`, 约 30 行, 不能延伸到 ψ 形状, GPL 只借思路); `FixCounter` 的递归序 (若 `VLab` 要跨层比较).

### 对 "`Lv` 是否继续" 有影响的发现

**这些仓库不提供继续或停止的决定性证据. 有三点值得记入判断:**

1. **定义层面, `Lv` 没有问题, 甚至比先例干净.** Kovács 与 Takahashi 都要 `Acc`, 前者还要 funext 和 UIP; `Lv` 结构递归通过 `--safe --without-K`. 非递归 `up` 对应 `Super.agda` 的 `OU` (最接近的先例, 但其下标是裸 `O`, 不含 `limᴼ`). 指南 §6.4 "没找到层号就是裸 IR 宇宙的前人工作" 在这批代码里继续成立.
2. **比较层面, 没有外援.** 总判决的障碍在这些仓库里没有解法, 也没有人碰到过同样的问题. 所以不要指望文献再给出 `D`; 只能靠 `InaccStrike` 文首写的决定性检验 (`N` 扩到可数标准形, 看 `lim` 目标的范数模). 这次调查不改变那个结论 (PLATFORM, 只在标签路线上).
3. **读到的所有成功案例都是 "证据先于比较" 或 "比较在语法上".** 这符合 `Uniform3` (`Goodᴸ`, 地板) 的方向, 不符合 `Lv` 的 "只看层号的总比较". 这是相关性证据, 不是定理: 这些开发的目标都不含折叠, 没有证明 `Lv` 路线走不通. 我的判断是不增加对 `Lv` 判决路线的信心; 决定权在作者.

### 没有读到的

- Dybjer–Setzer 仓库: 无匿名访问.
- Kovács `TTGUModel`/`TTFLModel` 主体与 `arXiv 2607.11329` 的 `NatHierInj` 论文; `ir-metatheory` 的规范性证明.
- Coquand id1 的 `BHFml`, `Inf/BHCut`, `RA*`; Coquand Mahlo 的绝大部分; `QIITOrd` 的 `Order/Code*` 代码本体 (只读了文档); `ordinal-notation` 的 `Rank*`.
- 我跳过了所有 `.claude/` 内容; `ordinal-notation` 根目录的 `CLAUDE.md`/`GEMINI.md`, `AzertyWasTaken` 的 `AGENTS.md`/`Metadata/prompt.txt`, `echo-types` 的 `.machine_readable/` 也没有读.
