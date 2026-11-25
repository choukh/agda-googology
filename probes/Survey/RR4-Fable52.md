# 第四次整体路线审查 (RR4, 2026-11-10)

> 审查者: Fable 5.2 (模型 ID `claude-fable-5-2`). 前提只有 AGENTS.md 的四条纲领与目标 "让树自足". 仓库里的其余文档 (README, LOG, RESULTS, Survey 下各篇, 以及 `.lagda.md` 里的讲解文字) 一律当作待核的主张.
>
> **证据标准.** 只有冷编通过的 Agda 定理与我亲自读过的陈述算证据. 每条结论标档:
>
> - **定理 (已冷编)**: 我删掉该模块自己的接口文件后重新编译, 退出码 0, 输出里有 `Checking` 该模块. 依赖取缓存 (Agda 会核对依赖的源码哈希; 除一处外都只重查了目标模块, 见 §9).
> - **定理 (未复核)**: 只读了陈述, 没有冷编.
> - **测试**, **判断**: 字面意思.
>
> 强度写 ψ₀(Ω_x). 定理里的标签项字面是 `ψ₀ᵗ (Ωt (ψᵗ 1 2 ∷ []))`; 把它读成 ψ₀(Ω_{Ω·ω²}) 用的是仓库约定的换算, 不是 Agda 定理.

## 0 对纲领与目标意味着什么

1. **终点 (记号无关的树, 序数值不低于 EBO) 没有接近的编译定理.** 记号无关的树侧, 序数值互相 ≼ 的最高点仍是 ψ₀(Ω_{Ω·ω²}); 严格下界再高一个后继. 带记号的完整 EBO 闭项已经编译并双向验收 (`DirectedViewDirectClosed.full-EBO`). 所以缺的不是 "布劳威尔树能否表示 EBO", 而是 "不引用记号时, 折叠的派发证据从哪里来".
2. **没有任何编译定理否定乙线, 也没有否定其它开放路线.** 乙线的每条否定都是对某个接口形状、在全合法域上的否定.
3. **RouteReview3 §5.9 把乙线的停顿归到 V 墙 ("折叠不是值的函数"), 这个归类在定理层面不成立.** 七个反例里, 机制上对应 `ψ⁰-not-cong` 的只有最后一个; 四个是字面位置证据的问题 (其中第八轮那个是 W 墙的直接实例, 对象都是规范写法); 一个是平行块两侧合法性不一致; 一个是输出严格性, 而它的值恰好是对的.
4. **本次新增的编译证据改变了两处读法.** (a) 派发证据 `Reg` 在规范层的读回域上不需要严格性: 原块上 $\hat\Omega\,2$ 满足 `Reg`, 退化坐标在内 (`RR4RegOmega2.Ω₂-reg`); 第十轮的反例不在读回域里 (`RR4CoordRoot.x-not-coordinate`). (b) D7 最后一个反例的成因恰是链不增长: 链严格增长时同一个输出式合法 (`RR4FullAdd.growing-output-legal`).
5. **V 墙对 EBO 下界不是必经的.** 下界需要的是 "树的基本列在记号的像上逐项对应" 或 "逐点单调", 都不是值同余. 值前序在 "分支对值单调" 的片段上仍有反例 (`RR4MonoFragment.mono-fragment-not-cong`); 逐点前序在第 1 层成立 (`pointwise-mono₁`).
6. **对 "让树自足".** 证据支持 "证据随坐标或构造携带", 不支持 "从任意合法树事后恢复证据". 这与 C 线的 `PH` 是同一个组织原则, 但这里的证据是字面的子树路径, 不读记号.

## 1 到底证到了哪里

### 1.1 与终点相关的最强定理

| # | 定理 | 位置 | 精确陈述 | 读法 | 档 |
|---|---|---|---|---|---|
| 1 | `BTBO≈` | `OCF/Align/BTBOFull.lagda.md:101` | `tr₀ BTBO ≈ᵛ BTBOᴵ` | `src` 的 BTBO 与带标签的树序数值互相 ≼ | 定理 (已冷编) |
| 1′ | `BTBO-label` | `OCF/Align/Label.lagda.md:316` | `Lab N.BTBOᴵ (E.EBOψ 2)` | `BTBOᴵ` 的基本列与 ψ₀(Ω_Ω) 的记号逐项一致 | 定理 (已冷编) |
| 1″ | `no-lab` | `BTBOFull.lagda.md:133` | `Lab (tr₀ BTBO) (E.EBOψ 2) → ⊥` | `src` 的 BTBO 自己不带这个标签 | 定理 (已冷编) |
| 2 | `vv-ω²` | `OCF/Align/EmbVVInstO2.lagda.md:346` | `VV (V end zero) tω²` | 见下 | 定理 (已冷编, 14G) |
| 3 | `closed-value` | `OCF/Align/TreeEmitBuildAccept.lagda.md:40` | `VV closed tω²` | TreeEmit 的闭项与第 2 行的树 `≅` (`All.new-old`), 继承同一验收 | 定理 (已冷编, 14G) |
| 4 | `labelled-strict-lower` | `OCF/Align/CrossMHighSeedAccept.lagda.md:57` | `Σ R. Lab R tω² × (suc R ≼ T⊤ᶜ ω²ᶜ)` | `T⊤ᶜ ω²ᶜ` 严格高于带标签 ψ₀(Ω_{Ω·ω²}) 的树; **只有下界** | 定理 (已冷编, 14G) |
| 5 | `omega-lower` | `OCF/Align/TotalValueHighOmega.lagda.md:56` | `plus-omega N.BTBOᴵ ≼ Accept.read (proj₁ Final.closed)` | 改值闭项 ≥ ψ₀(Ω_Ω)+ω; **只有下界** | 定理 (已冷编) |
| 6 | `closed` | `OCF/Align/RadicalValueNativeFinal.lagda.md:64` | `closed : Object` (`Object = Σ Cd LgB`), 附 `View`, `FGH` | 这是定义 (闭项, 合法性, 内部视图), 不是强度定理 | 已冷编 |
| 7 | `step-T₁` | `OCF/Align/SumOneAccept.lagda.md:220` | `suc BTBOᴵ ≼ trA T₁` | 差树 `T₁` > ψ₀(Ω_Ω); **只有下界** | 定理 (已冷编) |
| 8 | `epsilon-in-grid` | `OCF/Align/GridBaseTowerAccept.lagda.md:27` | `Accept.epsilon ≤ᵛ Grid.closedGrid` | OutputDriven 的方格闭项 ≥ ε₀; **只有下界** | 定理 (已冷编) |
| 9 | `full-EBO` | `OCF/Align/DirectedViewDirectClosed.lagda.md:54` | `(R.reference ≤ᵛ closed) × (closed ≤ᵛ R.reference)` | 完整 EBO, 双向; **闭项读记号与记号的良基证明, 不满足纲领 4** | 定理 (已冷编) |

第 2 行的读法. `VV X t = Σ Y. Lab Y t × (X ≼ Y) × (Y ≼ X)` (`ValLabPos.lagda.md:59`): 存在一棵基本列与项 $t$ 逐项一致的树 $Y$, 与 $X$ 序数值互相 ≼. `tω²` (`OrdLabRead.lagda.md:62`) 是 ψ₀(Ω_{Ω·ω²}) 的项. 所以:

- **序数值互相 ≼**: 主线树 `V end zero` 对 ψ₀(Ω_{Ω·ω²}). 这是树侧最高的值验收.
- **Lab 基本列一致**: 是参照树 $Y$ 带的, 不是主线树带的.
- **条件**: 无. 模块无参数; 我对它的 285 个模块的导入闭包做了文本扫描, `Funext` 只在一处讲解文字里出现, 不在代码里.

### 1.2 没有的东西

- **没有** 对任何记号无关的 $T$ 的 `reference ≤ᵛ T`. 核对方式是文本检索 `reference ≤ᵛ` 的全部出现: 以 `TerminalFoldAccept.reference` 为左端的无条件闭定理, 只有参照自身, 以及两个读记号的闭项 (第 9 行, 与同形的 `DirectedViewBuildClosed.full-EBO`, 后者未冷编). 其余出现要么是条件定理 (如 `BoundedCompletionStageWfEbo`), 要么左端是文件内另行定义的低参照 (如 `GeneralOmegaStrengthActual`).
- **没有** `T⊤ᶜ ω²ᶜ` 的上界, 也没有比 ψ₀(Ω_{Ω·ω²})+1 更高的下界. README 写它 "读 ψ₀(Ω_{Ω²})" 是判断.
- **没有** 改值闭项对 ψ₀(Ω_{Ω·ω²}) 的下界. 它的编译下界是 ψ₀(Ω_Ω)+ω.
- 其余闭项 (`HtFeed`, `HtTower`, `DiagK`, `FamFold`, `EvFold`, `CRw`, `RecB`, `Third`) 的读法我没有找到值定理, 也没有复核它们的闭项.

### 1.3 禁用构造

对 `probes/OCF` 下全部 `.lagda.md` 的 Agda 代码块扫描 `postulate`, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `{!`, `with-K` 等: 0 处. 我冷编的每个模块都有 `--safe --without-K` (`--safe` 模块只能导入 `--safe` 模块, 由检查器保证).

## 2 壁垒到底挡住了什么

### 2.1 W: 下标的比较

**`Barrier.barrier : Ω-Extension → LPO`** (`OCF/Barrier.lagda.md:262`, 定理 (已冷编)).

前提 (`Ω-Extension`, 第 244 行) 要同时有:

1. 类型 `I` 与传递、无自反的 `<ᴵ`;
2. `ι : Ordᴰ → I` 严格保序;
3. **精确**: `z <ᴵ ι (lim f)` 推出某个 `n` 使 `z <ᴵ ι (f n)`;
4. `top`, 在整个 `ι` 的像之上;
5. **有界三歧**: `a <ᴵ c → b <ᴵ c → a <ᴵ b ⊎ b <ᴵ a ⊎ a ≡ b`.

前提可满足性: 朴素的 `Ord₁` 除第 5 条外都满足 (`naive-barrier`, 第 384 行), 且它的第 5 条可直接反驳 (`¬naive-trich`, 第 416 行).

| 它否定的 | 它不否定的 |
|---|---|
| 以全体可数树为精确初始段、其上还有元素、并且对有公共上界的任意两元素三歧的下标类型 | 层号类型到 Λ (`LevelFixVal.Legal-Λ`, 第 290 行, 已冷编) |
| 于是: 用 "下标的有界三歧" 派发的折叠, 下标到不了 Ω 之上 | 序只在字面第一位置上的设计: 同一合法界下第一位置可比 (`YiLevelCompare.compare`, 第 29 行; `bounded-compare`, 第 51 行, 已冷编). 那里可数树不是这个序的初始段, 第 3, 4 条不成立 |
| | 带证据的部分折叠; 只在陈述里出现、不被派发读取的值关系 |

同族的定理与各自的前提:

| 定理 | 位置 | 前提 | 结论 | 档 |
|---|---|---|---|---|
| `dec≈→LPO` | `Value.lagda.md:312` | 第 0 层任意两棵树的值相等可判定 | LPO | 已冷编 |
| `dec→WLPO` | `Stage2.lagda.md:350` | `a ≺ᴵ suc ωᴵ` 对一切 `a` 可判定 | WLPO | 已冷编 |
| `total-ψ→WLPO` | `TreeLevelsO7.lagda.md:187` | raw 扩张 `TΩ+1` 上的全函数折叠同时满足保留、同层、在上三条方程 | WLPO | 已冷编 |
| `strict→LPO` | `BrwViewNeg.lagda.md:84` | 内部视图的 ℕ-极限按**值**严格, 且载体里有 0/1 部分和极限的一族对象 (`Enc`) | LPO | 已冷编 |
| `upd→wdec` | `CohWUpd.lagda.md:51`, `DiagKLev.lagda.md:90` | 以裸下标为定义域的世界有逐点更新 (`at`, `off`) | 下标相等的弱判定 | 已冷编 |
| `no-wide-compare` | `YiDispWideAudit.lagda.md:57` | Ω₁ 之下两个经分支的位置有三分 | ⊥ | 已冷编 |

`total-ψ→WLPO` 的范围要特别说明: 文件自己写明它的 `Common` 对任意层号对都能构造, 不是合法公共界; 它不覆盖带证据的部分折叠与只在生成域上满足方程的折叠. 所以它不是对乙线的否定.

### 2.2 V: 折叠不是值的函数

**`Value.ψ⁰-not-cong : Ω₁ ≈ᵛ Ω₁′ × ¬ (ψ⁰ Ω₁ ≼ ψ⁰ Ω₁′)`** (`Value.lagda.md:286`, 定理 (已冷编), 无前提).

- `Ω₁′` 的分支是 `g`: `g (suc zero) = zero`, 其余恒等. 两个结点的上确界相同. 规则 6 的链从 1 起, `1 ↦ ψ(g 1) = ψ(0) = 1` 不动 (`stall`, 第 276 行), 于是 `ψ⁰ Ω₁′ ≼ 1` (第 280 行).
- **它否定的**: `Level.ψ⁰` 对一切第 1 层的树是 ≈ᵛ 的同余, 或对 ≼ 单调.
- **它不否定的**: 受限片段上的同余; 别的折叠定义; 任何下界证明; 乙线.
- 注意 `g` 不尊重值: `g` 在字面的 1 上取 0, 在同值的 `lim const 1` 上取它自己. 所以这个反例落在 "分支不是值的函数" 的结点上.

同族:

| 定理 | 位置 | 陈述 | 档 |
|---|---|---|---|
| `no-valmonoT⁺` | `TpPort2Tab.lagda.md:120` | `¬ ValMono T⁺ Lg-T⁺ _≤ᴴ_`. 反例: 常 0 分支的 Ω-极限 `Z` 与 0 在 `≤ᴴ` 下互相 ≤, 而 `T⁺ 0 < T⁺ Z` | 已冷编 |
| `ψ-not-⊑mono` | `Certified.lagda.md:254` | `suc a₁ ⊑ Ω₁ × ¬ (ψ₀ (suc a₁) ⊑ ψ₀ Ω₁)`. 结构序版本: 经一条分支在 Ω₁ 之下, 折叠后不在其下 | 已冷编 |
| `ψ⁰-mono⁰` | `Value.lagda.md:243` | 第 0 层参数: `a ≼ b → ψ⁰ a ≼ ψ⁰ b` (正面) | 已冷编 |
| `ψ-≅` | `Level.lagda.md:622` | 一切层: 结构互模拟 (Ω-结点逐点, 输入相关则分支相关) 被 `ψ` 保持 (正面) | 已冷编 |

**本次新增 (都是定理 (已冷编), 第 1 层结点):**

- `RR4MonoFragment.mono-fragment-not-cong` (第 162 行): `(Ω₁ ≈ᵛ Ω₁ˣ) × ¬ (ψ⁰ Ω₁ˣ ≼ ψ⁰ Ω₁)`. `Ω₁ˣ` 的分支是 $x\mapsto X+x$, $X=\psi^0\Omega_1$. 这个分支**对值单调** (`hX-mono`), 且 $x\preccurlyeq X+x$. 折叠值偏大: `suc (ψ⁰ Ω₁) ≼ ψ⁰ Ω₁ˣ`.
- `RR4MonoFragment.Pointwise.pointwise-mono₁` (第 78 行): 若 `∀ {x y} → x ≼ y → h x ≼ h′ y`, 则 `ψ⁰ (node h) ≼ ψ⁰ (node h′)`. 前提实例 `pointwise-instance`.

**精确的说法 (判断, 由上面几条定理支持).** 折叠沿基本列计算, 值按上确界计算. 上确界会吸收前缀 ($X+\Omega_1$ 的上确界是 $\Omega_1$) 与延迟 (分支在链经过的点上取小值), 折叠却逐点读分支. 所以折叠只对 "逐点" 的关系单调 (`ψ-≅` 是它的等价版本, `pointwise-mono₁` 是第 1 层的单向版本), 对 "上确界" 的关系不单调. 这与记号里 "基本列展开只在标准形上等于语义值" 是同一件事.

### 2.3 C 与交接文档列的五堵墙

这些都是特定架构 (种类结构 `KS`, 世界 `Wd`, C 线的 `PS`/`PH`) 上的定理. 我冷编了它们, 读了陈述, **没有**逐条核前提在各架构里的可满足性.

| 定理 | 位置 | 否定的 | 不否定的 | 档 |
|---|---|---|---|---|
| `fac-TG` 等八条 | `SkelDxGen.lagda.md:47` 起 | (正面的 `refl` 事实) 八个闭项各等于 `T⁺` 作用在某个高度上 | 没有定理说坍缩到固定类型必然有损 | 已冷编 |
| `no-cross→`, `no-cross←`, `no-route` | `CohWNeg.lagda.md:106, 110, 128` | 在 `U⋆` 的合法世界里, 同一种类的两份拷贝 (`κ0⋆`, `κL`) 的界互相推出; 以及经任何中间种类结构同时读入读出 | 链上拷贝的相干; 不产生拷贝的设计 | 已冷编 |
| `no-wmatch` | `HtTowerNStage.lagda.md:131` | 同上形状, 在 `U′` 与 `L′ 2` 之间 | 同上 | 已冷编 |
| `no-retract` | `HtTowerNeg.lagda.md:54` | 对一切 `S`, `κ`: 高度类型 `HB S` 收缩进它自己某个种类的坐标 | 塔与并 | 已冷编 |
| `fb-must-legalize` | `Lean/NegLHRecIf.lagda.md:168` | (条件正面) 若下一世界的界恒为 `hs e`, 则回灌的输出合法; 推论 `no-plain-sh` 否定 "回灌就是加法" | 带合法化的回灌 | 已冷编 |
| `keep-req`, `no-lower-rule` | `Lean/NegThirdPre.lagda.md:251, 343` | C 线 `Third` 的接口上, 留下结点带回灌时, 单调的下层规则同时满足两个世界对 | 其它接口 | 已冷编 |

## 3 乙线的状态

### 3.1 逐个核对

主张 (待核): "S3 第八轮以来的反例都是同值异形, 即 V 墙 `ψ⁰-not-cong` 的实例". 七条都已冷编, 退出码 0.

| # | 定理 | 位置 | 陈述 (缩写) | 陈述里有折叠吗 | 反例对象 | 实际失败的性质 |
|---|---|---|---|---|---|---|
| 1 | `no-keep-seed-dispatch` | `YiGammaKeep.lagda.md:57` | `KeepSeedDispatch → ⊥`. 记录要求对一切合法守卫坐标 ζ, `suc ζ` 与 Ω₁ 有第一位置公共界. 取 ζ 为 ω | 无 | ω (`lim nat`) 与 Ω₁, **都是规范写法** | (ω+1, Ω₁) 没有字面第一位置公共界 |
| 2 | `no-next-ev` | `YiDispHigher.lagda.md:97` | `DispEv (tree i) (tree one) → ⊥`, `j = lc 1 (cO 1) 0 (λ → 0)`, `i = suc (suc j)` | 无 | 分支全为 0 的 Ω-结点 (直接造的层号) | 判定型与结构型的位置证据都没有 |
| 3 | `no-omega-preservation` | `YiRegZeroLimit.lagda.md:198` | `(∀ t → Legal t → Reg t → Reg (Ω̂ t)) → ⊥`, `x = suc (lim const 0)` | 无 (`Ω̂` 是结构递归, 不是 ψ) | 常零极限的后继 | `Reg` 的根条件: `x` 不是 `Ω̂ x` 的字面子树 |
| 4 | `no-Ω-preservation₂` | `YiReg2Stop.lagda.md:90` | `(∀ x → Legal x → Reg₂ x → Reg₂ (Ω̂ x)) → ⊥`. 规范 `Ω̂ 1` 的坐标 `lim const 1` | 无 | 规范树自己的合法坐标 | `Reg₂` 新加的严格性 (`Proper 1 1`) 与原块 Raw 合法性允许自反步不相容 |
| 5 | `no-rule-preservation` | `YiLglFoldPause.lagda.md:184` | `SourceRules go points → Legalˢ (go source) → ⊥`, `source = lc 0 (cO 0) 1 (λ → 1)` | 有 (局部规则合同) | 常值 Ω 分支的结点 | 输出是常列, 不严格合法 |
| 6 | `no-omega-two` | `YiLglAllStop.lagda.md:107` | `Legalˢˢ (Ω̂ 2) → ⊥` | 无 | Raw 里常值 Ω 分支的坐标 | LF 一侧的合法性加严了, Raw 一侧的 `Lgl.lc` 没加 |
| 7 | `no-faithful-preservation` | `YiLglFullZeroStep.lagda.md:72` | 零行给 1, 忠实零步与守卫迫使链停在种子, gt 行输出常 1 列, 不满足 `Legal` | 有 (合同) | 分支严格、在种子处取 0 的源 | 链不增长 |

### 3.2 归类在定理层面成立吗

**不成立.** 逐条:

- **第 1 条不是同值异形.** 两棵树都是规范写法. 失败的是 "字面第一位置公共界", 属于 W 类. 第九轮的结构型证据已经覆盖了这一对 (`all-retained-Ω`, `YiDispCountable.lagda.md:96`, 已冷编).
- **第 2, 3, 4 条的陈述里没有折叠, 也没有值.** 它们说的是字面位置证据在全合法域上不封闭. 把反例对象描述成 "同一个值的另一种写法" 可以 (判断; 这些文件里没有 LF 上的值前序), 但失败的性质是位置证据, 不是 "折叠的值依赖写法".
- **第 5 条与 V 墙相反.** 同批的 `YiLglFoldValue.same-value` (第 62 行, 已冷编) 证明停顿的输出与正确值互相 ≤. 值是对的, 不合法的是严格性.
- **第 6 条是平行块里两处合法性定义不一致**, 四处都加严后消失 (`YiLglFullVal.Legal-Ω̂`, 第 245 行; `Legal-Λ`, 第 303 行, 已冷编).
- **第 7 条在机制上对应 `Value.stall`** (链在种子处不动). 这是七条里唯一对应的. 即便如此, 它的陈述是 "输出不满足严格 `Legal`", 不是值不等; "这个源与 Ω₁ 同值" 没有形式化.

另外, 主张里的 "八个" 与 RouteReview3 §5.9.2 的表 (七行) 及简报列的名字 (七个) 对不上.

### 3.3 这些反例实际说明了什么 (定理加判断)

**定理 (本次新增, 已冷编):**

- `RR4CoordRoot.x-not-coordinate` (第 141 行): 第 3 条的 `x` 不是任何合法守卫坐标的读回.
- `RR4CoordRoot.coordinate-root` (第 62 行): 对一切合法守卫坐标 η (退化的在内), `Below (up 0 η) (Ω̂ (up 0 η))`. 证据是坐标自己.
- `RR4RegOmega2.guarded-reg` (第 95 行), `Ω₂-reg` (第 137 行): **原块上, 用第十轮冻结的 `Reg`, `Ω̂ 2` 满足 `Reg`**, 它的全部合法守卫坐标 (含常值分支的结点 `junk-reg`) 的读回都满足. 此前仓库里规范的 `Ω̂ n` 满足 `Reg` 的闭实例只有 `Ω̂ 1` (`YiRegInstances.tower2-reg`, 第 63 行).
- `RR4FullAdd.growing-output-legal` (第 44 行): 第 7 条的同一个源、同一个输出式, 若链点在坐标上严格增长, 折叠保持严格第一位置与合法性, 则输出合法. 前提实例 `instance-legal`. `not-both` (第 101 行): 链固定与链增长互斥.

**判断:**

- 第 2, 3 条的反例是 "直接造出来的层号", 不是规范结点的坐标读回. 第十轮到 D7 的严格化, 是为排除读回域之外的反例而加的; 在读回域上, 不加严格性的 `Reg` 在 `Ω̂ 1`, `Ω̂ 2` 上成立.
- "对一切合法树量化" 的封闭定理, 对字面位置证据来说目标定错了. 一棵层号若不是字面地由读回给出, 证明 "它的后继字面地出现在 `Ω̂` 里" 要一个极限函数的字面相等, 没有函数外延时既证不出也否定不了 (第 3 条用了一个能逐项区分的退化形状才得以否定). 所以该问的是 "读回域上是否封闭", 不是 "全合法域上是否封闭".
- 严格性不是纲领要求的. 终点类型 `Cd` 的合法性用的是自反的第一位置 (`CRwBase.lagda.md:56` 的 `hself`, 第 82 行的 `LgB (hl f)`); 按值严格反而推出 LPO (`strict→LPO`).

### 3.4 有没有否定乙线本身的定理

**没有.** 七条都各自写明只否定所给的接口. 最一般的 W 类定理 `total-ψ→WLPO` 明示不覆盖带证据的部分折叠. `Barrier.barrier` 的精确性前提在第一位置序上不成立.

### 3.5 乙线已有的正面定理

| 定理 | 位置 | 内容 | 档 |
|---|---|---|---|
| `Legal-Ω̂`, `Legal-Λ` | `LevelFixVal.lagda.md:228, 290` | 层号对 $x\mapsto\Omega_x$ 的合法闭包到 Λ, 一步, 不按阶段 | 已冷编 |
| 同上, 四处严格块 | `YiLglFullVal.lagda.md:245, 303` | 严格版本的同一闭包 | 已冷编 |
| `bounded-compare` | `YiLevelCompare.lagda.md:51` | 同一合法界下第一位置三路可比 | 已冷编 |
| `all-retained-reg` | `YiRegCover.lagda.md:105` | 字段层 `Reg` 时, 已保留结点的第一支与全部合法坐标都有派发证据; 目标只需合法 | 已冷编 |
| `Ω₂-reg`, `coordinate-root` | 本次 | 见 §3.3 | 已冷编 |

**没有的**: ψ, 回灌, 闭项, 任何值定理. P1 的 x 在乙线上没有数.

## 4 剩下的方向

RouteReview3 §5.9.3 列了四个. "只剩这几种" 是判断; 我的结论是这张表漏了至少三个方向 (§4.5 到 §4.7), 其中 §4.5 在它自己的 §5.8 里出现过, 到 §5.9.3 被去掉了.

### 4.1 V 墙的单调片段

- **支持**: `ψ⁰-mono⁰`; `ψ-≅` (一切层的等价版本); `pointwise-mono₁` (第 1 层的单向版本).
- **挡住**: `mono-fragment-not-cong`: 片段若按 "分支对值单调" 划, 同余不成立. `ψ-not-⊑mono`: 允许 "经一条分支在其下" 的规则时单调不成立. `dec≈→LPO`: 值关系不能进定义.
- **最便宜的决定性检验**: 把 `ψ-≅` 改写成单向的关系 (ℕ-极限用上确界规则, Ω-结点只许逐点, 不许 "低于某一支"), 在 `Level` 族的一切层上证 `ψ` 保持它.
  - 成功: 第一条阶段无关的值单调引理, 可作第 4 层的通用工具与代入引理的模板. 但 `Level` 族只到 ψ₀(Ω_Ω), 它不直接抬高前沿.
  - 失败 (第 2 层有编译反例): 第 4 层只能逐轨道模拟, 非逐项对应的树要到 EBO 就缺少证明手段.
- **我的判断**: 这个方向对 "达到 EBO 下界" 不是必经的. 它决定的是 "树的基本列可以与记号不同到什么程度仍能证值".

### 4.2 链靠加法增长

- **支持**: `RR4ChainAdd.escape` (第 84 行): 在 `Value` 的 `Ω₁′` 上加法链不再停滞, `ψ⁰ Ω₁ ≼ F⁺ g`. `same-on-Ω₁` (第 131 行): 在规范的 Ω₁ 上值不变, `F⁺ id ≈ᵛ ψ⁰ Ω₁`. `RR4FullAdd.growing-output-legal`: 四处严格块里 D7 最后一个反例在链增长时消失. 先例: `src` 的 BTBO 用累加, 值在 ψ₀(Ω_Ω) 处被吸收 (`BTBO≈`).
- **挡住**: 就它的用途 (合法性与不停滞) 而言, 没有编译定理挡它. `additive-not-cong` (第 187 行) 与 `additive-prefix` (第 222 行) 说明它不让折叠成为值的函数, 但那不是它的目的.
- **未证**: 完整折叠的 `StrictMap` 与 `LegalMap` (各行的互归纳); 折叠输出读成坐标并给出坐标上的增长; 高层; 值在一般结点上与原链的关系.
- **最便宜的决定性检验**: 在乙线的块上写第 0 层到第 0 层的完整折叠 (零, 后继, 极限, gt 四行, gt 行用增长的链), 证它保持合法性.
  - 成功: 乙线第一个合法的折叠, 可以对 ε₀ 一档的参照给第一个值下界.
  - 失败: 得到加法链方向的编译否定, 并知道是哪一行.

### 4.3 D8 (停顿处由值的论证兜底)

- **支持**: `YiLglFoldValue.same-value`: 已知常输出时直接返回它, 同值.
- **挡住**: 一般的停顿识别要判定链点相等; 值层面的判定推出 LPO (`dec≈→LPO`). 字面相等的判定我没有找到定理.
- **判断**: 若 §4.2 成功, 链不停顿 (`not-both`), D8 没有对象. 不必单独检验.

### 4.4 重审乙线 (坐标要范式, 范式是否即记号)

- **支持 "要限制定义域"**: 第 2, 3 条对全合法域的否定.
- **挡住 "要范式"**: `Ω₂-reg` 与 `junk-reg`: 退化坐标在内, `Reg` 成立. 没有任何定理说坐标要一值一写法. `mono-fragment-not-cong` 说明同值的不同写法折叠值不同, 但下界不需要同余.
- **最便宜的决定性检验**: 就是 §4.5 的 K1.

### 4.5 漏掉的方向: 读回域上携带证据

RouteReview3 §5.8 把它列为 "生成域", 并以 "生成的 Ω 树仍含退化坐标, 所以光靠生成域避不开" 搁置. `Ω₂-reg` 是这条理由在 `Ω̂ 2` 上的反例: 退化坐标在分支域里, `Reg` 仍成立.

- **支持**: `coordinate-root`, `Ω₂-reg`, `all-retained-reg`, `Legal-Λ`.
- **挡住**: 没有. 第 3 条的反例在读回域之外 (`x-not-coordinate`).
- **未证**: 一般层的坐标; `Ω̂ (Ω̂ 1)` 的分支 `Ω̂ (up 0 η)` 对一切可数的 η; 回灌的输出是否落在读回域里.
- **最便宜的决定性检验 (K1)**: 在原块上证 `Reg (tw 3)`, 即对一切合法守卫坐标 η 证 `Reg (Ω̂ (up 0 η))`.
  - 成功: 第十轮以来的严格化都不需要, 回到原块; 派发证据的封闭问题在规范塔上解决一层, 再对层号归纳.
  - 失败 (读回域内的编译反例): 证据必须放进守卫 `Gd`. 那要过归纳-递归块的正性检查 (`LevelFixCore` 开头记录的 `P1` 报错是同类). 若正性拒绝, 这才是乙线在这个块上的硬障碍, 而且会是一条编译事实.

### 4.6 漏掉的方向: 对现有闭项做条件覆盖 (RouteReview3 的 O1)

- **现状**: `Cover.terminal` (`TreeLevelsO1Cover.lagda.md:39`, 已冷编) 把终点下界化为解释 ι 的两条一步律. 仓库里 `GeneratedCover`/`ChainDom` 的使用只在 `TreeLevels*` 里, 只对 `LevelNoKFold` 做了诊断 (`no-ω-target`, `TreeLevelsO1Native.lagda.md:70`, 已冷编). RouteReview3 §2 O1 说的另两个候选 (`RadicalValueNativeFinal.closed`, `HtFeedClosed.TΛ`) 以及 `Third.TΛ`, `OutputDriven.closedGrid` 没有做.
- **支持**: 这些闭项都已合法并有 FGH (我只复核了第 1 节列的几个).
- **挡住**: 没有定理说其中任何一个到不了 EBO; 也没有定理说到得了. 编译下界分别只有 ψ₀(Ω_Ω)+ω 与 ε₀.
- **最便宜的决定性检验**: 对每个候选, 写 ι 到第一个需要 Ω-共尾派发的站. 第一个填不上的字段就是它的类型封顶, 这是编译事实.

### 4.7 被冷落的线

| 线 | 编译证据 | 挡住它的编译证据 | 我的评估 (判断) |
|---|---|---|---|
| 带高度族 (`EmbVV`, `LadderOrd`, `CrossM`) | 唯一有互相 ≼ 值阶梯的族: `vv-ω²`; `T⊤ᶜ ω²ᶜ` 的严格下界; `EmbVVMain.V-≃` (第 43 行, 已冷编) 是对一切高度结构 `HtB` 的值同余 | 没有. 据 RouteReview3 §4 D6 的转述, 封存依据是成本估计, 不是定理 (我没有核 RouteSeal) | 抬高 P1 的 x 最现成. 没有到 Λ 的构造; 检验: `T⊤ᶜ ω²ᶜ` 的下一个下界是否是现有定理的实例而不新增证明模块 |
| 改值闭项 (`TotalValue`, `RadicalValueNative`) | 闭项, 内部视图, FGH; ≥ ψ₀(Ω_Ω)+ω | 没有 | 值证明目前逐站. 见 §4.6 |
| 差树 `SumOne` | `T₀≈`, `step-T₁` | 没有. O8 "未走通" 的止点我未复核 | 只有下界; 上界三次未写出 |
| `TreeEmit` | `closed-value`: 保值改写 | 没有 | 不增加强度; 是 "改写后仍能继承值定理" 的一个实例 |
| `OutputDriven` | 无参数闭项与合法性 (未复核); `epsilon-in-grid` | 没有 | 值未知. 见 §4.6 |
| `DirectedView`/`DirectClosed` | `full-EBO`: 完整 EBO, 双向 | 纲领 4 (闭项读记号) | 只能作参照与 `Cover` 的实例来源 |
| C 线 (`CRw`, `RecB`, `Third`) | 闭项 (未复核) | `keep-req`, `no-lower-rule`, `fb-must-legalize` 限定了它的接口 | 无值定理. 它的 "证据随构造携带" 是 §4.5 的先例 |

## 5 推荐

**现有编译证据不足以说哪一条路线最有希望达到 EBO 下界.** 理由:

1. 记号无关的各族里, 没有一条越过 ψ₀(Ω_{Ω·ω²}) 的阶段无关值定理, 也没有到 Λ 的折叠.
2. 没有一条开放路线被编译定理否定.
3. 上一轮把方向收窄到四个, 依据是 "都归到 V 墙"; 这个依据在定理层面不成立 (§3.2).

**若要我排序 (判断, 只引编译证据):**

**第一位: 乙线, 改为 "读回域上携带证据, 链严格增长", 先在原块上做.** 证据: 层号到 Λ 的合法闭包已有 (`Legal-Λ`); 同界第一位置可比 (`bounded-compare`); `Reg` 前提下的全层保留覆盖 (`all-retained-reg`); `Reg` 在 `Ω̂ 1`, `Ω̂ 2` 上成立且含退化坐标 (`tower2-reg`, `Ω₂-reg`); 根条件在读回域上由坐标给出 (`coordinate-root`); D7 的最后一个反例在链增长时消失 (`growing-output-legal`); 导入闭包无记号. 它的弱点同样是编译事实: 没有 ψ, 没有值定理.

**第二位: 带高度族作为值的基座.** 它是唯一有值阶梯的族. 但没有任何证据说它通向 Λ.

**能决定这件事的最小检验, 按成本排:**

| 检验 | 做什么 | 成功意味着 | 失败意味着 |
|---|---|---|---|
| **K1** | 原块上证 `Reg (tw 3)`: 对一切合法守卫坐标 η, `Reg (Ω̂ (up 0 η))` | 严格化不需要; 派发证据在规范塔上可按层归纳 | 得到读回域内的编译反例; 证据须进守卫, 转去查正性 |
| **K2** | 乙线块上第 0 层到第 0 层的完整折叠, gt 行用增长的链, 证保持合法 | 乙线第一个合法折叠与第一个值下界 | 加法链方向有编译否定 |
| **K3** | 对 `Third.TΛ`, `closedGrid`, `RadicalValueNativeFinal.closed` 各写 ι 到第一个 Ω-共尾站 | 现成闭项里有候选, 余下的是第 4 层 | 每个候选的类型封顶成为编译事实 |
| **K4** | `ψ-≅` 的单向版本, `Level` 族一切层 | 第 4 层有阶段无关的单调引理 | 第 4 层只能逐轨道模拟 |

K1 与 K2 文件不相交, 可以并行; K1 的结果决定 K2 在哪个块上写. K1, K2 都成功之后, 下一个问题才是高层 (目标层不为 0, 结点层高于 0) 的派发, 那里会第一次真正碰到 "保留结点对一切坐标递归" 与回灌.

**什么情况下应当停掉乙线 (判断).** K1 在读回域内失败, 并且把证据放进守卫被正性检查拒绝. 这两件都会是编译事实. 在此之前, 按 "否定路线要有依据", 乙线只能写 "暂停", 不能写 "归到 V 墙而止".

## 6 文档与代码的不符之处

| # | 文档的说法 | 代码 | 性质 |
|---|---|---|---|
| 1 | RouteReview3 §5.9.2: 第八轮以后的反例按 "同值异形" 归到 V 墙 | 七条里机制对应 `ψ⁰-not-cong` 的只有第 7 条; 第 1 条的对象都是规范写法; 第 5 条的值是对的 (`same-value`) | 说过头 |
| 2 | 简报转述 "八个反例" | §5.9.2 的表七行, 列出的名字七个 | 计数不符 |
| 3 | RouteReview3 §5.8: "生成的 Ω 树仍含退化坐标, 所以光靠生成域避不开" | `RR4RegOmega2.Ω₂-reg`, `junk-reg`: 含退化坐标的 `Ω̂ 2` 满足 `Reg`. `RR4CoordRoot.x-not-coordinate`: 第十轮的反例不在读回域 | 判断被新定理削弱 (只到 `Ω̂ 2`) |
| 4 | RouteReview3 §5.9.3 的四个方向 | 没有 §5.8 自己列过的 "生成域"; 没有 "对现有闭项做 O1" | 漏 |
| 5 | `Value.lagda.md` §3 的读法与 RouteReview3 §5.9.3 第一行: 同余可在 "分支对值单调" 的片段上成立 | `mono-fragment-not-cong`: 两个分支都对值单调, 值相同, 折叠值不同 | 片段的刻画不够 |
| 6 | RouteReview3 §5.8: D7 的四处严格反例 "与 `ψ⁰-not-cong` 是同一现象", 因而 "D7 最后撞上的是 V 墙" | 机制 (链停在种子) 相同; 但 `growing-output-legal` 表明同一输出式在链增长时合法, 所以挡住 D7 的是链的写法, 不是 "折叠不是值的函数" | 结论说过头 |
| 7 | RouteReview3 §1.2 V: "没有一路把值证明对阶段参数化" | `EmbVVMain.V-≃` 对一切 `HtB` (模块参数) | 说过头; 实例仍按码逐个写 (我只读了 `EmbVVInstO2`) |
| 8 | RouteReview3 §2 O1: 对三个候选各写条件定理 | 只对 `LevelNoKFold` 做了; `GeneratedCover`/`ChainDom` 的使用只在 `TreeLevels*` | 未完成, 文档后文没有标出 |
| 9 | README: `T⊤` "读 ψ₀(Ω_{Ω²})" | 只有 `labelled-strict-lower` 的下界 (高一个后继) | README 已标 "判断", 相符; 这里重申 |
| 10 | 交接文档 §7: 三个大模块 "6G 载不进来, 14G 可以" | 我没有试 6G; 14G 下三个都约 41 秒通过 | 未核 |

相符的 (抽查): README 关于 D7 关闭的描述与 `YiLglFullStop`/`YiLglFullZeroStep` 的陈述一致; "P1 仍是 x = Ω·ω²" 与 §1 一致; 交接文档对 `labelled-strict-lower` "严格越过一个后继" 的说法与陈述一致; 导入闭包脚本对 `TreeEmitBuildClosed`, `RadicalValueNativeFinal`, `CrossMClosed`, `LevelFixVal`, `YiLglFullStop`, `SumOneClosed`, `OutputDriven`, `Third` 都返回干净 (脚本级, 未用 `--dependency-graph` 核对).

## 7 本次新增的实验

五个文件, 都在 `probes/OCF/Align/`, `--safe --without-K --lossy-unification`, 代码块里禁用构造 0, 无本机路径. 都以 6G 冷编, 退出码 0.

| 文件 | 所在层 | 主要定理 | 导入闭包 |
|---|---|---|---|
| `RR4MonoFragment` | 第 4 层 (`Level` 族) | `mono-fragment-not-cong`, `Pointwise.pointwise-mono₁`, `x≼ψ⁰`, `irr` | 含 `Value` (验收侧) |
| `RR4ChainAdd` | 第 4 层 (`Level` 族) | `escape`, `same-on-Ω₁`, `additive-not-cong`, `additive-prefix`, `gᴺ-mono` (条件, 实例 `ω-inf`) | 含 `Value` |
| `RR4FullAdd` | 乙线四处严格块 | `growing-output-legal` (条件, 实例 `instance-legal`), `not-both` | 无记号 |
| `RR4CoordRoot` | 乙线原块 | `coordinate-root`, `reg-root-suc`, `x-not-coordinate`, `junk-coordinate-root` | 无记号 |
| `RR4RegOmega2` | 乙线原块 | `guarded-reg`, `Ω₂-reg`, `junk-reg` | 无记号 |

各文件的范围写在文件里. 要点: 前两个只对第 1 层结点、目标层 0; 第三个只对 `YiLglFullStop.source` 一个源, 没有构造满足 gt 行的折叠; 第四个只有根条件、第 0 层坐标; 第五个只到第 1 层坐标. **没有一个抬高 P1 的 x.**

`RR4ChainAdd` 的对照表 (四个结点都与 Ω₁ 同值, $X=\psi^0\Omega_1$):

| 结点 | 原链 | 加法链 |
|---|---|---|
| Ω₁ | $X$ | ≈ᵛ $X$ |
| `Ω₁′` (`Value.g`) | ≼ 1 | ≽ $X$ |
| `node gᴺ` (字面有限数送到 0) | 未证 | ≼ 1 |
| `Ω₁ˣ` (分支 $X+x$) | ≽ $X+1$ | ≽ $X+1$ |

## 8 没有做的, 与本审查的局限

- 冷编只重查目标模块; 没有从头重编整个仓库.
- §2.3 的五堵墙只核了陈述与编译, 没有逐条核前提的可满足性.
- 没有复核 `HtFeed`, `HtTower`, `DiagK`, `FamFold`, `EvFold`, `CRw`, `RecB`, `Third`, `LevelNoKFold` 的闭项与读法; 没有复核任何 FGH 的主张; 没有复核行数与切片数字.
- "读回域上 `Reg` 封闭" 只证到 `Ω̂ 2`. K1 的结论我没有, 只有它在前两层成立的证据与一段纸面分析 (一般层里 `top` 之下是低层 `top` 的嵌入链, 应可对层号归纳).
- §3.3 关于函数外延的那段是纸面分析, 没有写成定理.
- 序数读法 (某棵树 "是" ψ₀(Ω_x)) 全部经由 `Lab` 与仓库约定的换算; 我没有独立核对记号侧 `EBO` 的定义与文献一致.

## 9 冷编复核清单

命令形状: 仓库根目录, `agda +RTS -M<n>G -RTS --library-file=<库文件> -i src -i probes <文件>`, 先删该模块自己的 `.agdai`. 一次只跑一个. 全部退出码 0.

**14G (三个, 简报原先单独允许; 恢复后的约束改为不超过 6G, 此后未再用):** `EmbVVInstO2` (42 秒), `TreeEmitBuildAccept` (41 秒), `CrossMHighSeedAccept` (41 秒).

**6G:**

- 壁垒与值: `OCF/Barrier`, `Value`, `Level`, `Stage2`, `Certified`, `BrwViewNeg`, `TpPort2Tab`, `TreeLevelsO7`.
- 强度: `BTBOFull`, `Label`, `SumOneAccept`, `TotalValueHighOmega`, `RadicalValueNativeFinal`, `GridBaseTowerAccept`, `DirectedViewDirectClosed`, `EmbVVMain`, `TerminalFoldAccept`, `TreeLevelsO1Cover`, `TreeLevelsO1Native`.
- 五堵墙与 C: `CohWUpd`, `DiagKLev`, `CohWNeg`, `HtTowerNStage`, `HtTowerNeg`, `Lean/NegLHRecIf`, `Lean/NegThirdPre`, `SkelDxGen`.
- 乙线: `LevelFixVal`, `YiLevelBase`, `YiLevelCompare`, `YiGammaKeep`, `YiDispHigher`, `YiDispCountable`, `YiDispWideAudit`, `YiRegBase`, `YiRegCover`, `YiRegInstances`, `YiRegZeroLimit`, `YiReg2Stop`, `YiLglFoldPause`, `YiLglFoldValue`, `YiLglAllStop`, `YiLglFullVal`, `YiLglFullStop`, `YiLglFullZeroStep`.
- 本次实验: `RR4MonoFragment`, `RR4ChainAdd`, `RR4FullAdd`, `RR4CoordRoot`, `RR4RegOmega2`.

除 `GridBaseTowerAccept` 外, 每次只重查了目标模块 (输出里只有一行 `Checking`). `GridBaseTowerAccept` 连带重查了四个依赖 (`OutputDrivenGrid`, `GridBaseFirst`, `GridValueBase`, `GridBaseTowerCore`), 退出码 0. 冷编 `Level`, `Value`, `Barrier` 之后, 我对两个下游模块做了热编, 都没有触发重查, 说明重新生成的接口没有使别的模块失效.

失败的编译: 实验过程中 `RR4MonoFragment` 有一次退出 42, 原因是与 `Level.below` 重名, 改名后通过. 没有把任何失败的编译当作否定的依据.
