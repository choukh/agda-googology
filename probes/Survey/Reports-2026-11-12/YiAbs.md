# 抽象理论范式的评估与试做 (YiAbs)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 09:23 至 09:41 |
| 工具调用 / agda 编译 (粗数) | 36 / 11 |
| token (usage 字段，按消息去重) | 输出 101712；新写入缓存的输入 242886；读缓存的输入 5215550；其余输入 62 |
| 写过的仓库文件 | `YiAbsFrame.lagda.md`, `YiAbsInst.lagda.md`, `YiAbsObs.lagda.md` |
| 文件前缀 | `YiAbs` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: 抽象理论一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 否定一侧统一成一条观察引理, 在框架上重推 wdec/flat→wdec/fullSem→lpo; branch→wdec 对任何树; 正面只到 exit 与 lower 的形状, add-model; 推荐作先验检查与值接口, 不改主线 (判断); 七件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一位独立评估者兼执行方。全程用中文。主审会从头冷编译复核你交的每个文件，只认编译过的定理。

###### 作者的原话（2026-11-13，请按它的范围做，不要放宽或收窄）
"我有一个想法, 希望另外单独派一路Fable 5.2评估: 我发现我们到目前为止都是直接上手写定义写各种候选, 我在想是否有必要先发展抽象理论. 基于Agda的归纳/ 归纳归纳/归纳递归类型本身的规则, 基于我们目前发现的各种关键(虽然可能不都是必要,也不知道哪些合起来是充分的)性质(如嵌入一致, 单调与保持合法等等), 直接建立抽象理论, 分析最终的形态可能的充分必要条件, 做成定理, 以此指导树的定义. 这是跟之前的研究完全不同的范式, 我不知道是更简单还是更难, 但我觉得值得试一下"

所以这一路有两件事：
1. **评估**：这种 "先抽象理论、再指导定义" 的范式，比我们一直用的 "直接写候选" 更简单还是更难？依据是什么？
2. **试做**：真的建立一份抽象理论的起点，做成编译过的定理，看它能不能说出最终形态的充分条件、必要条件，以及能不能指导眼下待定的设计选择。

同批另有四路在跑（F1 `YiFL`、F3 `YiCum`、值参照 `YiRef`、View 与 FGH `YiView`），你不动它们的文件。

###### 目标与背景（只信编译定理与条件定理；文档里的叙述与判断只是数据）
- **最终目标**：布劳威尔树上读法 ψ₀(Λ) 的合法闭项（EBO = ψ₀(Λ)，Λ 是 x ↦ Ω_x 的第一个不动点），加一条编译定理 "序数值 ≥ EBO 的参照树"（只要下界）。纲领在 `AGENTS.md`（四条不可违背）；目标是 "让树自足"。
- **我们已发现的关键性质**（都在具体块上编译过；字段名见文件）：
  - 嵌入一致（J2 一族）：`YiPhiIface`、`YiUpIface`、`YiLimIface` 的 `J2-*`；作用域块 `YiScopeSame`。
  - 单调：`mono⊥`、`monos`。
  - 保持合法：`pres⊥`、`press`；在合法块 `YiLegBlock` 里合法成了类型。
  - k 侧对一切孩子保留：`YiPhiNegK.kall-phi`。
  - 自身行上折：`YiUpIface.self-up`。
  - 有限后继层上嵌入与摊平同折叠：第十四次审查 `R14Flat` 的 `same-*`，条件定理，前提函数外延；附件 `probes/Survey/Reports-2026-11-12/attachments/Review14-R14Flat.agda.txt`。
- **已编译的否定与边界**（抽象理论最可能先说清的部分）：
  - `probes/OCF/Barrier.lagda.md`：下标类型以 Ordᴰ 为精确初始段、含 Ω 共尾元且有有界三歧，就推出 LPO。
  - `YiUniNegCmp.cmp-full→lpo`、`YiUniNegStep.step-full→lpo`、`YiPhiNegKSem.fullSem→lpo`：按层号的 "能保留处都保留" 推出 LPO。
  - `YiCtxNeg.diag1→dec`、`YiPhiNegB.wdec`、`wlpo`、`viaE→dec`、`YiUpNegFlat.flat→wdec`、`flat→wlpo`：分支侧要同支信息，就判定或弱判定字面相等。
  - `YiCompatDlLPO.lpo-tw`：摊平位置加派发下，跨层单调接口推出 LPO。
  - `YiCtxNeg.em-flat`。
  - `YiLimCheck.no-req`：反例是不合法树，读作量化域太宽。
  - `YiUpNegFlat` 边界：其余五行保留。
  - `YiOmCCheck.self-add` 与 `YiOmCVal.br0-≼`："留在孩子里" 对本层只是加法。
- **已有的抽象部件**（可作起点）：
  - 接口记录：`YiCrossIface`（跨层模拟 `Simʰ`、`Compat`、`MonoH`）、`YiPhiIface`、`YiUpIface`、`YiLimIface`、`YiUniIf`（`Full`、`At`）。
  - 终点出口 `YiMonoExit.ebo-lower`：一族对基本列封闭的（记号项，树）。
  - 通用 View 记录 `probes/OCF/Align/BrwViewDef.lagda.md`。
  - 统一值模拟 `YiUpSimRel`、`YiUpSimFold`：带上下文帧的关系族，`lower-fin`、`ω-tw1`。
- **综述**：
  - `probes/Survey/RR13-CommonWall.md`、`RR14-SelfRow.md`；
  - `probes/Survey/IdeaLedger.md` 的 V55 到 V89；
  - `probes/LOG.md` 末尾十节；
  - 主审的局势图（已发布的页面，不在仓库）概括了 17 条候选的条件矩阵。

###### 要做

**1. 先读，写 `preview.txt`**：你对这一范式的看法。抽象层次放在哪里，例如 "块" 是一个满足某些规则的归纳-递归宇宙，"折叠" 是一个带若干律的结构。哪些性质看起来是必要的，哪些合起来可能充分。

**2. 抽象框架**（新文件，前缀 `YiAbs`）：用 Agda 记录或模块参数写出抽象的 "块 + 折叠"。
- 层号、各层的树、嵌入、结点与槽位、目标路径，以及上面那些性质作为字段或假设。
- 要能把至少一个现有的具体块实填进去，例如 `YiUp` 或 `YiLeg` 的折叠，证明框架不是空的。

**3. 抽象定理**（编译），两类：
- **(a) 否定一类，最先做**：把已有的几条具体否定推广成框架上的定理。例如：任何满足框架、又满足 "分支侧同支交接" 一类律的折叠，都弱判定孩子下标的字面相等。说明它们是同一个抽象原因的实例，还是几个不同的原因。
- **(b) 正面一类**：哪些律合起来，足以推出值的下界或模拟关系。例如嵌入一致、单调、保留基底、自身行上折，推出某层上 ψ 的模拟，或者推出 `ebo-lower` 要的封闭族的一部分。能做到哪一步就做到哪一步，并写清还缺什么。
- 每个前提给出可满足的实例（AGENTS："前提要可满足"）。

**4. 指导**：框架与定理对眼下待定的设计说什么。
- Ω 结点层号的自身行：(A) 摊平有 `flat→wdec` 的损失；(C)/(C′) 留在孩子里对本层只是加法。抽象地看，这一层有没有既保同支又保值的写法？有没有否定？
- 值迁到合法块（V89）怎样做最省。
- 能编译的给定理，其余标判断。

**5. 评估**：这一范式与直接写候选各自的代价与收益，以过去两天的具体例子为证。例如哪几次反复试错，有了抽象定理可以省掉；哪些地方抽象反而更难，比如归纳-递归的宇宙在 Agda 里不好抽象。最后给推荐：主线怎样结合这一范式，或不建议。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiAbs`（模块名 `OCF.Lean.YiAbs…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 抽象框架文件尽量不导入记号与参照框架；涉及值与参照的定理放验收文件，文首标 "验收文件"。
- 中文 literate Agda（`.lagda.md`）。每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的结论标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G（另有四路在编译）。
  - 冷编译只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/abs`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；6G 仍耗尽。没有编译的否定时只写 "未走通"。归到已知的墙之前，逐条核机制。
- **过程要求**：读完先写 `preview.txt`，然后尽快动手；第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编译退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 结论：这一范式更简单还是更难，推荐怎样用（一段）。
2. 抽象框架：记录与字段的逐字陈述；实填了哪个具体块。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 判断）；否定与正面分开。
4. 充分条件、必要条件的清单，每条标档。
5. 对待定设计的指导（Ω 结点层号自身行、V89）。
6. 两种范式的代价与收益，以具体例子为证。
7. 超出定理的结论（表）。
8. 你没有读的、只凭转述引用的。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-13 09:40 (UTC)：

主审转告：同批另四路已返回，经主审冷编复核（退出码全 0，禁用构造 0）。下面只列编译事实与位置，不含主审的判断。你的范围不变（作者原话），不必重做下列已有结果，用不用由你自己判断。文件都在 probes/OCF/Lean/，回报原文在 probes/Survey/Reports-2026-11-12/<名>.md。

1. F1 折叠带合法性（YiFLBlock, YiFLLegal, YiFLFold, YiFLCoh, YiFLCheck；原型）
- 折叠带的是可计算的证据 E，不是合法性 Leg′。它与 pres⊥/press（输出带证据且非零）互递归，停机通过。
- YiFLCheck.dep : outd l₁ ≡ outd l₂ → ⊥。l₁, l₂ : Leg′ zero cd 是同一个合法下标的两个证明，给出两棵不同的输出树。
- YiFLCheck.no-keep : ((z : Tr zero) → Leg′ (tw 1) (up zero z (Ωt (h₁ z)))) → ⊥。保留行要的 "分支处处合法" 为假，反例是不合法树。
- keep-none：保留行给分支的证据没有相邻序。
- 相干证据下的 "加法保持相干"（+-dn）两种写法都过不了停机检查，首个错误是 TerminationIssue，主审已复现。附件：Reports-2026-11-12/attachments/YiFL-CohPlus.agda.txt、YiFL-CohPlus2.agda.txt、YiFL-CohTry.agda.txt。状态：未走通，没有编译的否定。

2. F3 读回取部分和（YiCumBlock, YiCumLegal, YiCumCheck, YiCumVal, YiCumValTw1, YiCumKept）
- 读回 ↑ᶜ 在 lim 处取部分和。
- 编译定理：Req-twᶜ, Req-Λᶜ, req-all, tw1ᶜ-just-all, kallᶜ, bho-tw1ᶜ。YiLim 的折叠与合法性一行不改。
- 层号值：up≼upᶜ；ωω-strict : L.suc (v↑ ωω) ≼ v↑ᶜ ωω；cof（每个累加读回与某个原读回值相同）；tw1-cof。
- 有限测试 tri：ω 的基本列从 0,1,2,3 变成 0,1,3,6。

3. 值参照（YiRefTw2，验收文件）
- closed-PH : Closed PH，其中 PH t X = Σ (HC t) λ h → Rt h ≼ X。这是 YiMonoExit 意义下的封闭，无前提。
- endpoint : (Y : T₀) → (∀ k → Rt (hc-tower k) ≼ Y) → toL EBO-tree′ ≼ Y；endpoint-sat 说明前提可满足。
- 陈述（Set，未证）：Row₂ = Rt (hc-tower 3) ≼ read (twᶜ 2)；Step₂⁺；Into n = read (twᶜ n) ≼ read EBOᶜ。
- 编译定理：row₂→btbo、row₂→step、step⁺→btbo。
- OCF.Align.Level 的层号只有 zero/suc/lim（Level.lagda.md:62-65）。给它加 Ω 结点构造子会碰 Stage2 的 dec→WLPO：执行方逐条核过，主审没有独立核。
- 执行方的未编译草图：记号直连的下界模拟 Mᴱ j t x，见 YiRef.md §5。

4. 内部 View 与 FGH（YiViewVal, YiViewInst, YiViewWf, YiViewFGH, YiViewRead）
- YiViewInst.brwView : BrwView SigY Tr (λ {i} x → val i x) (λ {i} x → Leg i x)。它在 YiFresh/YiUp 的块上，Ix = L，无前提。
- 另有编译定理：wf, vrec, objStep, emb-≈, val-incl, incl-leg, val-+, FGH-read。
- 值类型 V ℓ 去掉了 up，Ω 结点按 Br ℓ p（块的低层树）分支。

规则不变：只新建 YiAbs 前缀的文件；可以导入上述模块，但不改、不删它们的接口；同时只跑一个 agda，堆 6G。

Address this before completing your current task.

## 回报原文

第 1 份，转录时间戳 2026-11-13 09:40 (UTC)：

### YiAbs 回报: "先抽象理论, 再指导定义" 的评估与试做

交了七个新文件, 都在 `probes/OCF/Lean/`, 前缀 `YiAbs`, 共 1007 行。删自己的七个接口后按依赖次序 6G 冷编, 退出码全 0, 每份日志只有自己模块的一行 `Checking`。禁用构造与本机路径检索为 0。`importclosure.py` 对前六个模块报 OK (第七个 `YiAbsSimInst` 读记号, 是验收文件, 没有跑)。没有改任何已有文件。

#### 1 结论

- **否定一侧更简单, 推荐采用。** 现有的分支侧否定与 "能保留处都保留" 的否定是同一条两行引理 (`obs→dec` / `obs→wdec`) 的实例。差别只在被判定的命题: (E) 孩子下标的字面相等, (S) 层号上的存在命题。它还给出一条充要形状的判据: 指定孩子的交接行, 存在与否取决于孩子下标类型有没有同支证据函数。
- **正面一侧没有变简单。** 通用出口与 "步进传到值上" 都能写成定理, 但难点 (多层的对应关系 R) 原样留在前提里。加法模型 `add-model` 还说明框架里的四条结构律推不出超过加法的值。
- **推荐 (判断)。** 不把主线改成 "先理论"。把 `YiAbsObs` 与 `YiAbsFrame` 当作开新行之前的先验检查, 把 `Sim` 的前提当作值证明的接口形状。块的定义仍按具体块写。

#### 2 抽象框架

`YiAbsFrame`, 只导入 `YiAbsObs`。逐字:

```agda
record Block : Set₁ where
  field
    Lv   : Set
    Tr   : Lv → Set
    Ch   : Lv → Set
    chL  : (ℓ : Lv) → Ch ℓ → Lv
    ChT  : (ℓ : Lv) → Ch ℓ → Set
    chT  : (ℓ : Lv) (c : Ch ℓ) → ChT ℓ c → Tr (chL ℓ c)
    _⊑_  : Lv → Lv → Set
    self : ∀ {ℓ} → ℓ ⊑ ℓ
    inc  : ∀ {j} (ℓ : Lv) (c : Ch ℓ) → j ⊑ chL ℓ c → j ⊑ ℓ
    incU : ∀ {j} (ℓ : Lv) → Ch ℓ → ((c : Ch ℓ) → j ⊑ chL ℓ c) → j ⊑ ℓ
    up   : ∀ {ℓ} → Tr ℓ → (c : Ch ℓ) → ChT ℓ c → Tr ℓ
    hd   : ∀ {ℓ} → Tr ℓ → Bool
    _◃_  : ∀ {ℓ} → Tr ℓ → Tr ℓ → Set
    Leg  : ∀ {ℓ} → Tr ℓ → Set

record Fold (𝔹 : Block) : Set₁ where
  field
    Bs   : Lv → Set
    LegB : (ℓ : Lv) → Bs ℓ → Set
    Bt   : Lv → Set
    LegT : (j : Lv) → Bt j → Set
    ψ    : (ℓ : Lv) → Bs ℓ → (j : Lv) → j ⊑ ℓ → Bt j → Tr ℓ → Tr j
    ψβ   : (ℓ : Lv) → Bs ℓ → (j : Lv) → j ⊑ ℓ → Bt j → Tr ℓ → Bt j
    dn   : (ℓ : Lv) → Bs ℓ → (c : Ch ℓ) → Tr ℓ → Bs (chL ℓ c)
```

律是按层号陈述的谓词:

```agda
Hand ℓ = (b : Bs ℓ) (j : Lv) (c : Ch ℓ) (w : j ⊑ chL ℓ c) (β : Bt j) (x : Tr ℓ) (y : ChT ℓ c)
  → ψ ℓ b j (inc ℓ c w) β (up x c y)
  ≡ ψ (chL ℓ c) (dn ℓ b c x) j w (ψβ ℓ b j (inc ℓ c w) β x) (chT ℓ c y)
HandU ℓ = (b : Bs ℓ) (j : Lv) (c₁ : Ch ℓ) (ws : (c : Ch ℓ) → j ⊑ chL ℓ c) (β : Bt j) (x : Tr ℓ)
  (c : Ch ℓ) (y : ChT ℓ c)
  → ψ ℓ b j (incU ℓ c₁ ws) β (up x c y)
  ≡ ψ (chL ℓ c) (dn ℓ b c x) j (ws c) (ψβ ℓ b j (incU ℓ c₁ ws) β x) (chT ℓ c y)
Mono = (ℓ : Lv) (b : Bs ℓ) (j : Lv) (w : j ⊑ ℓ) (β : Bt j) {x y : Tr ℓ} → x ◃ y → ψ ℓ b j w β x ◃ ψ ℓ b j w β y
Pres = (ℓ : Lv) (b : Bs ℓ) → LegB ℓ b → (j : Lv) (w : j ⊑ ℓ) (β : Bt j) → LegT j β
  → (x : Tr ℓ) → Leg x → Leg (ψ ℓ b j w β x)
```

白话: `Hand` 是嵌入一致 (J2) 的指定孩子形式, `HandU` 是目标对一切孩子各给一条路径的形式。

另有 `Probe ℓ` (字段 `b j β x c₀ y w on`) 与 `Offᴾ`; 行级的记录 `Row` (字段 `C H Y X hd k fb`) 在 `YiAbsObs`。

**实填了三个:**

| 实例 | 文件 | 内容 |
|---|---|---|
| 空白页的块 + 任意 `YiPhiIface.Iface` | `YiAbsInst` (`blk`, `fold`) | `phi` (YiPhi 折叠) 与 `upφ` (YiUp 上折折叠) 都是实例。`hand-suc`, `hand-lim`, `handU-suc/lim/Ω`, `mono`, `pres` 成立 |
| 合法块 `YiLegBlock` / `YiLegFold` | `YiAbsLeg` (`blkᴸ`, `foldᴸ`) | 同名各条成立; `Pres` 平凡 (合法是类型) |
| 加法模型 | `YiAbsAdd` | 见 §3 |

框架没有表达的: 结点行 (槽位 `Pos`, `Br`, `at`, 链)、k 侧路径 `ink` (只以 `HandU` 的形状出现)、自身行上折、到第 0 层的 `ψ⊥`。

#### 3 定理表

##### 否定

| 名字 | 陈述 (逐字) | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `obs→dec` | `{P : Set} (b : Bool) → (P → b ≡ true) → (b ≡ true → P) → Dec′ P` | 布尔观察与 P 等价就判定 P | YiAbsObs | 编译定理 |
| `obs→wdec` | `{P : Set} (b : Bool) → (P → b ≡ true) → ((P → ⊥) → b ≡ false) → WDec P` | 弱形式 | YiAbsObs | 编译定理 |
| `sep→wdec` | `∀ {C} {c₀ : C} → Sep c₀ → ∀ c′ → WDec (c₀ ≡ c′)` | 在 c₀ 为真、字面不等处为假的观察, 弱判定与 c₀ 相等 | YiAbsObs | 编译定理 |
| `RowLaws.row→wdec` | `(r : Disp) → Same r → Off r → (P : Probe) → ∀ c′ → WDec (Probe.c₀ P ≡ c′)` | 同支交给孩子、异支回退且头部可分的一行, 弱判等 | YiAbsObs | 编译定理 |
| `RowLaws.viaE→dec` | `(r : Disp) → Same r → ViaE r → (P : Probe) → ∀ c′ → Dec′ (Probe.c₀ P ≡ c′)` | 经证据函数派发则判等 | YiAbsObs | 编译定理 |
| `diag→dec` | `∀ {C : Set} {c₀ : C} (E : ∀ c′ → Maybe (c₀ ≡ c′)) → IsJust (E c₀) → ∀ c′ → Dec′ (c₀ ≡ c′)` | `diag1→dec` 去掉块 | YiAbsObs | 编译定理 |
| `sep→wdecα` | `Sep c₀ → (K : Cantor c₀) → ∀ α → AllF α ⊎ (c₀ ≡ Cantor.cα K α → ⊥)` | 下标类型含康托探针时的形式 | YiAbsObs | 编译定理 |
| `sep→wlpo` | `Sep c₀ → (K : Cantor c₀) → (∀ α → AllF α → c₀ ≡ Cantor.cα K α) → WLPO` | 加反方向得 WLPO | YiAbsObs | 条件定理 (第三个前提在含函数的树上要函数外延, 没有给实例) |
| `Slot.full→dec` | `{P : Set} (tst : M → Bool) → tst m ≡ true → (o : X) → Full o → (P → Has) → (∀ q → tst (lv q) ≡ true → P) → Dec′ P` | 有同层号槽位就以它为根, 则判定夹在中间的 P | YiAbsObs | 编译定理 |
| `sig→lpo`, `lpo→wlpo` | `(o : (ℕ → Bool) → Bool) → (∀ α → Found α → o α ≡ true) → (∀ α → o α ≡ true → Found α) → LPO`; `LPO → WLPO` | (S) 的终点; 两种全知原理的强弱 | YiAbsObs | 编译定理 |
| `Fold.hand→wdec` | `∀ {ℓ} → Hand ℓ → (P : Probe ℓ) → Offᴾ P → (c′ : Ch ℓ) → WDec (Probe.c₀ P ≡ c′)` | 框架上: 某层 J2 的指定孩子形式加可观察的回退, 弱判定该层孩子下标 | YiAbsFrame | 编译定理 |
| `Fold.branch→wdec` | `(ℓ) (b) (j) (β) (c₀ : Ch ℓ) (w : (c′ : Ch ℓ) → j ⊑ chL ℓ c′) (o : Tr ℓ) → hd (ψ ℓ b j (inc ℓ c₀ (w c₀)) β o) ≡ true → ((c′ : Ch ℓ) → (c₀ ≡ c′ → ⊥) → hd (ψ ℓ b j (inc ℓ c′ (w c′)) β o) ≡ false) → (c′ : Ch ℓ) → WDec (c₀ ≡ c′)` | 对任何一棵树 o: 分支侧目标恰在一支上保留就弱判等; 不用 `Hand`, 与自身行怎么写无关 | YiAbsFrame | 编译定理 |
| `wdec′` | `Hand (tw 3) → Ωb-off I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)` (对任意 `I : PI.Iface`) | `YiPhiNegB.wdec` 由 `hand→wdec` 重推 | YiAbsInst | 编译定理; 前提实例 `off-phi`, `off-up` |
| `flat-sep` / `flat→wdec′` | `(I : UI.Iface) → NF.FlatKeep I → NF.FlatOff I → Sep c₀` | `flat→wdec` 的前提就是一个 `Sep` | YiAbsInst | 编译定理 |
| `fullSem→lpo′` | `(I : PI.Iface) → FullSem I → LPO` | `fullSem→lpo` 由 `Slot.full→dec` 重推 | YiAbsInst | 编译定理 (探针仍不在规范域, 与原文相同) |
| `phi-not-hand`, `up-not-hand` | `Fold.Hand (fold phi) (tw 3) → ⊥`; `Fold.Hand (fold upφ) (tw 3) → ⊥` | 两个现有折叠在 Ω 结点层号上都不满足指定孩子的 J2 | YiAbsInst | 编译定理 |
| `leg-wdec`, `leg-branch` | `hand→wdec`, `branch→wdec` 在合法块实例上的陈述 | 合法块上不用重证 | YiAbsLeg | 编译定理; `leg-wdec` 的前提 `Probe` 在合法块上没有实例 |
| `add-model` | `((ℓ : ⊤) → Hand ℓ) × ((ℓ : ⊤) → HandU ℓ) × Mono × Pres` (折叠 `β + x`, 嵌入 `x + y`) | 四条结构律被加法满足 | YiAbsAdd | 编译定理 (模型是玩具块, 不是具体块) |

**是不是同一个原因。**
- (E) 与 (S) 是同一模式 (`obs→dec`) 作用在两个不同的命题上, 这是编译事实。
- "(E) 不蕴含 LPO" 是判断, 没有内部定理。
- 第三类不是全知原理: `no-req`, `R-illegal`, `Ψᴹ-not-lgl` 是量化域太宽。这一归类是判断, 没有抽象定理。
- `cmp-full→lpo`, `step-full→lpo`, `lpo-tw` 归 (S) 只凭读陈述 (见 §8), 没有重推。
- 壁垒定理没有归类。

##### 正面

| 名字 | 陈述 (逐字) | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `wdec→sep`, `dec→diag`, `dec→obs`, `wdec→obs` | `(∀ c′ → WDec (c₀ ≡ c′)) → Sep c₀` 等 | 否定的逆向: 条件是恰好的 | YiAbsObs | 编译定理 |
| `rowE-same`, `rowE-off`, `eq→dec` | `(Q : Eq) → Same (rowE Q)`; `(Q : Eq) → Off (rowE Q)`; `Eq → ∀ c c′ → Dec′ (c ≡ c′)` | 有自反证据函数 (`E c c ≡ just refl`) 就写得出同支交接加回退的一行; 它蕴含判等 | YiAbsObs | 编译定理; 实例 `Eq⊤`, `Eqℕ` |
| `rowU` | `((c : C) → H c) → (c : C) → Y c → X` | 一致的目标不比较孩子 (定义) | YiAbsObs | 定义 |
| `hand-suc`, `hand-lim`, `handU-*`, `mono`, `pres` | 两个块上各一份 | 后继、ℕ 极限层号上 J2 的指定孩子形式成立; 一致目标在三种层号上成立 | YiAbsInst, YiAbsLeg | 编译定理 |
| `Exit.exit` | `∀ {P} → Closed P → ∀ {t X} → P t X → (h : HC t) → tree h ≼ X` | 对任意值前序与任意带基本列的参照系统的出口 | YiAbsSim | 编译定理 |
| `Exit.Sim.lower` | `∀ {t x} → R t x → G x → (h : HC t) → tree h ≼ v (ψ x)`; 前提 `strict`, `weak`, `r1`, `rω` | 对应 R 沿基本列走严格步或不严格步, 步在折叠后的值上成立, 就有下界 | YiAbsSim | 编译定理; 前提实例 `Fin.lower-fin` (有限序数, 只说明可同时满足) |
| `FromMono.mono-strict`, `mono-weak` | `G₁ y → x ◃₁ y → vs (v (ψ x)) ≼ v (ψ y)`; 前提 `mono`, `pres`, `str₀` | 单调 + 保持合法 + 输出层第一位置序值严格, 则第一位置序是严格步 | YiAbsSim | 编译定理; 没有在具体块上实填 `str₀` |
| `exit′`, `ebo-lower′`, `lower′` | `∀ {P} → E.Closed P → (Y : L.Ordᶜ L.zero) → (∀ k → Σ (L.Ordᶜ L.zero) λ X → P (EBOψ k) X × (X ≼ Y)) → toL EBO-tree′ ≼ Y` 等 | `YiMonoExit` 的出口是通用出口的实例; `Sim` 的结论直接接终点 | YiAbsSimInst (读记号) | 编译定理 |

**做到哪一步, 还缺什么。** 正面只到 "给出 R 与两种步就有下界"。缺的:
- R 本身 (多层的, 带上下文帧的对应; `YiUpSimRel` 是它在有限后继层号上的具体形式)。
- 结点行的链与后继行的迭代作为步的 `weak` / `strict` 证明。它们不是第一位置序的步: Ω 结点只以第一分支为前驱, 所以 `FromMono` 给不出。

#### 4 充分条件与必要条件

| 条 | 内容 | 档 |
|---|---|---|
| 必要 1 | 某层有指定孩子的 J2 且异支回退头部可分 ⇒ 该层孩子下标在探针处弱判等 (`hand→wdec`) | 编译定理 |
| 必要 2 | 经同支证据函数派发 ⇒ 判等 (`viaE→dec`) | 编译定理 |
| 必要 3 | 任何一棵树在分支侧目标下恰在一支保留 ⇒ 弱判等 (`branch→wdec`) | 编译定理 |
| 必要 4 | 按层号相等的 "能保留处都保留" ⇒ 判定槽位存在 (`full→dec`); 配探针族得 LPO (`fullSem→lpo′`) | 编译定理 |
| 必要 5 | 值的下界必须用到四条结构律以外的律 (读自 `add-model`) | 模型是编译定理, 这句读法是判断 |
| 充分 1 | 孩子下标有自反证据函数 ⇒ 指定孩子的交接行可写 (`rowE-*`); ⊤, ℕ 有 | 编译定理 |
| 充分 2 | 目标对一切孩子一致给出 ⇒ 交接不需比较 (`handU-*` 在两个块上成立) | 编译定理 |
| 充分 3 | 封闭族 ⇒ 下界 (`exit`); R + 两种步 ⇒ 下界 (`lower`, `lower′`) | 编译定理 |
| 缺口 | 必要 1 是弱判等, 充分 1 蕴含判等, 两者之间没有闭合 | 判断 |
| 缺口 | 对终点 (读法 ψ₀(Λ) 的下界) 充分的一组律: 没有 | 未走通 |

#### 5 对待定设计的指导

**Ω 结点层号的自身行。**

- 编译事实: `branch→wdec` (空白页的块) 与 `leg-branch` (合法块) 对任何输出树 o 成立。所以 (A)、(B)、(C)、(C′) 任何一种写法, 只要之后的分支侧折叠能在输出上区分同支与异支, 都弱判定 `Tr k` 上的字面相等。`flat→wdec` 是 (A) 上的这一情形。
- 编译事实: `Ch (Ωₗ k h) = Tr k` 上若有自反证据函数就判等 (`eq→dec`)。所以这一层的行只能是 "一致目标的交接" (`handU-Ω`, k 侧同形) 或 "不区分支的回退"。
- 判断: "保同支" 只剩一种不触犯上面定理的含义, 即 (C) 那种 "结点的链步在离开孩子之前做完"。这是可以的, 但外层 x 只能经 `dn` 给的底进入孩子。它的值高低不在这份理论之内, 抽象理论对 (A) 与 (C′) 的值没有给出任何定理。
- 判断: 没有 "既在之后可观察地保同支、又保值" 的写法; "之后可观察" 这一半有定理, "保值" 这一半没有。维持主审现在的取舍 (A), 理论不反对也不支持。

**V89 (值迁到合法块)。**

- 编译事实: 合法块填进同一对记录; J2 的指定孩子形式 (后继、ℕ 极限) 与一致目标形式在合法块上都以 `≡` 成立 (`YiAbsLeg`)。台账 V89 里 "≡ 比较要改用关系" 的判断, 对这几条行律没有发生。它对值文件里含极限的树是否发生, 没有测。
- 编译事实: 对框架陈述的否定在合法块上不用重证。
- 判断 (最省的做法): 值的统一模拟不要对 `YiUp` 的块写完再搬。把它写成对一个接口的定理, 接口就是 `Sim` 的前提 (两种步的 `strict` / `weak` 加 R 的 `r1` / `rω`), 两个块各实填一次。`lower′` 已经把这个接口接到终点的参照。没有做这一步。

#### 6 两种范式的代价与收益

**抽象范式省得掉的 (以过去两天为例)。**
- 同一条引理被重证了至少五次: `YiPhiNegB.wdecᵂ`, `YiUpNegFlat.wdecᴾ`, `YiCtxNeg.diag1→dec`, `YiPhiNegB.diag→dec` (与 `R13Diag` 同), `YiPhiNegKSem.fullSem→lpo` 里的 `go`。
- V79 (分支侧同支交接) 与 V83 的 (A) 侧 (`omD` → `flat→wdec`) 在抽象里是同一个 `Sep`; `branch→wdec` 先写出来的话, 对 V83 四种写法都先成立。但各文件的主体是探针 (`c₀`, `y₀`, `diag`, `nz`, 规范域核对), 抽象不省这部分。省的是 "要不要试" 的决定, 不是行数 (判断)。
- 第十三次审查把 V68 拆成三处不同; (E)/(S)/量化域三分给了一个现成的核对表 (判断)。

**抽象反而更难或没有用的。**
- 归纳-递归的块不能被量化。框架在一小时里改了两次: 填空白页的块时, 零层没有孩子, `incU` 要加一个见证孩子; 填合法块时, 偏移带证明, 要加 `Bt`, `ψβ`, `LegT`。所以框架是事后的描述, 每个新块都可能再改它; 它不能规定块怎么写。
- 结点行、槽位、链、上折没有进框架。要进就得把 `Pos`/`Br`/`at`/`fromBr` 这一套归纳-递归的结抽象掉, 没有试。值的难点全在这些行上。
- 正面定理的前提就是原来的难题换了名字 (`Closed` → R + 步)。`add-model` 是这一侧唯一有信息量的结果。
- 本路一次编译失败都没有卡在数学上, 这与抽象定理都很浅是一回事。

**推荐的结合方式 (判断)。**
- 新行的简报里加一项先验检查: 这一行的目标是指定孩子的还是一致的; 孩子下标类型有没有证据函数; 有没有 "按存在性保留"。对上 `YiAbsObs` 的三条, 对上了就不派。
- 配对否定的文件改为: 构造探针, 再调用 `sep→wdec` / `full→dec`。
- 值的统一模拟按 `Sim` 的前提定接口。
- 不另开 "抽象理论" 主线。

#### 7 超出定理的结论

| 结论 | 档 |
|---|---|
| (E) 与 (S) 是两个不同的原因, (E) 不到 LPO | 判断 |
| 量化域太宽是第三类, 不是全知原理 | 判断 (归类) |
| `cmp-full→lpo`, `step-full→lpo`, `lpo-tw` 属 (S) | 判断 (只读了陈述与 `decide` 的类型) |
| Ω 结点层号上没有 "之后可观察的同支 + 保值" 的写法 | 前半是编译定理, 后半是判断 |
| 抽象省的是决定不是行数 | 判断 |
| 框架每遇新块可能要改 | 两次实测, 推广是判断 |
| `add-model` 说明值必须靠结点行与自身行的律 | 判断 (模型不含这两类行, 也不是具体块) |

#### 8 没有读的、只凭转述引用的

- `Barrier.lagda.md`: 只读了文首, 没有归类。
- `YiCompatDlLPO`: 只读了文首与 `decide` 的类型。
- `YiUniNegCmp`, `YiUniNegStep`: 只读了陈述。
- `YiUniIf`, `YiCrossIface`, `YiLimIface`, `YiLimCheck.no-req`, `YiScope*`, `YiOmC*`, `YiUpSimRel` / `YiUpSimFold` 的正文, `R14Flat` 附件, `BrwViewDef` §2 以后: 没有读, 凡引用都来自日志、台账与两份综述。
- 主审的局势图: 没有看。
- 同批四路 (`YiFL`, `YiCum`, `YiRef`, `YiView`): 没有读。

#### 文件

- `<仓库>/probes/OCF/Lean/YiAbsObs.lagda.md` (303 行, 只用标准库)
- `<仓库>/probes/OCF/Lean/YiAbsFrame.lagda.md` (159 行)
- `<仓库>/probes/OCF/Lean/YiAbsSim.lagda.md` (139 行, 只用标准库)
- `<仓库>/probes/OCF/Lean/YiAbsAdd.lagda.md` (41 行)
- `<仓库>/probes/OCF/Lean/YiAbsInst.lagda.md` (182 行, 验收)
- `<仓库>/probes/OCF/Lean/YiAbsLeg.lagda.md` (122 行, 验收)
- `<仓库>/probes/OCF/Lean/YiAbsSimInst.lagda.md` (61 行, 验收, 读记号)
- 预览与编译日志: `<实验目录>/agents/abs/` (`preview.txt`, 各 `<文件>.log`)

第 2 份，转录时间戳 2026-11-13 09:41 (UTC)：

### YiAbs 补充回报: 对同批四路结果的处理

读了主审转来的四路编译事实。**我没有据此改动或新增任何文件, 前一份回报的定理表与结论不变。** 下面是这四路与 YiAbs 的关系; 我没有打开它们的源文件, 只凭主审转述, 所以全部是判断。

#### 与前一份回报有无冲突

没有发现冲突。逐路:

- **F1 (`YiFL*`)**: `dep` 说同一个合法下标的两个证明给出两棵不同的输出树。这与我在 V89 一节的保留一致: 我只编译了合法块上 J2 各行以 `≡` 成立 (`YiAbsLeg`), 并写明 "对值文件里含极限的树是否发生, 没有测"。`dep` 是在 F1 的块上、针对折叠带证据的写法, 不是 `YiLegBlock`; 它不推翻 `YiAbsLeg` 的任何一条, 但说明 "证明进入计算" 时输出会依赖证明, 这一点 V89 迁移时要查。
- **F1 的 `no-keep`**: 反例是不合法树, 属于我归的第三类 (量化域太宽), 不是 (E) 也不是 (S)。归类仍是判断。
- **F1 的 `+-dn` 停机失败**: 抽象框架不涉及停机, 对这一条没有话说。
- **F3 (`YiCum*`)**: 改的是读回, 折叠与合法性不动; 框架里没有读回 `↑`, 所以不相交。
- **值参照 (`YiRefTw2`)**: `closed-PH : Closed PH` 是 `YiMonoExit.Closed` 的一个实例, 而 `YiAbsSimInst` 已证明那个出口是通用 `Exit.exit` 的实例。两者可以直接相接, 我没有写这一步的代码。
- **View (`YiView*`)**: 值类型去掉 `up`、按块的低层树分支。框架的 `Block` 没有值类型, 不相交。

#### 可以接但没有做的两处

| 可接的地方 | 做法 | 为什么没做 |
|---|---|---|
| `YiRefTw2.closed-PH` 接 `YiAbsSimInst.exit′` | 把 `PH` 当作 `E.Closed` 的实例, 重推 `endpoint` | 只是重述已有定理, 不产生新信息 |
| `Sim` 的 `strict` 前提在具体块上实填 | 用 `YiViewVal` 的值与 `mono⊥`/`pres⊥` 填 `FromMono.str₀` | 要先读 `YiViewVal` 的值前序与第一位置序的关系, 超出这次转告的范围; 值得作为下一步 |

第二处如果做成, `mono-strict` 就从 "条件形状" 变成 YiUp 块上的一条值定理 (折叠到第 0 层在合法树上值严格单调)。这是判断, 没有编译。

#### 对推荐的影响

不变。四路里没有一路给出 "指定孩子的交接在 `Tr k` 上可写" 或 "四条结构律推出超过加法的值", 所以 §4 的必要条件与 §5 的指导都照旧。

#### 没有读的

四路的源文件、回报原文 (`Reports-2026-11-12/YiFL.md`, `YiCum.md`, `YiRef.md`, `YiView.md`) 与三个 `YiFL-Coh*` 附件都没有打开。
