# 按读回域的充分性与参照出口（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 03:57 至 04:35 |
| 工具调用 / agda 编译 (粗数) | 69 / 22 |
| token (usage 字段，按消息去重) | 输出 229851；新写入缓存的输入 558420；读缓存的输入 14678280；其余输入 112 |
| 写过的仓库文件 | `YiQDFold.lagda.md`, `YiQDIface.lagda.md`, `YiQDNeg.lagda.md` |
| 文件前缀 | `YiQD` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 3 件全部退出 0，禁用构造 0，导入闭包干净；充分性按读回域陈述（keepAllᴰ、sys→lowᴰ），换基上 LowKeep 的树一侧全实填，剩参照一侧（lowᴰ、low-tw1 条件）；原链一支形状被否定（no-chain₁），改成按关系支配（chain-dom） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b77/YiQD.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiQD 回报 (Opus 5.5, 按读回域的充分性与参照出口, 不读记号, 摆脱侧)

#### 1. 判决

**对纲领与目标意味着什么.** 纲领四条都没有碰。树、折叠、合法性一处没改，新文件不读记号 (`importclosure` 结果: 禁用表命中 0)。没有公理。结点处的二选一按 `kp` 的字面结果走，即折叠自己的分情形，不比较两个孩子下标，所以不落到 `obs→dec` 一族。

对目标 "树自足"，这一路是摆脱侧的一步，三处结论都由树一侧的要求逼出:
- 量化域的形状，由第一位置序与 `kp` 的字面证据定出;
- 走链一支的字段形状，用编译否定划出原形状不能有;
- 新的支配形状只用关系的六条生成规则证明。

换基行上的 LowKeep (折到低层时的保持) 仍是**条件定理**: 树一侧的出口全部实填，剩下的前提都在参照一侧，逐项见第 4 节。

**各步到哪.**
- 第 0 步完成: 临时文件 `QD0.agda` 写出按域陈述的类型，编译退出 0。
- 第 1 步完成: 证出 `SuffD`、`SuffRD`、`SuffRAD`、`sys→lowᴰ`。
- 第 2 步: 树一侧完成，参照一侧没有实填，也没有写验收文件 (原因见第 4 节)。
- 第 3 步: 剩余前提逐字段列在第 4 节。

**域的选择与理由.** 没有复用 `YiGLDom.Dom`: 它是层号与读法的域，而且读记号。主线的 `Gx` (x 就是 Ω 树) 对生成规则的前提不封闭: 结点只有第一分支在它下面。所以新写了只看树形状与 `kp` 字面结果的谓词 `KD`:
- 本层结点都在有保留证据的槽位上;
- 嵌入的原材料 `⊴` 孩子层号的 Ω 树。

后一条是补上的: 原 `EmbOut` 的 "替身支配原材料" 对任意原材料 y 陈述，我的判断是在 c = ω、d = 1 一格大概不成立 (未编译)。所以给它加了域前提 (`EmbOutD`)，旧形状可以换算成新形状 (`embOut→D`)。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 保持只对域里的树陈述; 域对放宽、后继、结点分支、嵌入左项封闭; 回退行和换基行各有域条件 | `YiQDIface` 的 `SuffD.keepAllᴰ`, `SuffRD.keepAllᴰ`, `SuffRAD`, `sys→lowᴰ` | 编译定理 |
| 新接口的前提可满足 (玩具模型, 域取全体) | `YiQDIface.ToyD.toy-lowᴰ` | 编译定理 |
| 主系统的结点出口只剩保留一支, 树一侧实填 | `YiQDFold.QDPack.ntᴮ` | 编译定理 |
| 辅助系统结点出口的树一侧实填 (有证据走保留, 无证据走折叠自己的链) | `YiQDFold.QDPack.WithRules.ntᴬ` | 编译定理 |
| 原 `Out` 链一支的 `⊴` 形状在 k = 1 处不成立 (最小实例, 折叠自己的链) | `YiQDNeg.Min.no-chain₁` | 编译定理 |
| 链一支改成 "按关系支配" 后对一切 k 成立 | `YiQDFold.AddR.chain-dom` | 编译定理, 条件是六条规则、沿 Le 向下封闭 (`leR`)、生成 |
| 替身支配原材料归到两棵 Ω 树之间 | `SubstDom.embEᴮ`, `raise→SubDom` | 编译定理 (归约); `SubDom` 本身未证 |
| 塔第 1 项的 Ω 树在域里 | `kept-tw1`, `QDTw1.Ωt-tw1` | 编译定理 |
| 参照一侧的出口对 `foldᴮ` 可满足 | 无 | 判断, 未实填 |

#### 2. 文件表

| 文件 | 代码行 / 总行 | 冷编退出码 |
|---|---|---|
| `probes/OCF/Lean/YiQDIface.lagda.md` | 255 / 349 | 0 |
| `probes/OCF/Lean/YiQDFold.lagda.md` | 217 / 313 | 0 |
| `probes/OCF/Lean/YiQDNeg.lagda.md` | 128 / 183 | 0 |

- 冷编时每个文件只删自己的 `.agdai`，日志里只有自己模块的 `Checking` 行。
- 峰值内存: `YiQDNeg` 487MB，`YiQDFold` 346MB。没有退出 251。
- 禁用构造与本机路径检索均为 0。
- 三个文件文首都标 "不读记号"，导入闭包检查通过。
- 临时文件在 `<实验目录>/YiQD/QD0.agda`。

#### 3. 定理表

`YiQDIface` 的模块参数是 𝔾 𝔻; 下面的 S、A 指 `Sys.St` 等字段, D 指域的谓词。

- **`QD.SuffD.keepAllᴰ`** (编译定理)
  `∀ {a} → WfL a → (s : S.St a) (K : S.Cxt) → S.Bdˢ s K → ∀ {t x} → R a t x → D s x → S.Q s K t x`
  白话: 回退系统满足保留律、回退律和 `OutD`，域对孩子封闭 (`dch`)，则域里每棵树上保持成立。

- **`QD.SuffRD.sys→lowᴰ`** (编译定理)
  `∀ {ℓ} → WfL ℓ → (s : S.St ℓ) (K : S.Cxt) → S.Bdˢ s K → (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (Kc : Cx ℓ j) → (∀ x → S.Φ s x ≡ ψ ℓ b j w β x) → (∀ t → S.ap K t ≡ app Kc t) → ∀ {a x} → D s x → R ℓ a x → R j (app Kc a) (ψ ℓ b j w β x)`
  白话: 换基系统 (含辅助系统上按域的保持) 的 LowKeep 只对域里的树陈述。`SuffRAD` 用 `SuffD` 填上辅助系统那一段。

- **`out→outD`、`outR→outRD`** (编译定理)
  `∀ {Le 𝓀 𝒻} (wk : Weak) (D : ∀ {a} → S.St a → Tr a → Set) → S.Out Le 𝓀 𝒻 → OutD Le 𝓀 𝒻 D`, 另一条同形。
  白话: 旧出口对任何域都给出新出口。`⊴` 经放宽推出按关系支配。

- **`assemble`、`outDT→outD`、`outRDT→outRD`** (编译定理)
  `(𝓀 : S.KeepLaw) (D : …) (nt : NodeTree 𝓀 D) → NodeRef 𝓀 D nt → NodeOut 𝓀 D`
  白话: 结点出口 = 树一侧 (`pick`、`mvR`) 加参照一侧 (`NodeRef`)。

- **`ToyD.toy-lowᴰ`** (编译定理)
  `(β K : ℕ) → K ≤ β → ∀ {a x} → a ≤ x → K + a ≤ β + x`
  白话: 在 `YiBLToy` 的模型里，新接口的前提有居民。

- **`kp-good`** (编译定理)
  `(ℓ : L) (o : Ok ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → GoodK (at ℓ p) (slTᵍ ℓ p) (kp ℓ o p w)`
  白话: `kp` 保留时，目标槽位的层号就是原槽位的层号，换型与 `slTᵍ` 交换。逐行照 `kp` 的分情形证。

- **`mv-good`** (编译定理)
  `∀ {ℓ a} (d : Dn ℓ a) (p : Pos a) → Σ (at ℓ (mv d p) ≡ at a p) λ e → ∀ z → slTᵍ a p (mvBr d p z) ≡ subst Tr e (slTᵍ ℓ (mv d p) z)`
  白话: 上折的槽位搬运也一样。

- **`AddR.add`** (编译定理)
  `(A : Tr j) → ∀ {τ y} → Rᵍ j τ y → Rᵍ j τ (A + y)`
  白话: 第 j 层的关系若由六条规则与沿 Le 向下封闭生成，则对左加封闭。

- **`AddR.chain-dom`** (编译定理)
  `∀ {X x₀} (G′ : X → Tr⁺ j) (S′ : X → X) → ∀ k {τ} → Rᵍ j τ (proj₁ (G′ (iter S′ x₀ k))) → Rᵍ j τ (proj₁ (node⁺ {x₀ = x₀} nothing G′ S′))`
  白话: 无证据结点的像是部分和极限; 第 k 个链点的像满足的关系，结点的像也满足。

- **`QDPack.kd-dw`** (编译定理)
  `∀ {x x′ : Tr ℓ} → ℓ ⊢ x ◃ x′ → KD x′ → KD x`
  白话: 域沿第一位置序向下封闭。

- **`QDPack.Ωt-in`、`Ωt-out`** (编译定理)
  `Kept (inj₁ (inj₁ tt)) → KD (proj₁ (Ωt ℓ))` 及其逆。
  白话: Ω 树在域里，当且仅当顶槽位保留。

- **`SubstDom.embEᴮ`** (编译定理)
  `Hand₁ → SubDom → ∀ {a} (s : Stᴮ a) K → Bdᴮ s K → EmbOutD sysᴮ sysᴬ keepᴬ embᴮ Le Dᴮ s K (inj₂ (rebᴮ s))`
  白话: 换基行的嵌入出口由上下文交接 (`Hand₁`) 与两棵 Ω 树之间的支配 (`SubDom`) 给出。

- **`SubstDom.raise→SubDom`** (编译定理)
  `(∀ {t} → Le t t) → (∀ (c : Tr k) {u} → Rᵍ (h c) u (proj₁ (Ωt (h c))) → Rᵍ (j ⊕ offsets S c) u (proj₁ (Ωt (j ⊕ offsets S c)))) → SubDom`
  白话: Le 自反时，`SubDom` 归到 "Ω 树上的关系沿层号抬高保持"。

- **`WithRules.lowᴰ`** (条件定理, 条件见第 4 节)
  `OutRDT sysᴮ sysᴬ keepᴬ embᴮ Le keepᴮ Dᴮ ntᴮ → OutDT sysᴬ Le keepᴬ fallᴬ Dᴬ ntᴬ → (β : Tr⁺ j) (K₀ : Cxtᴮ) → Bdᴮ (rt β) K₀ → (Kc : Cx ℓ j) → (∀ t → apᴮ K₀ t ≡ app Kc t) → ∀ {a x} → KD x → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (BS.ψ ℓ o r B j w β x))`
  白话: 换基行上 `YiBSFold.ψ` 的 LowKeep 对域里的树成立。

- **`kept-tw1`** (编译定理)
  `∀ {d} → NZ d → Σ … → kp (tw 1) (Ok-tw 1) (inj₁ (inj₁ tt)) (inc d self) ≡ just (q , cv , e)`
  白话: 塔第 1 项，目标 `h₁ d`，顶槽位保留。

- **`QDTw1.low-tw1`** (条件定理, 条件同 `lowᴰ`)
  `… → ∀ {a} → Graded.R 𝔾 (tw 1) a (proj₁ (Ωt (tw 1))) → Graded.R 𝔾 (h₁ d) (Laws.app 𝔾 𝔻 Kc a) (proj₁ (BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B (h₁ d) (inc d self) β (proj₁ (Ωt (tw 1)))))`
  白话: Ω 树上的实例。

- **`YiQDNeg.Min.noEv₁`** (编译定理)
  `Aux.Evᴬ j₁ s₁ p₁ → ⊥`
  白话: 最小实例里，换基层号的 Ω 树顶结点不保留。

- **`YiQDNeg.Min.no-chain₁`** (编译定理, 模块参数 `o : Ok a₁`)
  `Φ (gᵃ (zᵃ 1)) ⊴ᵗ Φ (proj₁ (Ωt a₁)) → ⊥`
  白话: 沿折叠自己的链 (`iter S x₀`)，第 1 个链点的像不 `⊴` 结点的像。实例是 j₁ = `h₁ 1`，a₁ = j₁ ⊕ ↑1，底值 1。
  证法: 不变量 "有限数，或以第 0 个链点的像为左前缀" (`P-dw`) 沿第一位置序向下封闭。结点的像满足它，第 1 个链点的像不满足。

- **`YiQDNeg.reach₁`** (编译定理, `refl`)
  白话: 这个状态就是 `YiBLFold.Main.Srᴮ` 在塔第 1 项、孩子 1、x = 0 处的换基状态。

#### 4. 第一个障碍, 以及 LowKeep 剩下的前提

**第一个障碍: 参照一侧的出口没有实填。**
- 工程上挡住: 没有 `Graded blkᵍ foldᴮ rowsᴮ` 的实例。主线的 `gradedᵍ` 建在 `foldᵍ` 上，而 `Graded.Bd` 依赖 `Bs` 的类型。我的判断是可以照 `gradedᵍ` 的 `Bdᵍ` 写一份，`Bdᵍ` 不用 `Rb`，但未做。
- 数学上未知 (判断, 未编译): 下面两条在记号一侧是否成立。
  - `SubDom`，或它的充分形式 (Ω 树上的关系沿 `floor ⊕ b → j ⊕ b` 抬高保持)。最可疑的是层号值相同而结构不同的格，例如 c = ω、d = 1 的 `h₁ ω` 与 `h₁ 1 ⊕ ↑ω`。
  - 辅助系统 `NodeRef` 的走链一支: 参照链 γ 落在折叠自己的链 z 下面，上下文的余尾是 ω。

**剩下的前提 (全部在参照一侧)**
- 主系统 `OutRDT`:
  - `zeroE`、`succE`、`limE`、`leE`;
  - `nodeR`: 结点只有保留一支 (`pickᴮ` 恒为 `inj₁`)，剩三项: `CΩ (apᴮ K t) κ`、代入与上下文交换、`Nu j slot κ`;
  - `embE`: 可由 `Hand₁` 与 `SubDom` 给出。
- 辅助系统 `OutDT`:
  - `zeroE`、`succE`、`limE`、`upE`、`leE`;
  - `nodeR` 保留一支: 同上三项;
  - `nodeR` 走链一支: γ、`Cω (apᴬ K t)`、`fsn` 交换、`R (at p) (γ k) (slTᵍ (iter S x₀ k))`。
- 关系的律: `Weak`、`Lim`、`Node`、`Zero`、`Succ`、`Emb`、第 j 层沿 Le 向下封闭 `leR`、各层 `Gen⁺`。

**已实填 (树一侧)**
- 两个系统的保留律、辅助系统的回退律、主系统的换基律、单调 (都来自 `YiBLFold`);
- 两个系统的域及其封闭性、`rowD`、`dch`;
- 两个系统的 `NodeTree` (`pick`、`mvR`);
- 塔第 1 项 Ω 树在域里、`WfL`。

与 `YiBLFold.lowᴮ` 相比: 那里 `OutR` 和 `Out` 整个是前提，其中 `nodeE` 的树一侧没有填，走链一支是 `no-chain₁` 否定的那种形状。

#### 5. 翻译账、偏离与事故、未读的东西

**翻译账**
- 新定义的来源:
  - `KD` 由树侧逼出: 主系统孩子槽位不保留 (`main-noEv`)，换基行不递归进孩子树。按 AGENTS，量化域取规范读回域。
  - `OutD` 的链一支形状由第一位置序与部分和极限逼出，配对否定是 `no-chain₁`。
  - `add` 只用六条生成规则。
  - 都不来自记号的基本列。
- 脚手架:
  - `GoodK`、`kp-good`、`mv-good` 约 45 行，是接口要求的槽位簿记，不是序数值所需，也不是翻译;
  - `NodeTree`/`NodeRef` 拆分只是接口重排;
  - `SuffD`/`SuffRD` 重复了 `FI.Suff`/`BL.SuffR` 的证明骨架，约 80 行。
- 加深翻译的标志: 没有新构造子; 没用 `Lab`; 闭包定理多出的前提 "域" 是通用的，不按阶段定制，玩具里取全体。
- 提供信息的标志: `kp-good` 是按 `kp` 逐行的一步定理; `no-chain₁` 用否定划出不能有的字段。

**合并候选 (未动已有文件)**
- `YiBLFold.trR` 是 `byGood ∘ kp-good` 的特例;
- 旧的 `Suff`/`SuffR` 是新版本在域取全体、链一支取 `⊴` 时的特例 (由换算定理 `out→outD`、`outR→outRD` 表明);
- `YiDecFlat.kp-at` 是另一块上的同类引理。

**建议记入台账的候选**
- `Out` 的链一支改成按关系支配;
- `KD` 作 `Gx` 的候选;
- 结点出口分成树一侧与参照一侧两部分。

**偏离与事故**
- 加了 `EmbOutD`: 原计划是直接复用 `EmbOut`，理由见第 1 节。
- 有一次编译套了 `/usr/bin/time`，显示的退出码 1 是 time 被沙盒拦下 (sysctl)，不是 agda 的; 当次 agda 报的是作用域错误，改后正常重编。
- 没有堆耗尽，所以没有读 `EBOHandbook` 4.2、4.6 节与 Bedrock 性能手册。
- 没有写验收文件。
- 没有改任何已有文件，也没有提交。

**未读、只凭简报转述的东西**
`YiBCCover`、`YiBCNeg`、`YiBCReach`、`YiBCSync`、`YiSV*`、`YiHCOmega`、`YiBSFam`、`YiRKCell`、`YiCTCall`、`YiDGDiag`、`YiDGCell`、`YiMXNote`、`YiKWObjects`、`YiC1Slot`，以及台账 V287、V96。本路的结论都不依赖它们。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：按读回域陈述的充分性与参照出口（不读记号，兼作摆脱侧）（前缀 YiQD，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路不读记号（验收文件除外），是这一批的摆脱侧。同批另三路与你互不导入。AGENTS："量化域先取带证据的读回域"。

#### 作者的决定与背景（2026-11-17）
- 作者已关闭现行折叠上同步对象那一步链步（台账 V287），依据是两份先读定义的 Fable 5.2 封存审核。**主线定义不动**；改树、折叠、合法性只在新文件里做候选；换基进主线由作者定。
- 第七十七批作者选四路（选项原文）："替身值的后继一步 StepS (Recommended), 按读回域的充分性与参照出口 (Recommended), 替身码域加嵌入码 (Recommended), Fable 先读定义审查换基候选"。前缀 `YiZS`（Fable 5.2）、`YiQD`（Opus 5.5）、`YiEM`（Opus 5.5），以及审查 E 路（Fable 5.2，只在临时目录），互不导入。
- **换基候选的现状（第七十五、七十六批，主审冷编复核过；都在 `probes/OCF/Lean/`）**：
  - 换基折叠 `YiBSFold`（`BS.ψ`；换基行在 `route` 落在地板之上时对一切孩子 c 同形：在 `j ⊕ offsets S c` 上重建 Ω 树经 `seen` 沿 `lift` 朝原目标折，原孩子树只进低层尾项，`YiBLFold.row-reb`）；证据 `YiBSBase`（`Schema`、`split`、`rbO`、`rb-tw`、`seen`）；替身码 `YiBSRead`（`Read`、`read`、`Domain`）；核 `YiRBSib`。
  - 证据覆盖（`YiBCCover`）：读回域上处处满（`full-sync`、`Chain.full-chain`、`full-kl`、`full-kl-child`、`full-rbO`、`full-↑`、`rb-row`、`full-row`）；变量层号上给不出（`YiBCNeg.no-sync`，谓词太宽）；嵌入块到达换基行而不在码域里（`YiBCReach.reach`、`yₑ∉`，ω 代替链点；`YiBCNeg.emb∉read`、`∉dom`）。`YiBCSync.a₁-eq`、`chain-eq`：`YiRKChain` 的副本与原定义逐字相等。
  - 律（`YiBLIface`、`YiBLFold`，不读记号）：换基律 `RebAt`、嵌入律 `EmbLaw`、出口 `OutR`；`SuffR.keepAll`、`sys→low`、`SuffRA`；换基折叠满足树一侧全部律（`rebᴮ`、`keepᴮ`、`keepᴬ`、`fallᴬ`、`monoᴬ`、`monoᴮ`）；`lowᴮ`、`lowᵗ`（LowKeep，前提只剩参照一侧：`OutR`、辅助系统的 `Out`、`Gen⁺`、`Weak`、`Lim`、`Node`）；`ev-cp`、`nodeE-cp`（目标槽位副本由 `lift` 实填）；`top-noEv`、`main-noEv`（替身自己孩子层号的槽位、主系统孩子槽位不保留）。YiBL 判断的下一处障碍：(1) 主系统 `OutR.nodeE` 在 ℓ 层孩子槽位上只能走链，而 `SuffR` 对一切树陈述，要改成按读回域陈述；(2) 辅助系统 `Out.nodeE` 走链一支要 `∀ k → Φ s (g (z k)) ⊴ Φ s (nd p g)`，对部分和极限在 k ≥ 1 处可能不成立。底层接口 `YiFIIface`（`Suff.keepAll`、`sys→low`、`Out`）与 `YiAbsG*`。
  - 值（`YiSV*`）：替身对偏移沿字面路径单调（`YiSVMono.Mono.mono-path`、`seen-mono`、`seen◃`，不读记号；与 `YiLTLift.upS`、`upL` 同形，未合并）；目标孩子 ω 时非零各支承载 ψ_ω(Ω_{ω+1})（`YiSVOmega.branch-nz`、`seen-ω`，参照关系 `YiHCLim.Lim.Mω`）；顶结点承载 ψ_ω(Ω_{Ω₁}) ⇐ 后继一步 `YiSVRed.Red.StepS`（`top-red`、`branch-red`、`liftC`），`StepS` 的结论在 η ≤ ω+1 成立（`step-low`），η = ω+2 处缺 "目标层之上两层" 的保持（`ℓ₊` 上折到自身的保持，`YiHCOmega.Tω.upB` 一类；跨两层的下折保持，`YiBSFam.LF` 在 ℕ 极限底座上的对应物）；字面延伸 ω 的分支要 ω+ω 一类 ℕ 极限层号上的关系族（`YiHCLim.Lim` 只要有限孩子 `fn (d n)`）。
  - 比较表一路的否定：`YiRKCell.no-ωᵉ`、`YiCTCall.cell`、`YiDGDiag.ColW.wdecα`、`YiDGCell.cell→wdecα`。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 本路的问题
`YiBLFold.lowᴮ` 把换基折叠上的 LowKeep 归到参照一侧的出口。YiBL 指出：`SuffR`（以及 `YiFIIface.Suff`）对一切树陈述，而主系统孩子槽位上的结点不保留（`main-noEv`），出口在那里只能走链；读回域里的树（例如规范树 `Ωt ℓ` 在 ℓ 层只有顶结点）不含这些结点。所以要把充分性改成只对读回域里的树陈述，再实填出口。

#### 要做的（按序）
0. **量化域与最小检查**：选读回域的谓词（复用 `YiGLDom.Dom`，或写一个只看树形状的谓词，说明理由），写出 "按读回域的充分性" 的陈述（仿 `SuffR.keepAll`，加 "树在域里" 的前提，并要求域对出口里递归到的子树封闭）。在临时文件里编译类型。不成立就停下回报。
1. **证充分性**（复用 `YiBLIface`、`YiFIIface`、`YiAbsG*`，不重写）。
2. **实填出口**：在换基折叠（`YiBLFold`）与读回域上实填 `OutR` 与辅助系统的 `Out` 能实填的字段，尤其 `nodeE`（主系统的结点只剩顶结点；辅助系统副本一支已由 `nodeE-cp` 给出）与走链一支对部分和极限的那条（YiBL 判断 k ≥ 1 处可能不成立：先在最小实例上判定，成立就证，不成立写成编译否定，说明是 `Out` 形状的问题）。参照一侧要读记号的字段放验收文件。
3. 交：换基上的 LowKeep 还剩哪些前提（逐字段），哪些已实填；翻译账。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M6G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 6G（同批另有四路，外部广撒网也可能在编，机器共 64G；峰值超过 4G 先改形状）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
- **停下的条件**：退出 251 时不原样重跑，先按 C-9、C-10、S-1 改形状并定位（附 profile 或二分数据）；改过形状后同一上限仍撞墙才停。同一处两次重新设计仍过不了检查器也停。若某一步要改树、折叠或合法性的定义，停下回报。没有编译的否定时只写 "未走通"。
- **过程**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。动手证一般形式之前先用临时文件检查前提可满足；已有引理先检索（`grep`）再写，不重证，搬来的证明在文首写明来源。查签名用检索，不整篇读大文件。
- 不在你的临时目录与你前缀的新文件之外写、删、移任何东西；不 `pkill`，不写 `/tmp`，不装包，不提交，不改 `probes/README.md`、`probes/LOG.md`、台账与留档。
- **两条已更正的事实**（不要再照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧非标准形项的项序单调，**不是**树侧折叠的跨层单调（树侧跨层单调目前没有编译的否定）；`YiKWObjects.kept` 是新封装的对象，与 `YiC1Slot` 不透明块里的 `kept` 不是同一个。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0；文首标 "不读记号" 的文件用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包。

#### 回报（最后一条消息就是回报，主审会原样留档）
1. 判决：先说对纲领与目标意味着什么；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理；是数学上挡住还是工程上挡住。
5. 偏离与事故；没有读、只凭转述引用的东西。
不用 "只差"、"自然" 一类形容；判断与定理分开写。

