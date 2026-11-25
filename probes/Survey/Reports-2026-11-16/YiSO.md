# 核心：证 LowSlot（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 06:36 至 07:00 |
| 工具调用 / agda 编译 (粗数) | 35 / 6 |
| token (usage 字段，按消息去重) | 输出 129855；新写入缓存的输入 297676；读缓存的输入 4965710；其余输入 58 |
| 写过的仓库文件 | `YiSOEnd.lagda.md`, `YiSOLow.lagda.md`, `YiSOTw1.lagda.md`, `YiSOUp.lagda.md` |
| 文件前缀 | `YiSO` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0（均为验收文件）；LowSlot 换成带树的域的多目标系统，回退行、链步、保留与参照一致的结点对一切层号一次归纳证出（Main.lowAll、UpAll.upAll，条件定理）；余下三条前提：保留判定与参照不一致的两格（NodeMis、UpMis）与换基行（RebRow），都出自对一切读法、一切树量化；与 F 路独立得到同一个反例（¬lowslot₀、¬lowslot₁）；塔第 1 项根状态的不变式无前提（root-bd1） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b80/YiSO.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-17 06:57 (UTC)：

主审补充信息（同批审查 F 路刚回来，主审已 8G 冷编三个判定件，全部退出 0）：(1) 现有两个不变式下的 LowSlot 都被编译否定：`¬LowSlot₀ : W.W₀.LowSlot → ⊥`、`¬LowSlot₁`。反例是层号 nd sS (λ _ → zero)、默认底 B₀、K = 1、零树，结论要 R zero (ψ₀(1)) (suc zero)。另有 `Need.base-need`：任何使 LowSlot 成立的不变式，都推出 "槽位层的底对着 ψ_κ(K)"。(2) 加强后的不变式 `Inv⁺`（底值条件 + 每个槽位 p、每个允许的 κ，槽位层的底对着 ψ_κ(K)）下，接线能合上：`inv-step⁺` 可由 `LowSlot⁺` 自己供给，`Plus.ebo⁺` 的前提是 `LeafSlot` 与 `LowSlot⁺`。(3) `FCross`（形状档）：LowSlot⁺ 若对一切树、一切槽位量化，那么在塔第 2 项、孩子 0 一侧的目标槽位、孩子侧结点槽位那一格，折叠值是 ℕ 极限（`tree-lim`），而参照 ψ_{Ω₁}(X+Ω₁) 的余尾是 Ω₁（`ref-cof`），且 Ω₁ 是允许的下标（`rd-Ω₁`、`nu-p`）。审查判断这一格在值上为假，但值的否定没有编译。审查建议把量化域收到读回域：状态可达（由根与 stepᶻ 生成）、树在 Ω 树一族里、槽位是实际链步用到的几种。另提醒出口条件依赖 LowSlot 证明项里 mc 的用法（Exᴴ 要求 mc 两边是标准形且可数）。三个文件在 <实验目录>/audit/F/（FNeg.agda、FWire.agda、FCross.agda），可以读，但仓库文件不能导入临时目录；要用的话在你自己的新文件里重写。你的简报与停止条件不变；若你正在证对一切树量化的 LowSlot，请先对照这几条，按你的判断调整陈述，并在回报里写明。

## 回报原文

### YiSO 回报：核心（证 LowSlot）

#### 1. 判决

**对纲领与目标意味着什么。** `LowSlot` 没有证出，也没有被整体否定。做成的是：把它换成一个带树的域的多目标系统，其中全部回退行、链步、保留与参照一致的结点，对一切层号用一次归纳证出（不按站）；余下的义务压成三条前提（两格"保留判定与参照不一致"，一条换基行）。这是阶段无关的闭包定理的形状，但只对回退行与链步成立；三条前提没有实填，所以对 EBO 终点仍是条件定理。不改树、折叠、合法性；四个文件全是验收文件（读记号）。

**各步到哪一步。**
- 第 0 步：做完。不变式 `SlotBd` 与多目标陈述 `Keepᵗ` 已写出并编译；塔第 1 项目标 `h₁ 1` 的 `LowSlot` 与 `inv-step` 实例（`lowslot-tw1`, `step-tw1`）编译通过，是条件的。
- 第 1 步（塔第 1 项）：未走通。根状态的 `SlotBd` 无前提证出（`root-bd1`）；这一项上的 `NodeMis`, `UpMis`, `RebRow` 没有实填。
- 第 2 步（一般）：条件定理 `Main.lowAll`；第一个挡住的引理见第 4 节。没有编译出读回域内的反例。
- 第 3 步：`Wire.LowSlot` 在 `Inv₂` 下实填（`Full.lowslot₂`, `ebo-end₂`），但前提是域取全体的三条，其中 `RebRow` 我判断在值上为假，所以这一条读作前提不可满足。可用的是带域的 `End.ebo-endᴬ` / `EndU.ebo-endᵁ`，它不经过 `Wire`。还剩：三条前提、`RootBd`（n ≥ 2）、一个满足封闭条件的域、出口条件。
- 第 4 步：翻译账见本节末。

**对照主审转来的 F 路结果**（F 路的三个文件我没有读，只凭转述对照）：
- `¬LowSlot₀/₁` 与我的 `¬lowslot₀/₁` 是同一个反例（层号 `nd sS (λ _ → zero)`、`B₀`、K = 1、零树），两路独立得到。
- `Need.base-need` 对应我的 `slot-needed`；`Inv⁺` 对应 `Inv₂`（我多带一项 `Good`：每个 Ω 形状上都有 `Schema`）。
- `FCross` 那一格（树走链而参照余尾是 Ω）正是 `Mis` 的 `drop-lt`/`drop-eq`，在我的系统里是前提 `NodeMis` 的一部分，没有被证明。
- 量化域：我在收到转述前已把对一切树的量化换成域参数 `Domˢ`（随状态）；槽位与读法仍对一切 `GR.Nu` 量化，没有收窄。
- 出口条件与 `mc`：`lowAll` 在目标第 0 层的推导里，`mc` 只来自向下封闭一条（原推导里的 `mc` 结点照搬）；链步里的 `closeᴿ (Ω≤ψ …)` 在槽位层的推导里，不进第 0 层的推导树（判断，未编译）。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `Inv₀`, `Inv₁` 下 `LowSlot` 不成立 | `YiSOEnd.¬lowslot₀`, `¬lowslot₁` | 编译定理 |
| 任何使 `LowSlot` 成立的 `Inv` 都推出 `SlotBd` | `YiSOEnd.Needed.slot-needed` | 编译定理 |
| 域取全体时 `RebRow` 不成立（材料 y 高于孩子层号的 Ω 树时只进第 0 层尾项；例：塔第 1 项，目标孩子 1，嵌入孩子 ω，y 取 Ω_ω 树的二倍）；于是字面的 `Wire.LowSlot`（对一切 y）对任何带根的 `Inv` 都不成立 | 无 | 判断 |
| `Mis` 的 `kept-gt`（树保留、参照坍缩）在目标读法偏低（如任何层号都有的空读法）时出现；`R` 的第一位置序太薄，一般推不出 | `NodeMis`, `UpMis` | 判断 |
| `RootBd` 从 n = 2 起要对一切 `GR.Nu` 读法的 Leaf，而槽位层号含 Ω 形状；全域 Leaf 在 Ω 形状上已有编译否定（`YiLLLeafNeg.noLeafOk`），这类退化层号是否作为塔第 2 项的孩子层号出现没有编译 | `RootBd` | 判断 |
| 根推导 `dom-top (dom-keel n)` 是规范的，但归纳对一切 `R` 推导陈述，所以前提对一切读法量化；要收窄须对推导加谓词（类似 `Exᴴ`）并直接对 `Mᴴ` 递归 | 设计 | 判断 |

**翻译账。** 新定义（`Stˢ`, `Good`, `SlotBd`, `Keepᵗ`, `Domˢ`, `Mis`）都是验收侧的关系与谓词，不进树、折叠、合法性。来自记号的：参照取 ψ_κ(K ++ t)、`cmpᵀ (ν+1) κ` 的二分、γ 链。由树逼出的：`Good`（无 `Schema` 时折叠落到 `⊞`）、`dem`（ℕ 极限形状上材料搬进目标孩子）、目标与底值全量化（嵌入一步后孩子的 `SlotBd` 就是 x 在各槽位目标上的像）。只用 `R` 验收，没有值的定理，属于加深翻译一侧的标志；带来的信息是把障碍分成"读法与保留判定不一致"与"换基行"两类。

**是否对一切层号一步给出。** 回退行、链步、一致的结点两格、上折除一格外：是，`lowAll` 与 `upAll` 各一次归纳，不按站。三条前提：不是，未证。

#### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`，冷编（删自己的接口后，`-M6G`）日志里只有自己模块的 `Checking` 行。禁用构造与本机路径检索为 0。四个文件都读记号，未跑 `importclosure.py`。

| 文件 | 代码行 | 冷编退出码 |
|---|---|---|
| `YiSOLow.lagda.md` | 230 | 0 |
| `YiSOUp.lagda.md` | 73 | 0 |
| `YiSOEnd.lagda.md` | 110 | 0 |
| `YiSOTw1.lagda.md` | 38 | 0 |

日志在 `<实验目录>/work/YiSO/`（`*.cold.log`）。

#### 3. 定理表（全部是编译定理）

**YiSOLow**
- 陈述用的定义：
  - `Keepᵗ {a} (o , r , B) K t x = ∀ j (w : j ≤ a) (β : Tr⁺ j) κ → GR.Rd j κ → GR.R j (E.ψ κ K ∷ []) (proj₁ β) → GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ (BS.ψ a o r B j w β x))`
  - `SlotBd {a} (o , r , B) K = (p : Pos a) → ∀ {κ} → GR.Nu a p κ → GR.R (at a p) (E.ψ κ K ∷ []) (proj₁ (B (at a p) (posW a p)))`
- `slot-step : ∀ {s h} (st : Stˢ (nd s h)) K → SlotBd st K → (c : Ch s) → ∀ {t x} → Keepᵗ st K t x → SlotBd (stepˢ st c x) (K ++ t)`。嵌入一步后孩子的不变式就是 x 在孩子各槽位目标上的像。
- `good-tw : ∀ n → Good (tw n) (rb-tw n)`。塔各项的换基证据处处在场。
- `Node.node : (Mis (kp a o p w) (E.cmpᵀ (E.sucT ν) κ) → Goal (kp a o p w)) → Goal (kp a o p w)`，其中 `Goal m = GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ (node⁺ m G S))`。结点上保留且参照穿透（`keptPen`）、走链且参照坍缩（`dropGt`，链点由槽位目标上的归纳假设给出）两格已证，只剩不一致的两格。
- `Sys.Main.lowAll : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K → ∀ {t x} → GR.R a t x → Dm (o , r , B) x → Keepᵗ (o , r , B) K t x`，模块前提 `(nm : NodeMis) (sr : SelfRow) (rr : RebRow)`。多目标系统的保持，对一切层号。
- `Sys.Main.core`：结论逐字是 `GR.R (at a p) (E.ψ κ (K ++ η) ∷ []) (proj₁ (BS.ψ a o r B (at a p) (posW a p) (B (at a p) (posW a p)) y))`，前提 `Good a r`, `SlotBd (o , r , B) K`, `GR.Nu a p κ`, `GR.R a η y`, `Dm (o , r , B) y`。即 `LowSlot` 的结论。

**YiSOUp**
- `UpAll.upAll : ∀ {ℓ} (j′ : L) (d : Dn ℓ j′) → ∀ {u y} → GR.R j′ u y → UpQ d u y`，其中 `UpQ {ℓ} {j′} d u y = ∀ (b : Tr⁺ ℓ) κ K′ → GR.Rd ℓ κ → GR.R ℓ (E.ψ κ K′ ∷ []) (proj₁ b) → GR.R ℓ (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (Up j′ d b y))`，前提 `UpMis`。上折的保持，只剩参照坍缩一格。
- `UpAll.self←up : (𝒟 : Domˢ) → Sys.SelfRow 𝒟`。自身行由 `UpMis` 给出。

**YiSOEnd**
- `¬lowslot₀ : W₀.LowSlot → ⊥`，`¬lowslot₁ : W₁.LowSlot → ⊥`。前提可满足：`Neg.inv₀ : Inv₀ s₁ K₁`，`Neg.inv₁ : Inv₁ s₁ K₁` 是闭项。
- `Needed.slot-needed : LowSlot → ∀ {a} (s : Stᶻ a) K → Inv s K → SlotBd (stˢ s) K`（对 `Wire` 的任何参数）。
- `End.ebo-endᴬ : (∀ n → H.Exᴴ (folded n)) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`，模块前提 `(𝒟 : Domˢ) (nm : NodeMis) (sr : SelfRow) (rr : RebRow) (rb : RootBd) (ri : RootIn)`；`folded n : GR.R zero (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ n)) ∷ []) (twcᴮ n)`。带域的终点。
- `Full.lowslot₂ : W₂.LowSlot`，`Full.ebo-end₂ : W₂.ExitCondition (W₂.chain←slot lowslot₂) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`，模块前提是域取全体的三条加 `RootBd`。
- `Full.lowslot-tw1 : ∀ {κ} → GR.Nu (tw 1) p11 κ → ∀ {η y} → GR.R (tw 1) η y → GR.R (at (tw 1) p11) (E.ψ κ ([] ++ η) ∷ []) (slotFold (rootᴮ 1) p11 y)`，`p11 = inj₂ (suc zero , inj₁ tt)`，`at-p11 : at (tw 1) p11 ≡ nd sS (λ _ → zero)`；`Full.step-tw1` 是 `inv-step` 在这一格的实例。
- `root-bd0 : SlotBd (rootˢ 0) []`。

**YiSOTw1**
- `root-bd1 : SlotBd (rootˢ 1) []`，无前提。塔第 1 项根状态每个槽位、每个 `GR.Nu` 读法上底支配 Ω_κ；用 `YiLLCheck.leafC` 与 `YiVRRel.NoΩ≤`。
- `EndU.ebo-endᵁ : (nm : NodeMis) (rr : RebRow) (rb : RootBd) (ri : RootIn) → (∀ n → H.Exᴴ (folded nm (self←up 𝒟) rr rb ri n)) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`，模块前提 `(𝒟 : Domˢ) (um : UpMis)`。

#### 4. 第一个障碍

三条前提，逐字陈述在 `YiSOLow.Sys.NodeMis`、`Sys.RebRow`、`YiSOUp.UpMis`。都是数学上挡住，不是工程上（四个文件都在 6G 内一次通过，没有撞堆）。

1. **`RebRow`**（换基行）：`route` 落在地板之上时，要 `GR.R j (E.ψ κ (K′ ++ u) ∷ []) (proj₁ (seen S j … fl β′ c ⊞ BS.ψ (h c) … zero (z≤ (h c)) (Ωt zero) y))`，已知 `GR.R j (E.ψ κ K′ ∷ []) (proj₁ β′)` 与 `GR.R (h c) u y`，以及 `Dm … (up x c y e)`。域取全体时判断为假；要一个域使 y 不高于孩子层号的 Ω 树，同时满足 `Domˢ` 的封闭条件（`dnd` 对一切分支、`dch`、`dem`）并含塔各项的 Ω 树。这样的域是否存在没有检查：后继形状层号的 Ω 树以一切低层树为分支材料，所以域必须随状态。它对应既有的 `YiSDRead.CellRaise` 与对照表 "y 一般时只进尾项" 一格。
2. **`NodeMis` 的 `drop-lt`/`drop-eq`**（树走链、参照余尾保持 Ω）：即 F 路 `FCross` 的一格，也是 `YiXTIface.stuck` 的情形。
3. **`NodeMis` 的 `kept-gt` 与 `UpMis`**（树保留、参照坍缩）：只在槽位读法 ν 与目标读法 κ 不满足 ν+1 ≤ κ 时出现；因为 `GR.Rd` 对任何层号都允许空读法，对一切读法量化时一定出现。

次一级：`RootBd` 在 n ≥ 2（见问题表）。

#### 5. 偏离与事故

- **偏离简报**：没有按"证 `Wire.LowSlot` 字面陈述"做到底。读定义后判断它对一切 y 的量化在换基行上为假，改为带域的多目标系统，终点 `ebo-endᴬ` 不经 `Wire`（第 0 层目标只是系统里的一个目标）。`Wire` 上的实填保留为 `Full`，并标明其前提读作不可满足。
- **没有用 `YiBAEbo.gradedᴱ` 的 (ν, P) 形式**：直接在 `Keepᵗ` 里对 (κ, K) 量化，用 `YiWREnd.genᴮ` 归纳，因为目标要随槽位变，而 `FI.Sys` 固定一个目标。`YiXTIface`, `YiQDIface.SuffD`, `YiBLFold` 的律、`YiSDRead.Tw.*`, `YiBAWeak.nodeʳ` 都没有调用；复用的是 `YiQDFold.kp-good`/`mv-good`, `YiGTGen` 的各条, `YiANFam.cofG`/`fsnG`, `YiLLCheck.leafC`。
- **过程**：第一个文件的编译晚于简报要求的 30 分钟（先读了定义栈）。没有另写临时 `.agda`，直接在仓库里以自己前缀的新文件编译。一次语法错误（退出 42），改后各文件首次即过。
- **只凭转述引用的**：F 路三个文件；`YiBAEbo` 的 `¬below`/`main-¬below₀`、`YiSDRead.CellRaise`、`YiXTReb`、`YiUF*`、对照表第 9 节只读了文首或检索行，没有读证明。
- **前提可满足性**：`lowAll`, `upAll`, `ebo-endᴬ`, `ebo-endᵁ` 的前提没有给出实例；`Full` 的前提判断为不可满足。两条否定的前提有闭项实例。
- 没有改任何已有文件，没有提交。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：核心，证 LowSlot（前缀 YiSO，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。同批另两路（`YiWC`、审查 F 路）与你互不导入。这是候选折叠上的证明，不改任何定义。

#### 作者的决定与背景（2026-11-17）
- 作者对方法的要求（原文）："更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。对照表 `probes/Survey/CompareTable.md` 之后，换基候选（`YiBSFold`，主线定义不动）在读回域里的义务压成了一条核心陈述。
- 作者选项原文："Fable 先读定义：LowSlot 会不会重蹈覆辙 (Recommended), 核心：证 LowSlot (Recommended), 较弱链形状对 EBO 参照 (Recommended)"。前缀 `YiSO`（Fable 5.2）、`YiWC`（Opus 5.5），以及审查 F 路（Fable 5.2，只在临时目录），互不导入。
- **核心陈述**：`YiWREnd.Wire.LowSlot`（状态 s 在槽位 p 上朝槽位层的折叠 `YiWRZero.slotFold` 把关系 `GR.R a η y` 变成以 ψ_κ(K ++ η) 为参照的关系，κ 来自 `GR.Nu a p κ`，不变式 `Inv s K`）。条件定理 `Wire.ebo-endˢ : LowSlot → ExitCondition → toL EBO-tree′ ≼ readRW EBOᴮ`（换基折叠上 Λ 的闭项，对一切站一次成立）。YiWR 判断：在现有不变式 `Inv₀`、`Inv₁`（`ebo-end₀`、`ebo-end₁`）下 `LowSlot` 量化域太宽；要换成记下各层底对上下文支配的不变式，那时 `inv-step` 是朝各层的保持，要一个同时覆盖回退行（`inu`、`ink`、后继与 ℕ 极限上的 `inc`、路由落在地板之下的 `back`）与换基行（路由落在地板之上）的多目标系统，上下文随目标取 ψ_κ。终点那条递归里换基行不出现（`YiWRZero.fallᶻ′`），换基行只在结点链的链步与孩子的底里。出口条件与主线同状态（`YiHCRel.Exᴴ`）。
- **主审核对过的一点**：同形的条件定理主线早有（`YiGIEnd.Assembly`、`YiMXEnd`：Leaf、Lift、全域律 LowKeep 推出终点），此后的站与格都是在拆那条律；`LowSlot` 与它同类。
- **周边已编译（主审复核过，都在 `probes/OCF/Lean/`）**：
  - 参照一侧结点前提：`YiXTIface.XT.Below`、`AboveL`、`split`、`exact`、`stuck`；`YiBAEbo.BelowE`（参照取 ψ_ν、ν 高于目标真槽位层读法时 `Below` 成立，条件 `KeepAt`；`gradedᴱ` 的上下文是对子 (ν, P)，参照 ψ_ν(P ++ a)），`main-¬below₀`（对一切目标用 ψ₀ 在非零目标上不行），`¬above`（`AboveL` 要求逐项对齐，第 0 项对不上），`YiBAWeak.RefChainʳ`、`nodeʳ`（较弱链形状对结点一行够用）。
  - 嵌入行：`YiSDIface`（`SD.Split.need`/`give`、`AtΩ.lowΩ`：顶槽位保留时 Ω 树上的保持不经主系统的生成原理）、`YiSDRead`（`sub-read`、`top-read`、`Tw.sub-readᵗ`、`Tw.cap-domᵗ`、`Tw.hand₁ᵗ` 无前提；`Tw.lowΩᵗ` 条件；一般参照的抬高 `CellRaise` 未走通）。
  - 树一侧与读回域：`YiBLIface`/`YiBLFold`（换基律）、`YiQDIface`/`YiQDFold`（`SuffD`、`SuffRD`、`KD`、`kp-good`、`AddR.chain-dom`）、`YiXTReb`（换基在读回域里无分叉出口，`lowˣ`）、`YiFIGen.genᴷ`、`YiGLDom`（`Dom`、`leafᴰ`、`liftᴰ`；`rd-not-dom`）。
  - 合成候选 `YiUF*`（带深度 d 的一族，下标侧分叉格在地板之上已覆盖）。

#### 要做的（按序）
0. **陈述与最小检查**：写出加强后的不变式 `Inv`（记下各层的底对上下文的支配，上下文随目标取 ψ_κ，参照一侧用 `YiBAEbo.gradedᴱ` 的 (ν, P) 形式或说明为什么不用），以及多目标系统的状态与目标类型；在塔第 1 项（目标 `h₁ 1` 一类）上写出 `LowSlot` 与 `inv-step` 的实例，在临时文件里编译类型。不成立就停下回报。
1. **塔第 1 项**：证这一项上的 `LowSlot`（与 `inv-step`）。复用：读回形式 `YiSDRead.Tw.*`、`YiSDIface.AtΩ.lowΩ`、`YiBAEbo.BelowE`、`YiBAWeak.nodeʳ`、`YiQDIface.SuffD`/`SuffRD`、`YiXTIface.split`、`YiBLFold` 的律（先 `grep`，不重证）。
2. **一般**：对一切层号（不按站）证 `LowSlot`，或给出第一个挡住的引理（精确陈述）；若发现在读回域里有反例，写成编译否定。
3. 若成立：把 `Wire.ebo-endˢ` 的 `LowSlot` 前提实填，报出还剩什么（出口条件）。
4. 翻译账；说明这条证明是否对一切层号一步给出（阶段无关的判据）。

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

