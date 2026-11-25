# 统一收量化域的检验（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 07:15 至 07:39 |
| 工具调用 / agda 编译 (粗数) | 36 / 5 |
| token (usage 字段，按消息去重) | 输出 125826；新写入缓存的输入 460447；读缓存的输入 4876401；其余输入 56 |
| 写过的仓库文件 | `YiQVDom.lagda.md`, `YiQVTw1.lagda.md`, `YiQVUni.lagda.md` |
| 文件前缀 | `YiQV` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 3 件全部退出 0，禁用构造 0（均为验收文件）；检验结果既不是是也不是否：树的域收不窄（full-succ、full₂、dom-full₂、reb-forced，编译）；读法改成一致量化后两条义务归到读法条件 Raise（lowAllᵘ、upAllᵘ 条件），塔第 1 项上 Raise 无前提（raise-tw1）；剩下的 NodeDrop 有最小域里的形状实例（drop-shape），执行方判断不是掉值，要把推导读法的限制做进参照关系 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b81/YiQV.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiQV 回报：统一收量化域的检验（Fable 5.2，2026-11-17）

#### 1. 判决

**对纲领与目标意味着什么。** 简报的问题（定一套统一读回域，在域里一次核完剩下的义务）答案是：**照 `YiSOLow.Domˢ` 这种 "随状态的树域" 收不窄**（编译），所以五条义务没有在一个域里全部判定。

- 做成的有三件：
  1. 树域被迫取全体（编译）。
  2. 两条 "树保留而参照坍缩" 的义务（`NodeMis` 的 `kept-gt`、整条 `UpMis`）换成读法一致量化后不再是前提，归到一条只关于层号读法的条件 `Raise`（编译，条件定理）。
  3. 塔第 1 项上 `Raise` 无前提成立（编译）。
- 没有任何值的否定，换基候选在域内哪一格掉值仍未判定。
- 三个文件全是验收文件（读记号），不改树、折叠、合法性；终点 ψ₀(Λ) 仍是条件定理。
- 对 "让树自足"：`Raise` 是读法一侧（记号参照）的条件，不是树侧判据；本轮没有新的树侧语言。

**各步到哪一步。**

- **第 0 步（定域）：部分做完。**
  - 状态：可达谓词 `Reach`（根与嵌入一步生成），其上 `Good` 成立（`reach-good`）。
  - 树：最小域 `Mn` 是 `Domˢ` 的实例，含根上的 Ω 树（`min-root`），含于任何带 `RootIn` 的域（`min-least`），状态都可达（`mn-reach`）。
  - G7 的回答（编译）：
    - 前半成立：Ω 树的顶结点槽位只有下标侧顶槽位与后继形状孩子侧顶槽位（`Ωt-sΩ`、`Ωt-sS`）。
    - 后半不成立：后继形状上 Ω 树的分支是 `suc c` 的嵌入，c 取遍孩子层一切树，所以最小域在该孩子层状态上含一切树（`full-succ`）。
    - 塔第 2 项里有一个层号为 `tw 1`（Ω 形状、带 `Schema`）的可达状态 `st₂`，其上最小域是全体（`full₂`、`dom-full₂`）。
  - 读法：没有定出一个 "规范读数" 的域。`YiGLDom.Dom` 自身对任何层号都给空读法（`dz`），不是精确读数。
  - 上下文前缀（受链上确界约束的一类）：没有做。
- **第 1 步（逐条核）：见下表。** 塔第 1 项做了读法条件；塔第 2 项只有 `full₂`、`reb-forced`。
- **第 2 步：没有全部成立，没有接上无前提终点。** 给了一条前提不同的终点 `Endᵘ.ebo-endᵘ`。

**义务 × 结论表**

| 义务 | 结论 | 位置 | 档 |
|---|---|---|---|
| `NodeMis` 的 `kept-gt`（树保留，参照坍缩） | 改成读法一致量化后由 `Raise` 给出，不再是前提；原逐点陈述未判定 | `YiQVUni.Nodeᵘ.keptGt`、`Mainᵘ.lowAllᵘ` | 编译定理（条件：`SlotRaise`） |
| `UpMis` | 同上；上折只需目标层的 `LvRaise` | `YiQVUni.upAllᵘ` | 编译定理（条件：`LvRaise ℓ`） |
| `NodeMis` 的 `drop-lt`/`drop-eq`（树走链，参照余尾保持） | 未判定。最小域里有形状与读法前提都满足的结点 | `YiQVTw1.drop-shape`；前提 `Sysᵘ.NodeDrop` | 形状：编译；值：判断（见下） |
| `RebRow` | 未判定。任何可用域上它含 `st₂` 上对一切材料 x、y 的实例，域没有把 "材料不高于孩子层 Ω 树" 收进来 | `YiQVDom.reb-forced` | 编译定理（说的是域，不是值） |
| `RootBd`（n ≥ 2） | 读法取 `Dom` 时对一切 n 成立；对一切 `GR.Nu` 读法未判定 | `YiQVDom.root-bdᴰ` | 编译定理 / 未判定 |
| `StepW` | 未单独核；它由槽位目标上的保持推出（`YiWCWire.slot→step`），与上面几条同状态 | — | 未判定 |
| `Raise`（新出现的读法条件） | 塔第 1 项一切槽位层成立；对一切合法层号不成立；塔第 2 项起未判定 | `YiQVTw1.raise-tw1`、`YiQVUni.¬raise-flat` | 编译定理 / 判断 |

**判断（未编译）。**

- **`drop-shape` 的结论在值上成立，不是掉值。** 它的结点读法偏低（槽位层号 1 读作 0），同一棵树另有读法取 1 的推导，那时参照坍缩，与树一致。所以它说明的是 "推导里的结点读法可以偏低"。
- **读法一致量化与走链一格互相牵制。** 保留一格要往高取读法（一致量化）；走链一格要目标读法不超过结点读法（逐点量化）。`GR.Rd` 的读法是下界，没有最大读法（任意树 c 读回的层号没有规范项）。
- **域要做进验收关系本身。** `YiHCRel.Mᴴ` 的 `Low` 与 `Nu` 是参数，可以换成域内的；但 `dom-top`、`YiGTGen`、`genᴮ` 都对 `GR.R` 陈述，要重证，本轮没有做。依据是 `full-succ`：保留的结点在输出推导里对一切分支与一切推导量化，这是 `GR.R` 的 `mΩ` 规则决定的，`Domˢ` 管不到。
- **`RootRaise` 在 n ≥ 2 判断为假。** 塔第 2 项的孩子层含常值族的 Ω 形状层号（例如 `Ω 顶槽位 (λ _ → zero)` 的读回），其孩子侧槽位的读法取得到孩子的最大读法。编译这条否定要先有 `Rd (tw 1)` 的上界，没有做。
- **出口条件没有分析。** `keptGt` 在非零目标层用了一次向下封闭（`closeᴿ`），它经链点的读回（`raiseR`）可能流进第 0 层的推导，与 `Exᴴ` 的耦合未查。

#### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`。删自己的接口后 `-M6G` 冷编，日志各只有自己模块的一行 `Checking`；禁用构造与本机路径检索为 0。三个文件都读记号，未跑 `importclosure.py`。

| 文件 | 代码行 | 冷编退出码 | 峰值驻留 |
|---|---|---|---|
| `YiQVDom.lagda.md` | 87 | 0 | 1.4G |
| `YiQVUni.lagda.md` | 289 | 0 | 1.6G |
| `YiQVTw1.lagda.md` | 99 | 0 | 1.6G |

日志：`<实验目录>/work/YiQV/YiQVDom.cold.log`、`<实验目录>/work/YiQV/YiQVUni.cold.log`、`<实验目录>/work/YiQV/YiQVTw1.cold.log`。

#### 3. 定理表（全部是编译定理）

**YiQVDom**

- `reach-good : ∀ {a} {st : Stˢ a} → Reach st → Good a (proj₁ (proj₂ st))`。可达状态的换基证据处处在场。
- `minˢ : Domˢ`；`min-root : End.RootIn minˢ`；`min-least : (𝒟 : Domˢ) → End.RootIn 𝒟 → ∀ {a} {st : Stˢ a} {x : Tr a} → Mn st x → Domˢ.Dm 𝒟 st x`；`mn-reach : Mn st x → Reach st`。最小域非空、封闭、最小。
- `Ωt-sΩ : ∀ k h → proj₁ (Ωt (nd (sΩ k) h)) ≡ Ω (inj₁ (inj₁ tt)) (λ c → up zero c (proj₁ (Ωt (h c))) (proj₂ (Ωt (h c))))`；`Ωt-sS : ∀ h → proj₁ (Ωt (nd sS h)) ≡ Ω (inj₂ (tt , inj₁ tt)) (λ c → up zero tt (suc c) (z◃ c ◃s))`。Ω 树的顶结点槽位与分支。
- `full-succ : ∀ {h} {st : Stˢ (nd sS h)} → Mn st (proj₁ (Ωt (nd sS h))) → (c′ : Tr (h tt)) → Mn (stepˢ st tt zero) c′`。后继形状上 Ω 树进域，则孩子层一切树进域。
- `full₁ : ∀ x (c′ : Tr (zero ⊕ ↑ zero x)) → Mn (st₁ x) c′`，`st₁ x = stepˢ (stepˢ (rootˢ 1) (suc x) zero) tt zero`。
- `full₂ : (c′ : Tr (tw 1)) → Mn st₂ c′`，`st₂ = stepˢ (stepˢ (rootˢ 2) (suc zero) zero) tt zero`；`dom-full₂ : (𝒟 : Domˢ) → End.RootIn 𝒟 → (c′ : Tr (tw 1)) → Domˢ.Dm 𝒟 st₂ c′`。塔第 2 项里层号 `tw 1` 的一个可达状态上，任何可用域是全体。
- `reb-forced : (𝒟 : Domˢ) → End.RootIn 𝒟 → Sys.RebRow 𝒟 → RebAll (proj₁ st₂) S₁ (proj₂ (proj₁ (proj₂ st₂))) (proj₂ (proj₂ st₂))`。`RebAll` 是 `RebRow` 在一个状态上去掉域前提的陈述。任何可用域上的 `RebRow` 含它在 `st₂` 上对一切材料的实例。
- `root-bdᴰ : ∀ n (p : Pos (tw n)) {κ} → Dom (at (tw n) p) κ → GR.R (at (tw n) p) (E.ψ κ [] ∷ []) (proj₁ (baseᴮ n (at (tw n) p) (posW (tw n) p)))`。读法在读回域里时，根状态的槽位条件对一切 n 成立。

**YiQVUni**

- 陈述用的定义：
  - `Bdᵘ j K β = ∀ κ → GR.Rd j κ → GR.R j (E.ψ κ K ∷ []) (proj₁ β)`
  - `Raise j q = ∀ {ν} → GR.Nu j q ν → Σ E.T λ κ′ → GR.Rd j κ′ × Pen (E.cmpᵀ (E.sucT ν) κ′)`
  - `LvRaise j = (q : Pos j) → Raise j q`；`SlotRaise a = (p : Pos a) → LvRaise (at a p)`
  - `Keepᵘ {a} (o , r , B) K t x = ∀ j (w : j ≤ a) (β : Tr⁺ j) → LvRaise j → Bdᵘ j K β → Bdᵘ j (K ++ t) (BS.ψ a o r B j w β x)`
- `lower : ∀ {ν κ κ′} X → E.cmpᵀ (E.sucT ν) κ ≡ E.gt → Pen (E.cmpᵀ (E.sucT ν) κ′) → (E.ψ κ X ∷ []) ≤ᵀ (E.ψ κ′ X ∷ [])`。
- `rd0 : ∀ {κ} → GR.Rd zero κ → κ ≡ []`。第 0 层只有空读法。
- `upAllᵘ : ∀ {ℓ} → LvRaise ℓ → (j′ : L) (d : Dn ℓ j′) → ∀ {u y} → GR.R j′ u y → UpQᵘ d u y`，其中 `UpQᵘ {ℓ} {j′} d u y = ∀ (b : Tr⁺ ℓ) K′ → Bdᵘ ℓ K′ b → Bdᵘ ℓ (K′ ++ u) (Up j′ d b y)`。上折的保持，前提只有目标层的 `LvRaise`。
- `Sysᵘ.Mainᵘ.lowAllᵘ : (a : L) (o : Ok a) (r : Rb a) (B : Base a) → Good a r → SlotRaise a → ∀ K → SlotBd (o , r , B) K → ∀ {t x} → GR.R a t x → Dm (o , r , B) x → Keepᵘ (o , r , B) K t x`，模块前提 `(nd′ : NodeDrop) (rr : RebRowᵘ)`。`NodeDrop` 的结论逐字是 `GR.R j (E.ψ κ (K ++ t) ∷ []) (proj₁ (BS.ψ a o r B j w β (Ω p g)))`，前提含 `Pen (E.cmpᵀ (E.sucT ν) κ)` 与 `kp a o p w ≡ nothing`。
- `Endᵘ.ebo-endᵘ : (∀ n → H.Exᴴ (foldedᵘ n)) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`，模块前提 `(𝒟 : Domˢ) (nd′ : NodeDrop) (rr : RebRowᵘ) (rb : RootBd) (ri : RootIn) (rz : RootRaise)`，`RootRaise = ∀ n → SlotRaise (tw n)`；`foldedᵘ n : GR.R zero (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ n)) ∷ []) (twcᴮ n)`。
- `¬raise-flat : LvRaise flat → ⊥`，`flat = nd sL (λ _ → zero)`，`ok-flat : Ok flat`。`Raise` 对一切合法层号不成立；反例不是任何树的读回，读作谓词太宽。

**YiQVTw1**

- `strict : (y : Tr zero) {x : Tr zero} → zero ⊢ x ◃ y → ∀ {ν} → GR.Rd (L⁰ x) ν → Up1 (L⁰ y) ν`，`L⁰ x = zero ⊕ ↑ zero x`，`Up1 j ν = Σ E.T λ κ′ → GR.Rd j κ′ × Pen (E.cmpᵀ (E.sucT ν) κ′)`。
- `raise-L⁰ : (x : Tr zero) → LvRaise (L⁰ x)`；`raise-tw1 : SlotRaise (tw 1)`。塔第 1 项每个槽位层上 `Raise` 无前提。
- `Tw1.folded₁ : GR.R zero (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ 1)) ∷ []) (twcᴮ 1)`，模块前提 `(𝒟 : Domˢ) (nd′ : Sysᵘ.NodeDrop 𝒟) (rr : Sysᵘ.RebRowᵘ 𝒟) (ri : Domˢ.Dm 𝒟 (rootˢ 1) (proj₁ (Ωt (tw 1))))`。塔第 1 项只剩 `NodeDrop`、`RebRowᵘ`（`RootBd` 用 `YiSOTw1.root-bd1`）。
- `drop-shape : DropShape`（形状档）。字段：
  - `in-dom : Mn (stepˢ (rootˢ 1) (suc (suc zero)) zero) (proj₁ (Ωt a₂))`
  - `cofΩ : E.cof (E.Ωs []) ≡ E.cΩ []`
  - `slotNu : GR.Nu a₂ p₂ []`
  - `hyp`（结点的分支前提）
  - `dropped : kp a₂ … p₂ (inc tt self) ≡ nothing`
  - `tgtRd : GR.Rd b₁ (E.natT 1)`
  - `pen : Pen (E.cmpᵀ (E.sucT []) (E.natT 1))`

**前提可满足性。**

- `upAllᵘ` 的 `LvRaise` 有实例（`raise-L⁰`）。
- `lowAllᵘ`、`ebo-endᵘ`、`folded₁` 的 `NodeDrop`、`RebRowᵘ` 没有实例。
- `RootRaise` 在 n = 0、1 有实例，n ≥ 2 判断为假。
- `reb-forced` 的前提 `Sys.RebRow 𝒟` 没有实例。

#### 4. 第一个障碍

**`NodeDrop`（即 `NodeMis` 的 `drop-lt`/`drop-eq`），数学上挡住，不是工程上。** 三个文件都一次通过，峰值不到 2G。

- 结点在目标上走链（`kp … ≡ nothing`），而结点推导里的槽位读法 ν 低于目标读法 κ（ν+1 ≤ κ）。
- 这时参照 ψ_κ(K ++ t) 的余尾是 Ω_{ν+1}，树是 ℕ 极限。`GR.R` 的规则里只剩放宽与向下封闭可用，而归纳假设只对给定的 t 成立，换不到读法更高的推导。
- `drop-shape` 表明这种读法偏低的结点在最小域里就有。
- 要去掉它，得让推导里的结点读法对目标读法 "够高"，这是对推导（不是对树）的限制，`Domˢ` 表达不了。

次一级：

- `RebRowᵘ`：`reb-forced` 说明域没有帮上忙；它还要 `seen` 里 `YiRBSib` 折叠的保持，没有做。
- `RootRaise`（n ≥ 2）。

#### 5. 偏离与事故

- **没有写第 0 步的临时 `.agda`。** 直接以自己前缀的新文件在仓库里编译；第一个文件的编译晚于简报要求的 30 分钟（先读了定义栈与两份留档）。
- **没有按 "把 `YiSOLow`/`YiSOUp` 的域参数实例化" 核 `NodeMis`、`UpMis`。** 原因是 `dom-full₂`：实例化后在 `st₂` 上与全体无异。改为另写读法一致量化的系统（`YiQVUni`），骨架逐行照 `YiSOLow.Sys.Main` 与 `YiSOUp.UpAll`，文首已注明来源。它的 `Keepᵘ` 比 `Keepᵗ` 弱（逐点推出一致，反过来不行），终点类型与 `YiSOEnd.End.folded` 相同。
- **没做的：** 上下文前缀的域；`StepW` 的单独检验；塔第 2 项上的 `Raise`、`NodeDrop`、`RebRow`；任何值的否定（`GR.R` 在非零层没有值的可靠性引理，简报背景里已知）。
- **事故：** 一次冷编用 `/usr/bin/time -l` 包装，沙箱里 `sysctl` 被拒，包装返回 1（agda 本身通过）；去掉包装重跑，三件退出 0。
- **没有读、只凭转述或检索行引用的：**
  - Bedrock 性能手册没有打开（没有遇到性能问题；`EBOHandbook` 只读了 4.2 与 4.6 的印证表前半）。
  - `YiQDFold` 的 `KD`、`Ωt-in`/`Ωt-out`，以及 `YiUFDom`、`YiBCCover`、`YiSDRead`、`YiBAEbo`、`YiXTIface` 都没有读，也没有用。
  - `YiWCWire` 只读了文首与 `StepW` 一段；`YiRBSib` 的折叠没有读。
  - 审查 F 路的三个附件没有读，只读了留档正文。
  - `YiNLRaise.raiseR` 的定义体没有读；"链点推导里的向下封闭经读回流进第 0 层" 是凭 `dom-top` 的 `dC` 一行与 F 路 G5 的转述作的判断。
- 没有改任何已有文件，没有提交。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：统一收量化域的检验（前缀 YiQV，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。同批另三路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者要求（原文）："更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。作者选项原文："统一收量化域的检验 (Recommended), 合并同类接口 (Recommended), 出口条件与核心证明的耦合, 辅助系统的底取目标层起点（改候选定义）"。前缀 `YiQV`（Fable 5.2）、`YiMI`（Opus 5.5）、`YiXC`（Opus 5.5）、`YiAB`（Fable 5.2），互不导入。**主线定义不动**；换基折叠 `YiBSFold` 是候选。
- **现状（主审复核过，都在 `probes/OCF/Lean/`）**：换基候选上的终点条件定理有两版：`YiWREnd.Wire.ebo-endˢ`（前提 `LowSlot` 与出口条件；两个具体不变式下 `LowSlot` 被审查 F 路编译否定，加强不变式后接线合上，见留档 `probes/Survey/Reports-2026-11-16/AuditF.md` 与附件 `attachments/AuditF-*.txt`），以及不经原接线、带域的 `YiSOEnd.End.ebo-endᴬ`、`YiSOTw1.EndU.ebo-endᵁ`（前提：域 `Domˢ`、`NodeMis`、`RebRow`、`RootBd`、`RootIn`、`UpMis`，加出口条件）。`YiSOLow.Sys.Main.lowAll`、`YiSOUp.UpAll.upAll`：多目标系统里保留判定与参照一致的格对一切层号一次归纳证出。
- **剩下的义务（判断：都出自量化域太宽，第四、五次同形出现）**：`YiSOLow.Sys.NodeMis`（树走链而参照保持 Ω 余尾：审查 F 路 FCross 那一格、`YiXTIface.stuck` 的情形；树保留而参照坍缩：读法允许取空时出现）、`YiSOUp.UpMis`（上折同类一格）、`YiSOLow.Sys.RebRow`（换基行：路由落在地板之上时替身加第 0 层尾项，域取全体时判断为假；`YiSDRead.CellRaise` 未走通）、`YiSOEnd.RootBd`（塔第 2 项起根状态每个槽位每个读法上的 Leaf；全域 Leaf 在 Ω 形状上有否定 `YiLLLeafNeg.noLeafOk`）、`YiWCWire` 的 `StepW`（链的步：上下文前缀可以超出链的上确界）。出口条件 `YiHCRel.Exᴴ` 要求推导里每个向下封闭步 `mc` 两边是标准形、较大一边可数，与核心证明里 `mc` 的用法耦合（审查 F 路 G5）。
- 可用的读回域工具：`YiGLDom`（`Dom`、`dom-top`、`leafᴰ`、`liftᴰ`、`dom-keel`；`rd-not-dom`）、`YiQDFold`（树的域 `KD`、`kd-dw`、`Ωt-in`/`Ωt-out`）、`YiUFDom.QDTw.Ωt-tw`、`YiBCCover`（证据在读回域上处处满）、`YiSDRead.sub-read`/`top-read`（读回形式）、`YiBAEbo.BelowE`（参照取 ψ_ν、条件 `KeepAt`）、`YiSOTw1.root-bd1`（塔第 1 项根状态无前提）。

#### 本路的问题（答案为是或否的检验）
定一套统一的读回域，然后在这个域里一次核上面那几条剩下的义务：成立就证，不成立就写成**域内的**编译否定（反例落在域里才算对路线的否定）。

#### 要做的（按序）
0. **定域**（在临时文件里编译类型）：
   - 读法：槽位与目标取规范读数（例如落在 `YiGLDom.Dom` 里的读法），不对一切 `GR.Nu`/`GR.Rd` 读法量化。
   - 状态：可达状态（由 `rootˢ n` 与嵌入一步 `stepˢ` 生成的最小谓词），记下证据 `r` 是 `rb-tw` 的后代、底的来历。
   - 树：Ω 树一族或 `KD` 一类；先回答审查 F 路的 G7：可达状态上被折叠的树是否都在 Ω 树一族里、结点槽位是否只有下标侧的与后继形状孩子侧的（编译）。
   - 上下文前缀：受链上确界约束的那一类。
   说明这个域在终点实际用到的推导（`lowᶻ` 作用于 `rootᴮ n` 与 `dom-top (dom-keel n)`）上非空、对证明里递归到的子情形封闭。
1. **逐条核**：在这个域里，`NodeMis` 的两类格、`UpMis`、`RebRow`、`RootBd`（n ≥ 2）、`StepW` 各自：证明，或给出域内的编译否定。先塔第 1、2 项，再一般。复用 `YiSOLow`、`YiSOUp`、`YiSOEnd`（把它们的域参数实例化为你的域；不改它们）。
2. **交结论**：一张表：义务 × 在域里成立 / 域内否定 / 未判定。若全部成立，接上 `YiSOEnd.End.ebo-endᴬ`（或 `EndU.ebo-endᵁ`），报出终点下界还剩什么（出口条件）。若有域内否定，写清它否定的是什么（换基候选在这个域里的哪一格掉值）。

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

