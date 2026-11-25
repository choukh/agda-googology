# C1：经典值工具与 LPO 型前提的清退（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 12:27 至 12:45 |
| 工具调用 / agda 编译 (粗数) | 93 / 4 |
| token (usage 字段，按消息去重) | 输出 102331；新写入缓存的输入 316900；读缓存的输入 17397014；其余输入 160 |
| 写过的仓库文件 | `YiCIClear.lagda.md`, `YiCIOrder.lagda.md` |
| 文件前缀 | `YiCI` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 两个新模块 YiCIOrder、YiCIClear 主审删接口 8G 冷编都退出 0；YiCIOrder：严格序、ℕ 族与 Ω 族的最小上界、跨层良基（无前提），二分、全序、三歧、外延、上确界刻画、最小元（条件：排中律）；YiCIClear：Tri、VMᴸ、EmbV、Crux 等一族与 LPO、WLPO、MP 在排中律下成立；盘点后新增的值只有旧块 T₃ᵐ 不低于 BTBO（条件：排中律）；现主线与换基候选的开前提（LowKeep、LowSlot 等）都不是 LPO 型，排中律清不掉，'有多高' 仍停在判断 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b89/C1.md`。先用 Read 工具完整读它，再逐条照做（含 "规则" 与 "回报" 各节）。只新建简报允许的文件（前缀 YiCI），不改仓库里已有的文件。全程用中文。最后一条消息就是你的全文回报。

## 回报原文

#### C1 回报：经典值工具与 LPO 型前提的清退

##### 0. 一句话结论
两个新模块都编译过，退出码 0。第一个给出主线块值 `V` 上的一组经典工具，含全序、上确界的刻画、跨层良基、最小元。第二个把值序二分一类的前提全部清退，结论标"条件（排中律）"。
- 经典工具：全序、二分、三歧、外延、上确界的分裂与刻画、最小元，条件（排中律）；严格序、良基、最小上界是无前提定理。
- 清退：`Tri`、`Cplˣ`、`Cplᵖ`、`VMᴸ`、`Crux`、`EmbV` 等一族前提，以及 LPO、WLPO、MP 都在排中律下成立。
- 盘点：LPO 型前提的条件定理几乎都在 11-11 的 BTBO 持平工作里。其中重写块的部分已被同日无前提的 `YiBtboLower` 取代，所以清退后真正新增的值下界只有一条：旧块 `T₃ᵐ` 不低于 BTBO，即 ψ₀(Ω_Ω)，条件（排中律）。
- 现主线 `EBOᶻ` 与换基候选 `EBOᴮ`：现有条件定理里没有 LPO 型前提，排中律一条也清不掉，"有多高"仍停在判断。

##### 1. 新文件与关键定理

**`probes/OCF/Lean/YiCIOrder.lagda.md`**（156 行代码）
对象是 `YiVWVal` 的 `V` 与跨层 `≼`；严格序记作 `a ≺ b`，定义为 `suc a ≼ b`。

无前提的编译定理：
- 严格序的基本性质：`irr : ¬ (a ≺ a)`、`≺→⋠ : a ≺ b → ¬ (b ≼ a)`、`≺→≼`、`≼-≺`、`≺-≼`、`s≼s⁻`、`≺0`。
- ℕ 族与 Ω 族的最小上界：`lim-ub`、`lim-lub`、`lim-lub⁻`、`Ω-ub`、`Ω-lub`、`Ω-lub⁻`。
- 严格在极限之下就严格在某一项之下：`lim-below : a ≺ lim f → Σ n (a ≺ f n)`，`Ω-below` 同形。
- 跨层良基：载体 `VΣ = Σ L V`，`wf : (a : V ℓ) → Acc _⊏_ (ℓ , a)`，另有 `acc-≼`。

条件定理，在 `module Classical (lem : (A : Set) → A ⊎ ¬ A)` 里：
- 二分 `dich : a ≼ b ⊎ b ≺ a`，跨层。
- 全序 `tri : a ≼ b ⊎ b ≼ a`，即 P1 的 `P1Tri.tri`；这里由 `dich` 推出，证法是新写的。
- `⋠→≻ : ¬ (a ≼ b) → b ≺ a`，三歧 `trich : a ≺ b ⊎ a ≈ b ⊎ b ≺ a`。
- 外延 `ext≼ : (∀ c → c ≺ a → c ≺ b) → a ≼ b`。
- 上确界的分裂 `lim-split : lim f ≼ b ⊎ Σ n (b ≺ f n)`，`Ω-split` 同形。
- 上确界的刻画 `lim-sup`、`Ω-sup`：`b` 是各项的上界，且严格在 `b` 之下的值都严格在某一项之下，则 `lim f ≈ b`（Ω 族同形）。
- 最小元 `least : P x → Σ m (P m × ∀ y → P y → proj₂ m ≼ proj₂ y)`，对 `VΣ` 上任意非空谓词成立，证法是排中律加 `wf`。

**`probes/OCF/Lean/YiCIClear.lagda.md`**（109 行代码）
全是条件定理（排中律），在 `module Classical (lem : LEM)` 里：
- `tri : Tri` 直接取现成的 `YiChainNegLEM.lem→tri`，见第 3 节第 1 条发现。
- 由它得到：`cplˣ`、`cplᵖ`、`cplˣS`、`vm : VMᴸ`、`crux : Crux`、`embV : EmbV`、`embVˢ`、`vmˢ`、`vmᶜ : VMᶜ`、`monoᶻ : MonoTᶻ`、`chainP : YiLeanValFin.ChainP`。
- 左加封闭：`add1 : Add1ˣ`、`addω : AddωS`，用到新写的无前提引理 `≼+ˡ : z ≼ c + z`（第 0 层）。
- 不读推导的写法：`vm¬¬`、`vmⁱ`、`embV¬¬`、`embVⁱ`；无关参数一支用排中律加 `.⊥ → ⊥`。
- 全知原则：`lpo : OCF.Barrier.LPO`、`lpoᵁ : YiUniNegBase.LPO`、`wlpo`、`mp`、`mpⁱ`。
- 值：
  - `btbo-T₃ᵐ : D.BTBOᴵ ≼ IV.read T₃ᵐ`，经 `YiMonoVM.btbo-vm` 得到；
  - `src-btbo-T₃ᵐ : tr₀ Ord-Ord.BTBO ≼ IV.read T₃ᵐ`，即不低于 src 里已发表的 BTBO（经 `BTBOFull.BTBO≈`）；
  - `D.BTBOᴵ` 与 `NoCumsum.BTBOᴵ` 字面相同，依据是 `YiBtboLower` 里的一个 `refl`。

##### 2. 编译结果
从仓库根目录跑简报给的命令，带 `+RTS -M6G -RTS`，两次都只跑一个 agda：
- `OCF.Lean.YiCIOrder`：退出码 0。日志只有一行：`Checking OCF.Lean.YiCIOrder (<仓库>/probes/OCF/Lean/YiCIOrder.lagda.md).`
- `OCF.Lean.YiCIClear`：最终版退出码 0。日志只有一行：`Checking OCF.Lean.YiCIClear (<仓库>/probes/OCF/Lean/YiCIClear.lagda.md).`

其他情况：
- 依赖用的是已有的接口文件，不是冷编。
- 无公设、无洞、无编译指示；排中律只作模块参数。
- 止损都没有触发：`Ordᶜ` 第 0 层的空构造子 `limᵢ ()`、`up ()` 一次就过，堆没出问题。
- 只新建了这两个文件，没改仓库里已有的文件。

##### 3. 对第 4 层下一步的意义，与第 3 项盘点

**两条与转述不符的发现：**
1. P1 说"排中律推出 `Tri`"没有编译，这个说法过时了。`YiChainNegLEM` 在 11-11 已有 `lem→tri` 与 `lem→chainP`，A1 缺的只是几行组合。
2. 11-11 重写块的条件定理，同日已被无前提的 `YiBtboLower.btbo : D.BTBOᴵ ≼ read T₃` 与 `btbo⁺ : … ≼ NA.read NT.T⁺` 取代。所以对 `T₃` 与 `T⁺`，排中律清退不给新东西，我没有重复写进文件。被取代的是：`YiLeanValFin.btbo-vm`、`btbo-p`，`YiNextValFin.btbo⁺-from-main`、`btbo₃-from-main`，`YiLowChain.FromVMᶜ`，`YiChainCond.btbo-cond`，`YiNextAcc.FromBTBO`。

**盘点：前提含 LPO、WLPO、二分、可判定一类的已编译条件定理**

| 条目 | 排中律能否清退 | 清退后的结论 |
|---|---|---|
| `YiMonoVM.btbo-vm`（前提 VMᴸ）、`FromMonoᶻ`（前提 MonoTᶻ） | 能，已编译 | 旧块 `T₃ᵐ` ≥ BTBO = ψ₀(Ω_Ω)，条件（排中律）；此前无前提只到 ψ₀(Ω_{ω+1}) |
| `YiVmConChain.btbo-p`、`YiVmNegChain.ch→btbo` | 不必 | 与上一行结论相同 |
| `YiBtValBT.FromMono.btbo`（前提 `MonoT`，不带 ZsL） | 只清掉一半 | 排中律给 VMᴸ；另一半要"不带 ZsL 的树侧下界"，不是 LPO 型，未清 |
| 11-11 块的各条 BTBO 条件定理（见上面第 2 条发现） | 能 | 已有无前提版，不给新值 |
| `YiZeroAccP.c2′`（前提 `Tr`，有 `tri→tr`） | 能，未编译 | 候选块上第 1 项 `D.γ 1` 落入 `≼ᵖ`；值只到 ψ₀(Ω₁)，我判断价值低 |
| `tri→vm`、`cpl→vm`、`cpl→crux`、`cpl→embV`、`crux→vm`、`embV→vm`、`embˢ→vmˢ`、`vmᴸ→vmᶜ` | 能，已编译 | 见第 1 节 `YiCIClear` |
| `YiGenFoldGap`（派发完全，前提是判定"在位置上"） | 只在验收侧成立 | 结论是派发完全，不是值；判定写进派发就违反纲领第 2 条 |
| `YiCross.M.monoʰ`（前提 `Compat`、`KeepRow`） | 不能 | 见下一张表 |

**`Compat` 一族：**
- 结论为 LPO 的一类（`YiCompatDlLPO.lpo-tw`、`lpo-Λ`、`lpo-ΛΛ`，对一切派发 D）：排中律下 LPO 成立，这几条否定不再排除"验收侧用排中律定义的派发"。但这样的 `Compat` 实例没有构造。我判断这属于 C2 理想折叠那一路，而且只关于理想折叠，不关于实际折叠。
- 结论为矛盾的一类（`YiCompatDlNeg.no-tw`、`no-Λ`、`no-ΛΛ`，对主线派发 `dl`）：排中律清不掉。所以实际折叠上的 `monoʰ` 在塔与 Λ 上不可用。

**结论为 LPO/WLPO/MP/弱判定的否定，分两类：**
- 证明侧，排中律下空真，前提已在 `YiCIClear` 编出：`tri→LPO`、`cplˣ→LPO`、`cplᵖ→LPO`、`embV→LPO`、`embVˢ→LPO`、`add1→LPO`、`addω→LPO`、`cplˣS→LPO`、`vm¬¬→MP`、`vmⁱ→MPⁱ`、`embV¬¬→MP`、`embVⁱ→MPⁱ`。
- 保初始段嵌入：`YiVmNegSeg.embVᴰ→LPO` 的前提 `EmbVᴰ` 在排中律下是否成立，未判定。
- 定义侧，仍约束定义，因为纲领第 2 条不许定义用排中律：`obs→dec` 一族、`dec-at→lpo`、`top-branch→lpo`、`full→dec`、`full→wlpo`、`cmp-full→lpo`、`fullSem→lpo`、`col→wlpo`、`exact→wdec`、`chain→wlpo`、`bare-way→lpo` 等。排中律只让它们不再否定验收侧的理想对象，例如 P4 的 ψ★。

**结论为矛盾的否定（排中律清不掉）：** `no-tw` 一族、`neg₀ⁿ`、`no-UB`、`no-cross-level`、`no-L`、`no-bm-all`、`no-keep`、`¬LowSlot₀`、`¬LowSlot₁`、`no-rfl₂` 等。

**对下一步的意义：**
- 现主线 `EBOᶻ` 的无前提下界仍是 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)，这一批没有改变它。
- 主线与换基候选还开着的前提是 LowKeep、LowSlot、NodeMis、UpMis、RebRow、RootBd 与 `Out`（台账 V50），都不是 LPO 型，排中律碰不到。
- 下一个必经缺口不变（据 P1 转述）：K6 那一格，即 Ω 形状层号上、目标经指定孩子时 `kp` 走链，最早在 tw 1 上 b·ω^{Ω₂} 的回灌处；对换基候选就是 A4。剩余距离按 P1 的判断是 A2 到 A6，约 5000 到 10000 行。
- `YiCIOrder` 给 C2、C3 备好了工具：全序、上确界刻画、外延、最小元与良基。用它们可以把"理想值"Ψ* 与转移引理写成验收侧陈述，也可以写经典上界，例如"主线 T₂ < ψ₀(Ω_{Ω₂})"，结论标条件（排中律）。这一步我没有做。

##### 4. 没有读、只凭转述引用的东西
- **读了全文：** `YiVWVal`、`YiVmConExact`、`YiVmConLPO`、`YiMonoVM`、`YiLowNeg`、`YiCompatDlLPO`、`YiCrossIface`、`YiChainNegLEM`、`YiRWBlock`，以及 `ProbeP1.md` 与附件 `P1Tri`。
- **读了部分：**
  - `Value` §1–2；`Level` 中 `Ordᶜ`、`Ω`、`ψ` 的定义；
  - 只看签名：`YiLowBase`、`YiLowChain`、`YiLeanValFin`、`YiNextValFin`、`YiVmNegIrr`、`YiChainNegAdd`；
  - 文首加签名：`YiBtboLower`、`YiCompatDlNeg`（另有 `no-tw` 的陈述）、`YiBtValBT`（另有 `MonoT`）、`BTBOFull`；
  - 只读文首：`YiVmNegSeg`、`YiTBObs`、`YiMTObs`、`YiFuncCrux`、`YiFuncChain`、`YiPEKey`、`YiSucWire`、`YiZeroAccP`；
  - `YiSHAccept` 只看了 `btbo-low`。
- **只靠检索的行文：** `RESULTS.md` 与 `IdeaLedger.md`。第 3 节"定义侧"与"矛盾"两类里的定理，大多只看过名字与 RESULTS 的行文，没读陈述。
- **没读：** P2 到 P5b 与 MathAB 的留档，P4 附件 `P4Star`，`YiTBRow`、`YiMTTab`、`YiRWFold`、`YiBS*`、`YiWREnd`、`src/OCF/BTBO`，手册 §4（没遇到堆的问题）。
- **只凭转述：** K6、E6 的定位与 A2 到 A6 的行数，都来自 P1 回报；`D.BTBOᴵ` 读作 ψ₀(Ω_Ω)，依据是 `BTBOFull` 文首与 `YiBtboLower` 里的那个 `refl`。
- **元层判断，没有编译：** 排中律作模块参数与 `--safe --without-K`、与无关参数相容（集合论模型加全局选择），所以这些条件定理的前提可满足。
