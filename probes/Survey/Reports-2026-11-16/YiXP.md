# 工程：保持引理族移到精确标签（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 13:31 至 13:57 |
| 工具调用 / agda 编译 (粗数) | 77 / 13 |
| token (usage 字段，按消息去重) | 输出 138976；新写入缓存的输入 309693；读缓存的输入 11549778；其余输入 114 |
| 写过的仓库文件 | `YiXPExact.lagda.md`, `YiXPFold.lagda.md`, `YiXPFrame.lagda.md`, `YiXPNeg.lagda.md`, `YiXPRel.lagda.md`, `YiXPRows.lagda.md`, `YiXPSmall.lagda.md` |
| 文件前缀 | `YiXP` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 7 件全部退出 0，禁用构造 0；精确标签下的 LowKeep 在一切不含 Ω 形状的层号上成立（lowKeepAt-noΩ、lowKeepˣ），前提有实例；Ω 形状层号上的证据域被否定（no-index-tree-tw1ˣ，来自 kp 对 Ω 形状经 inc 恒走链），LowKeepAtˣ (tw 1) 未定 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b71/YiXP.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### 回报：YiXP（工程：把保持引理族移到精确标签上）

##### 1. 判决

**对纲领与目标意味着什么。** 所有改动都在第 4 层（验收层），新文件全部是读记号的验收文件。树、折叠、合法性一行没改，没有公理。本路对 "树自足" 的目标没有直接进展，但查清了两件事：
- YiGT 一族（原有的保持引理文件）的一般各行，证明里**不用槽位标签的任何性质**。槽位标签选哪种，只影响 "框架" 有没有居民。框架指折叠时每个 Ω 结点 "保留还是走链" 所需的标签比较。
- 改用精确标签 `Lbl` 后（不含 Ω 形状的层号各自对应唯一的记号序数），框架只靠三条性质就能证出：标签唯一（`uniq`）、槽位标签低于层号标签（`below`）、标签沿路径不降（`lbl-path`，本路新证）。

翻译账：没有新的树侧定义，只新增层号谓词 `NoΩ`，并把 `KeepSpec` 改写成一般形式 `KeepG`（内容不变）。

**各步到哪一步。**
- 第 0 步完成。临时文件约 20 分钟写出并编译：上折一行对抽象 `Lab` 写出，用 `Lbl` 实例化，并换回 `Rˣ`（精确标签下的验收关系）。
- 第 1 步完成：`LowKeepAtˣ` 对一切不含 Ω 形状的层号有居民。`YiGLExact.LowKeepˣ` 整个陈述也有居民，但 `Lbl` 的 Ω 一条是 ⊥，所以它只覆盖不含 Ω 形状的层号，对 `tw (suc n)` 和 Λ 什么也没说。
- 第 2 步完成。`child d` 对一切 d 都不含 Ω 形状，所以 `LowKeepAtˣ (child d)` 无条件成立。在 `Rˣ` 里得到 `YiQLRead.Need` 形状的结论，d 取有限数和 ω 两种。
- 第 3 步见第 4 节。另外加了一条编译否定：`tw 1` 上的路径证据域为空。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 一般各行（Gen/Up/Self/Emb/Node/Fold/Index/Direct/Slot）不用槽位标签的性质 | 参数化副本 `YiXPRel`/`YiXPRows`/`YiXPFold` 对抽象 `Lab` 编译通过 | 对副本是编译定理；对原文件是判断（依据逐行搬运加检索） |
| 原族中下界读法 `Rd` 的性质只出现在实例与否定文件里：`YiGTInst`、`YiGTOmega` 用 `rd-zero` 与 `GR.c0 refl`；`YiGTCheck.PresJ` 以 `GR.Rd j ν` 作前提；`YiGTSlot.OmegaStepAt` 写到 `GR.Rd k ν`；`YiGTIndexNeg`、`YiGLFrame.no-frame-S` 用的是 "`[]` 是每个槽位的标签" | 检索 | 判断 |
| 不含 Ω 形状的层号上 `LowKeepAtˣ` 成立 | `YiXPExact.lowKeepAt-noΩ` | 编译定理 |
| `LowKeepˣ` 有居民，只覆盖不含 Ω 形状的层号 | `YiXPExact.lowKeepˣ` | 编译定理 |
| `child d` 上 Need 形状的结论（在 `Rˣ` 里，带 `Prefixˣ`，η ≤ λ） | `YiXPSmall` | 编译定理 |
| 在 `tw 1` 上，取 `Lbl` 时 `IndexTree`（每层每个槽位的路径证据）为空 | `YiXPNeg.no-index-tree-tw1ˣ` | 编译否定（只否定这个证据域） |
| `LowKeepAtˣ (tw 1)` 是否成立 | 无 | 未定 |

前提可满足：`need₀-fin`、`need₀-ω` 用标准底 `B₀`、`prefixˣ-B₀`、`topˣ`、`lbl-fin` 把 `LowKeepAtˣ` 的全部前提实填，所以 `lowKeepˣ` 不是空真。

##### 2. 文件表（全在 `probes/OCF/Lean/`）

各文件删掉自己的 `.agdai` 后冷编，8G 上限，退出码都是 0，每份日志只有本模块的 `Checking` 行。每件约 18–19 秒，含加载，同机有并行。

| 文件 | 代码行（非空） | 冷编退出码 |
|---|---:|---:|
| `<仓库>/probes/OCF/Lean/YiXPRel.lagda.md` | 114 | 0 |
| `<仓库>/probes/OCF/Lean/YiXPRows.lagda.md` | 284 | 0 |
| `<仓库>/probes/OCF/Lean/YiXPFold.lagda.md` | 128 | 0 |
| `<仓库>/probes/OCF/Lean/YiXPFrame.lagda.md` | 108 | 0 |
| `<仓库>/probes/OCF/Lean/YiXPExact.lagda.md` | 55 | 0 |
| `<仓库>/probes/OCF/Lean/YiXPSmall.lagda.md` | 76 | 0 |
| `<仓库>/probes/OCF/Lean/YiXPNeg.lagda.md` | 28 | 0 |

自查结果：
- 检索禁用构造（postulate、TERMINATING、NO_POSITIVITY、trustMe、洞、`--cubical`、irrelevant-projections）与本机路径，结果为 0。
- 七个文件都是读记号的验收文件，按简报不需要跑 importclosure。
- 文首都不超过 5 行。
- 第 0 步临时文件：`<实验目录>/work/YiXP/XP0.agda`，退出码 0。

##### 3. 定理表

`YiXPRel`/`YiXPRows`/`YiXPFold` 是以 `(Lab : L → E.T → Set)` 为参数的顶层模块。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `up-pres` | `∀ j → UpAt j` | 任意标签下的上折保持，前提为 `UpFrame` | YiXPRows | 编译定理（条件在 UpAt 内） |
| `self-pres` | `∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) ν t → NodeFrame ℓ o ℓ self ν → (β : Tr⁺ ℓ) → R ℓ (E.ψ ν t ∷ []) (proj₁ β) → ∀ {a x} → R ℓ a x → R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B ℓ self β x))` | 折到自身的保持 | YiXPRows | 条件定理 |
| `emb-row` | 同 `YiGTEmb.emb-row`，`GR.R` 换成 `R` | 嵌入行 | YiXPRows | 条件定理 |
| `pres` / `direct` / `kit` | `∀ ℓ → Kit ℓ → PresAt ℓ` / `∀ ℓ → IndexTree ℓ → PresAt ℓ` / `∀ ℓ → IndexTree ℓ → Kit ℓ` | 统一保持的组装 | YiXPFold | 条件定理 |
| `lbl-path` | `∀ {j a} → j ≤ a → ∀ {ν κ} → Lbl j ν → Lbl a κ → ν ≤ᵀ κ` | 精确标签沿路径不降 | YiXPFrame | 编译定理 |
| `lbl-noΩ` | `∀ a {ν} → Lbl a ν → NoΩ a` | 有精确标签的层号不含 Ω 形状 | YiXPFrame | 编译定理 |
| `frame` | `∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) {ν κ} → Lbl j ν → Lbl (at ℓ p) κ → KeepSpec ℓ j ν p κ (kp ℓ o p w)` | 不含 Ω 形状时，任意路径、任意带标签的目标都有框架 | YiXPFrame | 编译定理 |
| `index-all` | `∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (r : Rb ℓ) → ∀ {j} (w : j ≤ ℓ) {ν} → Lbl j ν → IndexOK ℓ o r j w ν` | 路径证据处处成立 | YiXPFrame | 编译定理 |
| `index-tree` | `∀ ℓ → NoΩ ℓ → IndexTree ℓ` | 每层每个槽位的证据树 | YiXPFrame | 编译定理 |
| `pres-noΩ` | `∀ ℓ → NoΩ ℓ → PresAt ℓ` | 一般保持无条件成立（`pres ∘ kit`） | YiXPFrame | 编译定理 |
| `lowKeepAt-noΩ` | `∀ ℓ → NoΩ ℓ → LowKeepAtˣ ℓ` | `YiGLExact` 的 LowKeep 陈述在不含 Ω 形状的层号上成立 | YiXPExact | 编译定理 |
| `lowKeepˣ` | `LowKeepˣ` | 整个陈述有居民；`Lbl` 的 Ω 一条是 ⊥，所以只覆盖不含 Ω 形状的层号 | YiXPExact | 编译定理 |
| `upˣ`, `selfˣ` | 上折与自身两行写在 `Rˣ` 里（`selfˣ` 要 `NoΩ ℓ` 与 `Lbl ℓ ν`） | 三行中的两行移到 `Rˣ`；嵌入行只在 `pres-noΩ` 内部使用 | YiXPExact | 编译定理 |
| `low-child` | `∀ d → LowKeepAtˣ (S.child d)` | 对一切 d 无条件成立 | YiXPSmall | 编译定理 |
| `needˣ` | `∀ d {λ′} → Lbl (S.child d) λ′ → ∀ η → η ≤ᵀ λ′ → Needˣ η d` | Need 形状：结论在 `Rˣ K.one (Q.Target η)` 里，前提多一个 `Prefixˣ base []` | YiXPSmall | 编译定理 |
| `need-fin` / `need-ω` | `∀ n η → η ≤ᵀ E.natT (suc (suc (suc n))) → Needˣ η (nat n)` / `∀ η → η ≤ᵀ E.sucT ωᵀ → Needˣ η W.ω` | d 为有限数 n（λ = n+3）与 d = ω（λ = ω+1）的实例 | YiXPSmall | 编译定理 |
| `need₀-fin` / `need₀-ω` | 标准底 `B₀`、底值 `Ωt K.one`，结论 `Rˣ K.one (Q.Target (E.natT (n+3))) (…)` / `Q.Target (E.sucT ωᵀ)` | 无前提的实例 | YiXPSmall | 编译定理 |
| `Any.no-frame-Ωinc` | `∀ k h (o : Ok (nd (sΩ k) h)) (c : Tr k) {j} (v : j ≤ h c) {ν} (c′ : Tr k) (t : Pos⁼ (h c′)) {κ} → Lab (proj₁ (sl⁼ (h c′) t)) κ → E._<ᵀ_ κ ν → NodeFrame (nd (sΩ k) h) o j (inc c v) ν → ⊥` | 任意标签下：Ω 形状层号经 `inc` 折到目标时，某个孩子里只要有一个标签低于目标的槽位，框架就为空 | YiXPNeg | 编译否定 |
| `no-index-tree-tw1ˣ` | `IndexTree (tw 1) → ⊥`（`Lab = Lbl`） | 失败处只用到 `one`、`zero` 的精确标签 | YiXPNeg | 编译否定（只否定证据域） |

##### 4. 第一个障碍

第 0–2 步都没有被挡住。往 Ω 形状层号走，第一个障碍是 **`YiXPNeg.no-index-tree-tw1ˣ`**，这是一条编译否定，挡住的是这个证据域。原因在折叠的保留判定 `YiRWFold.kp`：对 "Ω 形状、槽位在孩子里、路径经 `inc`" 一行，它的定义是 `kp (nd (sΩ k) h) _ (inj₂ _) (inc _ _) = nothing`，恒取走链。框架于是要求槽位标签不低于目标标签；而 `IndexTree` 的槽位路径 `posW` 正好经过 `inc`，孩子里更深的槽位标签更低，两者冲突。

这一点与 Ω 形状层号的 `Lbl` 无关，所以即使 YiEL 补上 Ω 一条，`tw 1` 也进不了 `IndexTree` 这个证据域（编译定理）。它不否定 `LowKeepAtˣ (tw 1)`，这一项未定。

判断：要越过它，需要另一种证据来处理这些 "树走链而记号保留" 的结点；若 `LowKeepAtˣ (tw 1)` 本身不成立，就要动折叠的这一行。那属于第 4 层逼出的定义改动，须作者定。

要得到真正的 `YiQLRead.Need`，还有三处没处理（判断）：
- (a) 结论在 `Rˣ` 里，带向下封闭 `mc`；`YiCLFam.M 1` 没有 `mc`，换回去要消去 `mc`。
- (b) `Need` 对任意满足 OK 的底成立；`Needˣ` 多要 `Prefixˣ base []`。`minimal-from` 用的子底来自 Ω 形状的父层号，不在本域。
- (c) η 的范围要从 `M⁰ η d` 推出 η ≤ λ，这是第 0 层下界关系 `M⁰` 的问题，属 YiEL 一路，没有替做。

##### 5. 偏离与事故；未读的东西

- **超出简报**：新增 `YiXPNeg`（28 行），以及 `upˣ`、`selfˣ`。
- **没有搬的部分**：`YiGTIndex.index-lift`、`index-tw1-slot`；`YiGTDirect.LayerIndex`、`layer-at`；`YiGTSlot.layer-index`、`step-layer`、`OmegaStepAt`、`omega-step-at`；实例文件 `YiGTLow`、`YiGTInst`、`YiGTOmega`、`YiGTCheck`、`YiGTCompat`。它们是 `Rd` 的实例，或者只服务 Ω 形状下标槽位；在 `Lbl` 下的作用由 `YiXPFrame` 与 `YiXPSmall` 承担。嵌入行没有单独写成 `Rˣ` 形式。
- **事故**：第 0 步首次编译时，`to` 直接对 `Mᴴ` 推导递归，停机检查在 `mw`、`mc` 两行失败。改用现有的 `YiFMMap.mapᴴ` 后通过。曾用 `/usr/bin/time -l` 计时，被沙箱的 sysctl 拦下，改用 `date`。全程没有 251，没有超时。
- **没有读或只读了一部分的**：
  - 完全没读：`YiGLDom`、回报 `probes/Survey/Reports-2026-11-16/YiGL.md`、`YiAbsGIface`。
  - 只读了片段：`YiTBRow` 只读到第 80 行，没读它的 `ψ` 定义体，用的是 `YiRWFold` 的 `kp` 与搬来的证明；`YiTBFam` 只检索了 `ψ-⊵`；`YiBVDomain`、`YiSQOmega`、`YiCLFam`、`YiBVReadBound` 只读了用到的片段。
  - 简报里第七十批 YiSY、YiLX、YiVN 的结果没有用到。
- **性能手册**：读了 Bedrock 手册的 C-9、C-10、C-24、S-1、H-6、Q-1、Q-23，S-3 只看了标题；本路没有遇到性能问题，这些规则没有用上。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：工程，把保持引理族移到精确标签上（前缀 YiXP，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。作者 2026-11-16 定第七十一批，本路选项原文 "工程：保持引理族移到精确标签 (Recommended)"，执行方 Opus 5.5。同批另三路（数学 YiEL、摆脱侧 YiWB、同步对象上的 Tail YiTL）与你互不导入。

#### 第七十批的结果（主审 8G 冷编复核过，读陈述）
- **整体引理 YiGL**（`probes/OCF/Lean/YiGL*`）：读回域 `YiGLDom.Dom`（`dz`、`dC`、`dN`、`dc`）上 Leaf 对一切层号形状成立（`dom-top`），接口 `YiAbsGIface` 的 Leaf、Lift 无前提成立（`leafᴰ`、`liftᴰ`），全域 Leaf 的反例在域外（`not-in`）。LowKeep 未证：现有条件保持引理 `YiGTFold.pres : ∀ ℓ → Kit ℓ → PresAt ℓ` 要的框架 `NodeFrame`，在槽位标签取下界读法 `Rd` 时，对一切后继形状层号无居民（`YiGLFrame.no-frame-S`、`no-tree-child`）；换成精确标签 `YiGLFrame.Lbl`（`Lbl zero ν = ν ≡ []`；后继逐字；ℕ 极限要 `cof ν ≡ cω`、`NF ν`、`LimAt ν`、各孩子标签与基本列的比较；Ω 形状取 `⊥`）后有居民（`frameˣ-S`、`YiGLNode.frameᴸ-S`）；`uniq`、`below`、`lbl-rd`；精确标签的关系族 `YiGLExact.Rˣ`（第 0 层与 `GR.R` 相同），`topˣ`（含 ℕ 极限层号；`topˣ-ω` 在 `no-omega-seed` 的对象上成立），`LowKeepAtˣ`、`LowKeepˣ`（陈述，无居民），`prefixˣ-B₀`、`betaˣ`；`YiGLNode.node-rowˣ`（结点一行的条件定理）。回报 `probes/Survey/Reports-2026-11-16/YiGL.md`。
- **对位调整 YiSY**：`ebo-from-stations′ : (∀ n → Kᴱ′ (suc n)) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；第 3 站下界归约为 `YiSYSmall.k2′-from-tail : Gᴱ.Tail → Kᴱ′ 2`，`Tail` 未证；`two-shape`、`kl-index`。
- **摆脱侧 YiLX**：`YiLXClimb.climb`（字面路径上源 Ω 树折叠按 `YiVRRel.Le` 不高于目标的，一般形式，不读记号），前缀 0、1；前缀 2 起底前提被否定（`YiLXOne.no-base-two-at0` 等：源底里分支取值在第 0 层的 Ω 结点，`Le` 放不进极限链之下）。
- **配对否定 YiVN**：`YiVNIdx.Gen.no-value-index-mono≈`：以下标的树侧值序作前提的下标单调不成立（谓词太宽）。所以前提只能是字面路径、关系或读回域。
- **作者定**：主线停逐项，改攻整体引理；参照只用记号关系 M（`OCF.Align.Level` 的下标类型只有 `zero`、`suc`、`lim`，接不到终点）。

#### 本路的任务
`YiGT` 一族（`YiGTGen`、`YiGTUp`、`YiGTSelf`、`YiGTEmb`、`YiGTNode`、`YiGTFold`、`YiGTIndex`、`YiGTDirect`、`YiGTSlot`，另有 `YiGTLow`、`YiGTInst`、`YiGTOmega`、`YiGTCheck`、`YiGTCompat`，非空行合计约一千行）把关系写死为 `YiGIRel.R`（槽位余尾 = 下界读法 `Rd`）。YiGL 判断：把它对槽位标签参数化后重做到 `Rˣ` 上是工程，结点一行已移（`node-rowˣ`），嵌入、上折、自身三行未移。

#### 要做的（按序）
0. **设计参数化**（最小检查）：把槽位标签抽成模块参数（一个 `Lab : L → E.T → Set` 加证明里实际用到的性质，例如 `uniq`、`below`、`lbl-rd` 一类），先用一个最小的行（例如上折 `Up` 或嵌入 `Emb`）在新文件里按参数化写一遍，用 `Lbl` 实例化，编译。说明原族的哪些地方用到了 "下界读法" 的哪条性质。不成立就停下回报。
1. **逐行移植**：嵌入、上折、自身三行，再加 `Fold`/`Index`/`Slot` 的组装，得到 `YiGLExact.LowKeepAtˣ` 在没有 Ω 结点的层号（带 `Lbl`）上的居民；量化域按 `Lbl` 的定义（Ω 形状取 `⊥`，所以先只覆盖不含 Ω 形状的层号）。
2. **实例**：在最小实例 `YiBVSmall` 的孩子层号（`two ⊕ ↑ zero (suc d)`，d 有限或为 ω，`YiGLOmega` 有 ω 的标签）上实例化，看能否给出 `YiQLRead.Need` 一类的结论（只在 d 带精确标签时）。
3. 说明移植后还缺什么：Ω 形状层号的 `Lbl` 一条（YiEL 一路在做）、第 0 层分支前提是下界关系 `M⁰` 的问题（YiEL 一路在做）。不要替它们做。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 8G（同批另有三路，主审也在编译）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
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

