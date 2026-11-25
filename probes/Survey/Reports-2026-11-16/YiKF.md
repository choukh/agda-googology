# 候选折叠 (A)+(B)+(C)（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 00:18 至 00:42 |
| 工具调用 / agda 编译 (粗数) | 43 / 16 |
| token (usage 字段，按消息去重) | 输出 131603；新写入缓存的输入 270165；读缓存的输入 7037327；其余输入 80 |
| 写过的仓库文件 | `YiKFKeep.lagda.md` |
| 文件前缀 | `YiKF` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0，三件不读记号的导入闭包干净；候选 (C) 合法、全函数、单调，对一切 d 使读回顶结点的下标槽位保留（kpᵍ）；YiTF 那一点承载 ψ₁(Ω₁)（out-abc）；链步第 1 项只归约到未判定的分支前提 Branch（top、cand₁、cand₂ 是条件定理）；同步对象与里程碑的值未走通 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b74/YiKF.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。只在新文件里写，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiKF 回报：候选折叠 (A)+(B)+(C)

#### 1. 判决

**对纲领与目标**：候选 (C) 能写成合法、全函数、单调的折叠，不比较 Ω 形状的孩子下标，三个不读记号的文件导入闭包干净。它让 d = 2 的槽位 `p₂` 保留，并且对一切 d 成立（编译定理，d 是变量）。但同步对象与里程碑 ψ₀(Ω_{Ω₂}) 的值没有拿到：链步第 1 项只归约到一条未判定的分支前提 `Branch`。所以候选目前是"机制成立、值未走通"，不足以支持替换主线。主线定义没有动。

**各步到哪里**
- 第 0 步（设计与先验检查）：完成。`p₂` 在 (C) 下保留。
- 第 1 步（实现）：完成。折叠、`mono`、`monoˡ`、闭项 `twᶜ`、`EBOᶜ`、证据 `pvT`、`pvΛ` 都编译。
- 第 2 步 (i) 三个障碍点：完成。`p*`、`p₂` 保留；YiTF 那一点承载 ψ₁(Ω₁)（定理）。
- 第 2 步 (ii) 链步：部分。对一切 d，n = 0、z 取 Ω 树时的输出里有一个保留的 Ω 结点；承载参照是条件定理，前提 `Branch` 未判定。
- 第 2 步 (iii) 里程碑基本列第 0、1 项：未做，卡在 `Branch`。
- 第 3 步代价清单：见第 6 节，全部是判断。

**先验检查（对照 `YiAbsObs` 的 `obs→dec` 一族）**
- 目标是否指定孩子：(C) 只动 `ink` 行，目标在下标层，路径 `v ∙ kh c` 对每个孩子一致给出；`inc c′` 行没改（`kpʳ` 该行仍是 `nothing`）。不满足 `branch→wdec`、`hand→wdec` 的前提。
- 孩子下标上的证据函数：`Pv` 里确有 `(c : Tr k) → Org k (h c)`，但值是"孩子 c 里的槽位到 k 的槽位"的可缺表，只涉及一个孩子，不是 `Maybe (c ≡ c′)`，没有对角。不满足 `viaE→dec`、`diag→dec` 的前提。它按构造子读 c，这一点与 `rbᶻ` 同类。
- 是否按存在性保留：不是 `Full`。`rel-Ω-no`（编译）说明同一个 Ω 形状孩子里的两个槽位即使字面相同也没有条目。孩子下标只在 ⊤ 与 ℕ 上比较。
- 壁垒、`no-all-node-pairs`、`YiCVDomain`：没有新下标类型，没有全结点比较，表可缺。这一条是读陈述后的判断，不是编译定理。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 简报写法的 (C)（只在 `ink` 行改 `kp`）在实际折叠里不起作用：折叠沿 `ink` 行进孩子后层号变成 `h c`，父层的来源表不在孩子的证据里 | 第一版 `sync₂ᶜ` 编译失败（退出 42，文件没有留） | 有限测试 |
| 为此折叠多带一张朝当前目标的来源表 `ot`，超出简报的 "穿过折叠的 `Pv`" | `YiKFKeep.dlg`、`YiKFFold` | 设计偏离，已编译 |
| `ot` 在换目标（回灌、底）时清空，内层回灌不继承来源 | `YiKFFold` 里的 `org-no _ _` | 判断：可能再掉值，未测 |
| `Branch` 未判定 | `YiKFValue.Branch` | 判断 |
| 候选在 `tw 1` 那一点与 (A)+(B) 的输出不是逐字相等（`refl` 不过），只同形 | `YiKFValue.Inst.shape` | 编译事实 |
| 值的定理用标准底 `B₀`，不是 `YiKTSlot.Cand` 的继承底 `D.dn Bᴱ` | `YiKFTest.outᶜ` | 说明 |

#### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`。删自己的接口后依次冷编，6G 上限。

| 文件 | 代码行 | 退出码 | 峰值驻留 | 读记号 |
|---|---|---|---|---|
| `YiKFKeep.lagda.md` | 203 | 0 | 0.21G | 否，闭包 OK |
| `YiKFFold.lagda.md` | 148 | 0 | 0.24G | 否，闭包 OK |
| `YiKFTest.lagda.md` | 64 | 0 | 0.16G | 否，闭包 OK |
| `YiKFValue.lagda.md` | 103 | 0 | 1.6G，约 21 秒 | 是，验收文件 |

日志里只有各自模块的 `Checking` 行。禁用构造与本机路径检索为 0。

#### 3. 定理表

**`YiKFKeep`（编译定理）**
- `Pv`、`Org`：新证据。`PvS (sΩ k) h = Pv k × ((c : Tr k) → Org k (h c))`；`OrgS k (sΩ k″) = (t : Pos⁼ k″) → Keep k (Br⁼ k″ t) (bz⁼ k″ t)`。白话：每个 Ω 形状结点给每个孩子一张表，记孩子层号里各 Ω 结点的下标槽位来自 k 的哪个槽位，可缺。
- `Pv↑ : (k : L) → Pv k → (y : Tr k) → Pv (↑ k y)`，`Pv⊕ : (a b : L) → Pv a → Pv b → Pv (a ⊕ b)`，`pvT : (n : ℕ) → Pv (tw n)`，`pvΛ : Pv Λ`。白话：证据对读回、加法、塔、Λ 都是闭项。
- `rowC`：`kpʳ (nd (sΩ k) h) o pv (inj₂ (c , t)) (ink v) ≡ alt (kpʳ⁼ (h c) (proj₂ o c) (proj₂ pv c) t (v ∙ proj₂ (proj₁ o) c)) (bindK (org-at k (h c) (proj₂ (proj₁ pv) c) t) (λ p′ → kpʳ k (proj₁ (proj₁ o)) (proj₁ (proj₁ pv)) p′ v))`。白话：那一行先用原判定，走链时查来源表并交给下标层。
- `keepʳ : (ℓ : L) (o : Ok ℓ) (pv : Pv ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) → Ref (kp ℓ o p w) (kpʳ ℓ o pv p w)`，其中 `Ref m m′ = ∀ K → m ≡ just K → m′ ≡ just K`；`keep-kpᶜ` 同形，对一切 `ot`。白话：原判定保留的地方，新判定给同一个槽位与换型。
- `rel-Ω-no : ∀ k h (x y : Σ (Tr k) λ c → Pos⁼ (h c)) → rel (nd (sΩ k) h) (inj₂ x) (inj₂ y) ≡ nothing`。白话：Ω 形状孩子之间不比较。

**`YiKFFold`（编译定理）**
- `Fold.ψ : (ℓ : L) → Ok ℓ → Rb ℓ → Pv ℓ → Base ℓ → (j : L) → j ≤ ℓ → Org j ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j`，`Fold.mono : … → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o r pv B j w ot β x) ◃ proj₁ (ψ ℓ o r pv B j w ot β y)`，`monoˡ` 同形。对一切 `K : KeepFnᴾ` 与两种开关。
- `row-ink`、`row-fbᴾ`、`row-liftᴾ`：三行的形状，都是 `refl`。
- 闭项 `twᶜ : ℕ → Tr zero`，`EBOᶜ : Tr zero`。

**`YiKFTest`**
- `kpᵍ : ∀ d → kpʳ (a₁ (suc (suc d))) (proj₂ oᵈ (suc (suc d))) (proj₂ pvᵈ (suc (suc d))) (pᵍ d) (ink self) ≡ just (qᵍ d , (λ z → z) , refl)`；`kpᵍᶜ` 对 `kpᶜ` 同陈述。编译定理，d 是变量。白话：读回顶结点的下标槽位保留在目标层自己的槽位上，换型是恒等；d = 0 是 `p*`，d = 1 是 `p₂`。对照 `YiRQDom.kp*ᵍ`（原判定对一切 d 走链）。
- `kp₀ᵍ : ∀ d → kpᶜ … (p₀ᵍ d) (ink self) (org-no _ _) ≡ kp … (p₀ᵍ d) (ink self)`。编译定理。白话：前缀 tw 1 的槽位不变。
- 有限测试：`kp*ᶜ`、`kp₂ᶜ`（`≡ just (q′ , (λ z → z) , refl)`）、`kp₂′ᶜ`；`syncᶜ : HeadΩ (pr (outᶜ zero))`，`sync₂ᶜ : HeadΩ (pr (outᶜ n1))`，`sync₂ᴬᴮ : HeadLim (pr (outᴬᴮ n1))`（d = 2 时 (A)+(B) 同一处仍是 ℕ 极限）；`tw1ᶜ : FirstLimΩ (el out₁ᶜ 0)`。

**`YiKFValue`（读记号）**
- `out-abc : GR.R lv1 γ₁ out₁ᶜ`。编译定理。白话：YiTF 那一点上候选的输出承载 ψ₁(Ω₁)。
- `hdᵍ : ∀ d → HeadΩ (pr (outᶜ d))`，`posᵍ : ∀ d → posΩ (pr (outᶜ d)) (hdᵍ d) ≡ qᵍ d`。编译定理，d 是变量。白话：在实际折叠的下行过程中，那个结点对一切 d 保留。
- `At.br-form : ∀ c → brᵍ d c ≡ proj₁ (next⁺ β) + proj₁ (G (brΩ (proj₁ (Ωt X₀)) tt c))`。编译定理。白话：分支是第 0 个链点的折叠加上孩子层 `X₀` 上朝 `h₁ (d+1)` 的折叠。
- `top : ∀ d {t κ} → E.cof t ≡ E.cΩ κ → GR.Rd (h₁ d) κ → Branch d t → GR.R (h₁ (suc d)) t (outᶜ d)`，其中 `Branch d t = ∀ η c → GR.R (h₁ d) η c → GR.R (h₁ (suc d)) (E.fsT t η) (brᵍ d c)`。条件定理。前两个前提有实例；`Branch` 是否可满足未判定。
- `cand₁ : Branch zero t₁ → GR.R (h₁ n1) t₁ (outᶜ zero)`，`t₁ = E.ψ κ₁ (E.Ωt (E.Ωt κ₁)) ∷ []`，即 ψ₁(Ω_{Ω₁})，与 `YiKTSlot.Cand` 的参照相同。`cand₂ : Branch n1 t₂ → GR.R (h₁ (suc n1)) t₂ (outᶜ n1)`，t₂ 是 ψ₂(Ω_{Ω₂})。都是条件定理。

#### 4. 第一个障碍

**引理**：`YiKFValue.Branch zero t₁`，即对一切读作 η 的可数树 c，分支 `brᵍ zero c` 承载 ψ₁(Ω_η)。

**机制（读定义的判断，未编译）**
- 分支进孩子层 `Xc c = nd sS (λ _ → tw 1 ⊕ … ⊕ ↑ zero c)`，它的 Ω 树在整个孩子层的槽位上走链。
- 链点里又遇到 `Ωt (tw 1)`：它的第 0 层槽位由 (A) 保留，分支落到 `tw 1` 上 "目标经孩子 2、嵌入在孩子 c″" 一行。c″ 非零时最小表缺项，走 (B) 的上折回退 `ψˡ`。
- 所以需要 `ψˡ` 在 `tw 1` 一切孩子上的值引理。这条引理现在没有；主线的 Leaf、LowKeep、`Core` 都是对 `YiTBRow.ψ` 陈述的，不能直接套用。
- 另外，c 是变量时 `flr` 卡在 `tw 1 ⊕ … ⊕ ↑ zero c` 上不化简，证明要先对 c 分情况。

**性质**：主要是数学上未做（候选折叠的值理论要从头建立），其次是工程量。没有编译的否定，只写"未走通"。

#### 5. 偏离与事故

- **(C) 的实现形态与简报不同**：见问题表前两行。`kpʳ` 里保留了简报写法的那一行，另加折叠带着走的 `ot`。两者并存，没有证明它们一致。
- **来源表的构造会求值分支**：`Pv↑` 在读回结点上对每个孩子 c 计算 `g (fromBr k p c)` 再按构造子读，不检查函数 g 本身。
- **`ink` 以外的行没有委托**：有来源的槽位在 `inc`、`inu` 行仍按原判定。这是照简报范围做的，没有试扩展。
- **折叠正文是脚本生成的**：从 `YiDXFold` 第 81 至 189 行机械插入参数，脚本在临时目录。第一版正则误伤 `emb-mono`，已改。
- **一次误报退出码**：用 `/usr/bin/time -l` 包编译时沙箱拒绝 sysctl，退出 1；去掉后重新冷编，上表是重跑的结果。
- **30 分钟时限**：没有计时。
- **没有读、只凭转述引用的**：`YiVA` 审核与封存附件、`YiVALeaf`、`YiTFBound`、`YiTFTight`、`YiTUReduce`、`YiXUFirst`、`Barrier.lagda.md` 正文、`YiCVDomain` 与 `YiTDExpose` 除文首与一条陈述以外的部分、`EBOHandbook` 第 4 节、Bedrock 性能手册（没有遇到堆问题，所以没查）。`YiKTSlot`、`YiRQDom`、`YiGTNode`、`YiAbsObs`、`YiDX*` 三件读了全文。

#### 6. 代价清单与翻译账（全部是判断，没有编译核对）

**替换主线要重做的**
- 折叠签名多两个参数（`Pv`、`ot`），所有调用点要改。合法性是类型，`mono` 已有。
- View 与 FGH：对树陈述的部分不依赖折叠；闭项换成 `twᶜ`、`EBOᶜ` 后，凡是对 `twᶻ`、`EBOᶻ` 逐字陈述的定理要重证。
- 已证的站值、终点无条件值、BTBO 下界：都对 `YiTBRow.ψ`，要重做。`keepʳ` 只保证原来保留的结点槽位不变；原来走链的结点可能变成保留，退路行也变了，所以不能整体搬。
- `lowKeepAt-noΩ`、`dom-top`、`YiGTNode.Core`：`node-at` 对任意 `K` 成立，但 `F` 与 `feed` 固定为旧折叠，要改成对折叠参数化后再实例化。
- 依赖 "走链" 的结果不再成立或不再适用：`YiTFTw1.kp-leaf`、`YiRQDom.kp*ᵍ`、`drop`、`fall`、`YiTFBound` 的上界、`no-out₀`、`YiTUReduce` 的链点上界。
- `ψˡ` 需要自己的 Leaf 与 LowKeep 值引理，这正是第 4 节的障碍。

**翻译账**
- `Pv`、`Org`、`walk`、`rel` 的形状来自读回 `↑` 与槽位的嵌套结构，不读记号的基本列。记号只出现在 `YiKFValue`。
- 新增脚手架约 200 行证据加一个折叠参数。动机是验收发现掉值，按规则应单列 "第 4 层逼出"。
- 没有新增构造子，闭包定理没有新增专属前提；但 `Branch` 没证，谈不上闭包定理。
- 这一步是否加深翻译：判断为没有加深，也还不能算带来值上的进展。
- 没有改 `probes/README.md`、`LOG.md`、台账与留档。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：候选折叠 (A)+(B)+(C)，在它上面重测同步对象与里程碑（前缀 YiKF，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。**这是候选：只在新文件里写，不改任何已有文件，不进主线；是否替换由作者定**（AGENTS "第 4 层不反过来改前 3 层"，改动理由来自树侧，翻译账里单列 "第 4 层逼出"）。同批另两路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- Fable 5.2 先读定义、封存后的独立审核（`probes/Survey/Reports-2026-11-16/YiVA.md`，封存件附件 `attachments/YiVA-plan.md.txt`）的意见：塔第 1 项为前缀的层号上（同步对象 `kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))` 及更小的对象），现行折叠会掉值（估计同步对象 ≲ ψ₀(Ω_Ω·Ω₂)，低于里程碑 ψ₀(Ω_{Ω₂})，把握约 70%，判断）。构造一路 YiKT（Fable）与构造续 YiRQ（Opus）独立判断同向。
- 作者据此定（选项原文）："两条并行：候选折叠与编译否定 (Recommended)"：一路在新文件里实现候选 (C)，与 (A)+(B) 合成候选折叠，在它上面重测同步对象与里程碑；一路做第 1 层的值上界语义，把审核意见做成编译否定。**主线定义暂不动**；候选达到里程碑后再交作者定是否替换。另有一路摆脱侧（AGENTS 1:1）。同批三路：候选折叠 `YiKF`（Fable 5.2）、编译否定 `YiUS`（Opus 5.5）、摆脱侧 `YiCA`（Opus 5.5），互不导入。
- **已编译的机制**（主审 8G 冷编复核过，读陈述）：
  - `YiVALeaf`（不读记号）：`ent`（最小表 `tbᶻ` 在两个非零孩子之间无条目）、`fall`（塔第 1 项上非零孩子的嵌入逐字是 "折 x ⊞ ψ₀ᶻ y"，对一切证据、底、目标、路径、起点）、`fall-diag`、`leaf-node`、`leaf-branch`（叶子朝第 1 层折时保留的每一支逐字是 "起点 ⊞ ψ₀ᶻ (Ωt (h₁ z))"）。
  - `YiRQDom`：`kp*ᵍ`、`kp₀ᵍ`（对一切 d：孩子层号顶结点的下标槽位走链，前缀 `tw 1` 的下标槽位保留）、`start-form`（链步起点是 `Ωt (h₁ d)` 加两段可数尾巴，其中一段是 `twᶻ 1`）、`drop`（`kp (tw 1) o (inj₂ (c , t)) (inc c′ v)` 恒为 `nothing`）、`fall`、`dom→cand : TightDom (suc zero) → KT.Cand`、`refute : ∀ d {κ} → GR.R zero κ d → Refute d κ → TightDom d → ⊥`（`Refute d κ = ∀ {t} → GR.R (h₁ d) t (Sᵈ.fd d (proj₁ (Ωt (h₁ d)))) → t E.<ᵀ E.γT (E.Ωt (E.Ωs κ)) κ 1`）。
  - `YiKTSlot`：`Cand`、`tight-at`、`KeepSpec′`、`Row′.node-above`、槽位 `p*` 与 `p₀`。`YiTFTw1.kp-leaf`、`no-stepU′-tw1`；`YiTFBound`（`bZ`、`bD`、`bS`：第 1 层一类树的读法上界）；`YiTFTight.Y₂-tw`。
  - 候选原型 `YiDXFold`（不读记号）：`KeepFn`、`module Fold (K : KeepFn) (lifted : Bool)`（折叠变体，`mono`、`monoˡ`）、(A) `kpᴬ`（字面第 0 层的槽位在目标地板保留；`rowA`、`rowA-indep`、`keep-kp`）、(B) 上折回退 `ψˡ`（`row-fb`、`row-lift`、`sel`）；`YiDXValue`：`spec*ᴬ`、`out-ab`（(A)+(B) 在 YiTF 那一点承载 ψ₁(Ω₁)）、`no-out₀`、`no-outᴬ`；`YiDXTest`：`kp₂ᴬ`（d = 2 时非零而低于目标的槽位在 (A) 下仍走链）、(C) 的对应检查 `at-q′ : at (a₁ n3) p₂ ≡ at (h₁ n2) q′`、`br-q′`、`kp-q′`。
  - 上界：`YiTUReduce`（`ubs→goalᶻ`：第 2 站闭项 ≤ BTBO ⇐ 每个链点一行的值上界；`ub0`、`ub1` 已证）；`YiXUFirst.first-ceiling`。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+2)；LowKeep 在一切不含 Ω 形状的层号上成立（`YiXPExact.lowKeepAt-noΩ`、`YiMGFrame.lowKeepAtᵐ-noΩ`）；Leaf 在读回域上（`YiGLDom.dom-top`）；摆脱侧两条实际链一切前缀的值界（`YiPTAll.prefix-all`）。

#### 本路的任务
YiDX 判断：(A)+(B) 只覆盖槽位层号字面为 0 的情形；d = 2 起要候选 **(C) 按读回来源委托给下标层**：在 `ink` 行，若孩子里的槽位来自下标层 k 的某槽位 p′（读回 `↑ k (Ω p′ g)` 的下标恰是 `at k p′`，见 `at-q′`、`br-q′`），就用下标层上的 `kp k _ p′ v` 决定保留。代价：要一种类似比较表 `Rb` 的新证据（读回来源，YiDX 记为 `Pv`），对塔各项构造（仿 `OkO↑`、`OkO⊕`，处理 ⊕ 的位置拆分与分支换型），并穿过整个折叠；估约 250 行。

#### 要做的（按序）
0. **设计与先验检查**：写出新证据 `Pv` 的类型与它在折叠里的用法；按 AGENTS "开新行前的先验检查" 逐条对照 `probes/OCF/Lean/YiAbsObs.lagda.md` 的 `obs→dec` 一族（`branch→wdec`、`hand→wdec`、`viaE→dec`、`full→dec`）、壁垒 `probes/OCF/Barrier.lagda.md`、`YiTDExpose.no-all-node-pairs`、`YiCVDomain`；说明 `Pv` 只记 "槽位来自哪里"、不比较孩子下标。在 d = 2 的槽位 `p₂` 上确认 (C) 使它保留。不成立就停下回报。
1. **实现候选折叠**：在新文件里，把 `YiDXFold.Fold` 扩成带 `Pv` 的版本（(A)+(B)+(C)），证合法性（类型）、全函数、`mono`；给出闭项（候选的 `tw` 各项与 `EBO`）及它们的 `Pv`。
2. **重测**：在候选下，(i) 三个已知障碍点（`p*`、`p₂`、YiTF 那一点）；(ii) 同步对象孩子 `a₁ (suc d)` 上的链步（`TightStep` 或 `YiRQDom.TightDom` 的候选版），先 d = 1、2；(iii) 若能，干净对象或同步对象上里程碑 ψ₀(Ω_{Ω₂}) 基本列的第 0、1 项。
3. **交代价清单**：候选替换主线时，第一档成品（View、FGH、合法性）与已证的站值、LowKeep（`lowKeepAt-noΩ`）哪些要重做；翻译账。

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

