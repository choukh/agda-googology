# 构造续：限在读回域推导上的证据（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 22:56 至 23:35 |
| 工具调用 / agda 编译 (粗数) | 66 / 11 |
| token (usage 字段，按消息去重) | 输出 211687；新写入缓存的输入 547054；读缓存的输入 11228996；其余输入 96 |
| 写过的仓库文件 | `YiRQDom.lagda.md` |
| 文件前缀 | `YiRQ` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 1 件退出 0，禁用构造 0；限制版链步的 d = 1 实例逐字就是构造一路的 Cand（dom→cand、top→cand），限在读回域并不绕开值的问题；对一切 d 的机制定理（kp*ᵍ、kp₀ᵍ、start-form、drop、fall）；执行方判断 Cand 不成立（未编译） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b73/YiRQ.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### YiRQ 回报：构造续，限在读回域推导上的证据（执行方 Opus 5.5）

##### 1. 判决

**对纲领与目标的意义。** 本路新增 1 个验收文件（第 4 层，读记号），树、折叠、合法性、比较表都没有改，序数值下界没有增加，也没有新的翻译账（文件里没有新定义；γT 链、ψ_κ 只出现在验收陈述里）。

本路的核心结论（编译）：把链步限在读回域的实际推导上，并不绕开决定性问题。
- 限制版只在 `Dom` 的 `dN` 推导上量化：分支固定为 Ω 树的实际分支，源关系由推导给出，前缀 tw 1 读空。
- 它在 d = 1、n = 0、z = Ωt one 处的实例，逐字就是 YiKT 的 `Cand`（`dom→cand`、`top→cand`）。
- 所以构造路线在 d = 1 是否成立，与审核一路 YiVA 要裁决的值问题是同一件事。

我的判断（未编译）：`Cand` 不成立；d ≥ 2 的同类实例按大小也不成立。如果 YiVA 确认值会掉，就要改折叠的定义（第 4 层逼出），由作者定。

**各步进度**
- 第 0 步完成：陈述、可满足性、与宽量化接口的关系都已编译。
  - 它不撞 `no-stepU′-tw1` 与 `no-tight′`，原因有三：分支固定为 `gΩ`；反例用的分支 `gT` 不是 Ω 树的分支（`not-gT`）；`TightDom` 没有 `PrefixU` 前提，所以 `vacuous` 的空真机制不适用。
- 第 1 步未走通。我核了 YiTF 的补偿机制，判断它给不出 ψ₁(Ω_c) 级的分支（理由见第 4 节）。
- 第 2 步没有做。第 1 步挡住了，按简报停下。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 限制版陈述的类型 | `Step.StepDom`、`TightDom` | 编译（定义） |
| 宽量化（`TightStep d` 加 `OK`、`PrefixU … []`）推出限制版 | `wide→dom` | 编译定理 |
| 反例的分支不是 Ω 树的分支 | `not-gT` | 编译定理 |
| a₁ (d+1) 由 `dN` 进入读回域，前缀读空 | `dom-a₁`、`dom-hh` | 编译定理 |
| 一切 d 上 n = 0 的前提都已实填 | `dom→top` | 编译定理 |
| d = 1 的实例就是 `YiKTSlot.Cand` | `dom→cand`、`top→cand` | 编译定理 |
| 一棵树的读法上界推出 `TightDom d` 不成立 | `refute` | 编译条件定理（前提未证） |
| 对一切 d ≥ 1：↑z 顶结点的下标槽位走链，同一孩子里前缀 tw 1 的下标槽位保留 | `kp*ᵍ`、`kp₀ᵍ` | 编译定理（把 YiKT 的有限测试升为定理） |
| 对一切 d：链步折叠的起点是 `h₁ d` 的 Ω 树加两段可数尾巴 | `start-form` | 编译定理 |
| 朝 tw 1 的孩子 c′ 折时，孩子 c 的槽位走链、嵌入只留可数尾巴（含 c = c′） | `drop`、`fall` | 编译定理（按定义的行） |
| `Cand` 是否成立 | — | 判断：不成立 |
| d ≥ 2 时 n = 0 的实例 | — | 判断：不成立（按大小） |
| YiTF 的补偿（分支约 ψ_d(Ω_c)） | — | 判断：不成立 |
| 同步对象孩子 a₁ (d+1)（d ≥ 1）的值低于 S(d+1)，因而 `Tail`、`FirstMissing` 在现行折叠下为假 | — | 判断 |

##### 2. 文件表

| 文件 | 物理行 | 非空非注释代码行 | 冷编 |
|---|---|---|---|
| `probes/OCF/Lean/YiRQDom.lagda.md` | 174 | 99 | 删自身接口后 6G 冷编，退出 0；日志只有本模块一行 `Checking`；最大驻留约 2.14G，约 33 秒 |

- 检索结果：禁用构造 0，本机路径 0，`Funext` 0。
- 文首标为"读记号"，所以不做导入闭包检查。
- 临时文件 `RQ0` 到 `RQ3`（纯 `.agda`）与日志在 `<实验目录>/work/YiRQ`，最终都退出 0。

##### 3. 定理表

文件都是 `YiRQDom`。
- `Step` 的模块参数是 `k h o r B`。其中 `gΩ c = proj₁ (upz {s = sΩ k} {h = h} c (Ωt (h c)))`，`fd = feedᴸ (nd (sΩ k) h) o r B (inj₁ (inj₁ tt)) gΩ`。
- `Sᵈ d = Step (h₁ d) (hh d) (proj₂ oᴱ (suc d)) (rbᶻ (a₁ (suc d))) (D.dn Bᴱ (suc d))`，`TightDom d = Sᵈ.StepDom d`。

| 名字 | 逐字的陈述 | 白话 | 档 |
|---|---|---|---|
| `StepDom` | `∀ {κ ν} → Dom k κ → E.cof ν ≡ E.cΩ κ → (∀ η c → GR.R k η c → Dom (h c) (E.fsT ν η)) → (n : ℕ) (z : Tr k) → GR.R k (E.γT (E.Ωt ν) κ n) z → GR.R k (E.γT (E.Ωt ν) κ (suc n)) (fd z)` | 只对读回域的 `dN` 推导量化；分支是实际的 Ω 树分支 | 定义 |
| `src` | `∀ {μ c} → Dom (h c) μ → GR.R (nd (sΩ k) h) (E.Ωt μ) (gΩ c)` | 分支的源关系由推导给出 | 编译 |
| `wide→dom` | `∀ d → TightStep d → OK (D.dn Bᴱ (suc d)) → PrefixU (D.dn Bᴱ (suc d)) [] → TightDom d` | 限制版是宽量化版本的实例 | 编译 |
| `not-gT` | `TF.gT TW.cΩ₁ ≡ Sᵈ.gΩ (suc zero) TW.cΩ₁ → ⊥` | `no-tight′` 用的分支不是 Ω 树的分支 | 编译 |
| `dom-hh` | `∀ d {η c} → GR.R (h₁ d) η c → Dom (hh d c) η` | 前缀读空，孩子的读法全由 ↑c 承载 | 编译 |
| `dom-a₁` | `∀ {κ d} → GR.R zero κ d → Dom (a₁ (suc d)) (E.Ωs κ)` | a₁ (d+1) 读作 Ω_{κ+1} | 编译 |
| `dom→top` | `∀ d {κ} → GR.R zero κ d → TightDom d → Top₁ d κ`；`Top₁ d κ = GR.R (h₁ d) (E.γT (E.Ωt (E.Ωs κ)) κ 1) (Sᵈ.fd d (proj₁ (Ωt (h₁ d))))` | 一切 d 上 n = 0 的实例，前提全部实填 | 编译 |
| `dom→cand` | `TightDom (suc zero) → KT.Cand` | d = 1 的限制版推出 YiKT 的 `Cand` | 编译 |
| `top→cand` | `Top₁ (suc zero) KT.κ* → KT.Cand`（恒等） | 实例逐字就是 `Cand` | 编译 |
| `refute` | `∀ d {κ} → GR.R zero κ d → Refute d κ → TightDom d → ⊥`；`Refute d κ = ∀ {t} → GR.R (h₁ d) t (Sᵈ.fd d (proj₁ (Ωt (h₁ d)))) → t E.<ᵀ E.γT (E.Ωt (E.Ωs κ)) κ 1` | 要否定，只需一棵具体树的读法上界 | 编译条件定理；前提可满足是判断 |
| `kp*ᵍ` | `∀ d → IsNothing (kp (a₁ (suc (suc d))) (proj₂ oᴱ (suc (suc d))) (p*ᵍ d) (ink self))`；`p*ᵍ d = inj₂ (zᵍ d , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))`，`zᵍ d = proj₁ (Ωt (h₁ (suc d)))` | ↑z 顶结点的下标槽位走链 | 编译（按定义计算，d 是变量） |
| `kp₀ᵍ` | `∀ d → IsJust (kp (a₁ (suc (suc d))) (proj₂ oᴱ (suc (suc d))) (p₀ᵍ d) (ink self))` | 同一孩子里前缀 tw 1 的下标槽位保留 | 编译 |
| `start-form` | `∀ d → proj₁ (D.dn Bᴱ (suc d) (h₁ d) (ink self)) ≡ proj₁ ((Ωt (h₁ d) ⊞ TF.Y₁) ⊞ TF.Y₂)` | 链步折叠的起点是 Ω 树加两段可数尾巴（`Y₂` 即 `twᶻ 1`） | 编译（`refl`，d 是变量） |
| `drop` | `∀ (o : Ok (tw 1)) c t c′ {j} (v : j ≤ h₁ c′) → IsNothing (kp (tw 1) o (inj₂ (c , t)) (inc c′ v))` | 孩子槽位朝孩子折，一律走链 | 编译 |
| `fall` | `∀ (o : Ok (tw 1)) (B : Base (tw 1)) c′ c {j} (v : j ≤ h₁ (suc c′)) β x (y : Tr (h₁ (suc c))) e → ψ (tw 1) o (rbᶻ (tw 1)) B j (inc (suc c′) v) β (up x (suc c) y e) ≡ ψ (tw 1) o (rbᶻ (tw 1)) B j (inc (suc c′) v) β x ⊞ ψ₀ʳ (h₁ (suc c)) (proj₂ o (suc c)) (rbᶻ (h₁ (suc c))) y` | 非零孩子的嵌入只留可数尾巴 | 编译 |

**前提可满足**
- `dom→top`：取 κ = [] 由 `mz` 给出；d = 1 时用 `r₁`。
- `wide→dom`：它是包含关系，前提 `TightStep d` 本身可满足与否未定（YiTF：`TightStep 1` 等价于前缀前提不可满足）。
- `refute` 的前提 `Refute d κ`：可满足是判断，见第 4 节。

##### 4. 第一个障碍

**引理：`Cand`**，即 `TightDom 1` 在 n = 0、z = Ωt one 处的实例，逐字是 `YiKTSlot.Cand`。陈述：`GR.R (h₁ one) (ψ₁(Ω_{Ω₁})) (fd z*)`。

**是数学上挡住**，没有工程问题：全程峰值约 2.1G，没有 251，没有 124。

以下全是判断（未编译）。它们都依赖"GR.R 在第 1 层以上对值可靠"，这一点没有编译的定理，带 `mc` 的非标准形项我没有核。

- **两种读法都会丢。**
  - 前缀读空时，参照全由 ↑z 承载。↑z 的 Ω 形状的下标槽位经层号证据推进 tw 1 叶子的孩子 d+1，朝 `h₁ d` 折时恒走链（`kp*ᵍ`，编译）。
  - 前缀按非平凡读法读时，tw 1 只有自己的下标槽位保留（`kp₀ᵍ`）。这个结点的分支 c 装的是孩子 c 的内容，而这些内容不是走链（`drop`），就是只留可数尾巴（`fall`），c = c′ 时也一样。
- **为什么补偿不成立。** 自折叠把孩子的嵌入变成孩子槽位上的结点，随后被 `drop` 送进链。所以被保留结点的分支 c 的值大致是 V·ω^{α_c}，其中 V 与 c 无关，α_c 可数。要有 ψ₁(Ω_{Ω₁})，分支 c 要不低于 ψ₁(Ω_c)，例如分支 1 已经要 Ω₁²。按我的估计，输出至多到 ε_{Ω₁+1} 一带，远低于 ψ₁(Ω₃)。
- **d ≥ 2 按大小。**
  - 起点是 Ω_{h₁ d} 树加可数尾巴（`start-form`），被保留的结点只有 Ω₁ 一种（`kp*ᵍ`、`kp₀ᵍ`、`drop`、`fall`）。
  - 所以输出落在 {起点} 与可数项在加法、ω 极限、Ω₁ 上确界下的闭包里，值低于 Ω_d·Ω₂ ≤ Ω_d²。
  - 而链的第 1 项 ψ_d(Ω_{Ω_d}) ≥ ε_{Ω_d+1}。按这个判断，`Refute d d` 对 d ≥ 2 可以满足。
- **对值的推论。** 同步对象孩子 a₁ (d+1)（d ≥ 1）的值低于 S(d+1)；`Tail`、`FirstMissing` 在现行折叠下为假。

**与 YiVA 的关系。** `dom→cand` 说明，限在读回域上并没有改变 YiVA 要裁决的问题。若 YiVA 判定值会掉，就要改定义（第 4 层逼出，交作者）。候选的位置（判断）：
- `kp` 中"Ω 形状、槽位在孩子里、路径经 `inc`"一行。槽位所在的孩子与路径所经的孩子都来自同一份 `Ok` 证据里的字面 `suc d`，但 `kp` 是分开拿到它们的。要保留，需要一个"同一孩子"的见证，派发前要先对照 `obs→dec` 一族。
- `rbᶻ` 的对角线条目。
- 层号证据把下标层经 tw 1 的孩子 d+1 路由的方式。

要做成编译否定，所需工具就是 `Refute` 的上界（YiTU 一类）。

##### 5. 偏离与事故

- **30 分钟时限**：没有计时。读定义花了大量时间，估计第一个临时文件 `RQ0` 大约在开始后 50 到 60 分钟才编译，很可能超时。
- **只做到第 0 步加机制定理**：第 1 步未走通；第 2 步（接 `k2′-from-keep` 的限制版）没有做，因为前提已判断为假，再写条件定理没有意义。
- **退出码**：第一次编译经 `/usr/bin/time` 运行，打印的是 time 的退出码 1（日志里是类型错误）。之后都直接报 agda 自己的退出码。退出 42 共 4 次，都是普通类型错误（层号是变量时 `GR.R` 不展开、`ChT` 不展开、变量名与构造子 `up` 撞名），改后通过。
- 临时文件编译时，在命令行加了 `-W noUnsupportedIndexedMatch`。
- **没有读、只凭转述或签名使用的**：
  - Bedrock 手册只读了 C-9、C-10、S-1、S-3、C-24、Q-1、Q-23、H-6 的正文；EBOHandbook 4.2、4.6 读了。
  - 只按签名使用：`YiNLRaise.ΩΩ`、`fsΩΩ`、`JiaAuditClosure.cof-regular`、`fs-regular`、`YiGTGen.weakᴿ`、`<ᵀ-irrefl`；`γT`、`Ωs` 在 `EBO.lagda.md` 里检索到定义。
  - 没有读：`YiGTNode`、`YiGTIndex`、`YiGTFold`、`YiKSDesc`、`YiGIInst`（`baseᴱ`、`pre`）、`YiFRStep`，以及第七十一、七十二批的 `YiMG*`、`YiXP*`、`YiEL*`、`YiTA*`、`YiVN*`、`YiFO*`、`YiXU*`、`YiCX*`、`YiTD*`、`YiCV*`、`YiRR*`。这些按简报转述使用。
  - 回报留档只读了 YiTF、YiTL、YiKT 三份的回报部分。`YiKTSlot` 只读了第 150 到 273 行。
  - 读过全文的：`YiTLReduce`、`YiTFTw1`、`YiTFTight`、`YiGLDom`，以及 `YiRW*`、`YiTBRow`、`YiMTTab`、`YiGIRel`、`YiHCRel`、`YiSUIface`、`YiLKIface`、`YiSY*`、`YiNLCtx`。
- **同批文件**：同批 `YiVA`、`YiTU`、`YiDX`、`YiPT` 的文件没有读，也没有导入；没有改动任何已有文件。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：构造续，限在读回域推导上的证据（前缀 YiRQ，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路选项原文 "构造续：限在读回域推导上的证据 (Recommended)"。同批另四路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者定：主线停逐项，改攻整体引理（读回域上的 Leaf 加 LowKeep）；参照只用记号关系 M。第七十三批选项原文："Fable 先读定义的独立审核：值会不会掉 (Recommended), 第 2 站闭项的上界工具 (Recommended), 构造续：限在读回域推导上的证据 (Recommended), 定义改动的候选原型"；摆脱侧 "前缀 3：自身折叠后的上折 (Recommended)"。同批五路：审核 `YiVA`（Fable 5.2）、上界 `YiTU`、构造续 `YiRQ`、定义候选 `YiDX`、摆脱侧 `YiPT`（Opus 5.5），互不导入。

- **决定性问题**：塔第 1 项（及以它为前缀的层号，例如同步对象 `kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))` 的孩子 `a₁ c`）上，折叠折到更低层时值会不会掉。若掉，就要改折叠的定义（第 4 层逼出，交作者）。
- **第七十一、七十二批的事实**（主审 8G 冷编复核过，读陈述；回报在 `probes/Survey/Reports-2026-11-16/`）：
  - 已成立：精确标签下 LowKeep 对一切不含 Ω 形状的层号无条件成立（`YiXPExact.lowKeepAt-noΩ`；合流后 `YiMGFrame.lowKeepAtᵐ-noΩ`）；Leaf 在读回域上（`YiGLDom.dom-top`、`YiMGRel.topᵐ`）；记号侧工具（`YiELLim.limAt`、`YiTAChain.ex-add′`、`ex-limc`、`lbl-limc`、`YiTAReal.real-exact`、`cofΩ-all`）。
  - 关系与证据档的否定（只否定接口或证据，不否定值）：`YiXPNeg.no-index-tree-tw1ˣ`；`YiTLReduce.no-index-top`、`block-frame`、`no-lbl-hh`；`YiMGNeck.no-chain-neck`、`no-frame-neck-child`；`YiKTSlot.no-above` 与同文件配套否定（槽位 `p*`）；`YiTFTw1.no-stepU′-tw1`、`no-wholeU-tw1`（前提全部实填）；`YiTFTight.no-tight′`、`vacuous`（`TightStep 1` 等价于实际底的前缀前提不可满足）。
  - 机制（编译）：`YiTFTw1.kp-leaf`：塔第 1 项叶子上，槽位在孩子里、目标非零且不含 Ω 时折叠走链；`YiKTSlot` 的有限测试：同一孩子里分支类型与读法相同的两个槽位，一个走链（`p*`），一个保留（`p₀`）；`YiTFBound.bS`：Ω₁ 树加可数尾巴的树读法低于 Ω₁+Ω₁；`YiTFTight.Y₂-tw : proj₁ Y₂ ≡ twᶻ 1`（实际继承底含第 2 站的闭项）。
  - **值上两个执行方判断不一致**（都未编译）：构造一路 YiKT（Fable 5.2）判断 `TightStep 1` 的结论 `Cand` 不成立、同步对象的值低于里程碑 ψ₀(Ω_{Ω₂})，机制是 `kp` 对 "Ω 形状、槽位在孩子里、路径经 `inc`" 恒走链加最小比较表在塔第 1 项上的退路行；配对否定一路 YiTF 判断有补偿（叶子自己的下标槽位被保留，加上自折叠，分支约为 ψ_d(Ω_c)，对一切可数 c 取上确界可达 ψ_d(Ω_Ω) 量级），净结果未定。
- 其他：`YiVNIdx.Gen.no-value-index-mono≈`（下标的树侧值序不能作下标单调的前提）；`YiFOValue.fallback-prefix`（退路保留此前折叠的值）；`YiXUFirst.first-ceiling`（干净对象第一支 ≤ ψ₀(Ω₄)）；`YiCXWindow`（局部派发允许不唯一的标签窗口）；`YiTDOrder`、`YiCVDomain`（全域派发等价于记号系统；现主线比较表在龙骨上不满足共现覆盖）；摆脱侧 `YiRRTwo.prefix-two`。

#### 本路的方向（YiTL、YiTF 的纸面判断；YiTF 认为是必需的）
以下界关系宽量化的接口在塔第 1 项上已被否定（`no-stepU′-tw1`）。要换成只在**读回域的实际推导**上量化的证据：前缀读空（`YiTLReduce.leaf-a₁` 用的就是 "前缀 `tw 1` 取空读法"），退路行只承载平凡参照；保留与否的检查只在实际推导到的 κ 处做（不是对一切下标）。YiTF 指出的补偿机制：叶子自己的下标槽位（`inj₁`）被保留，加上自折叠，分支约为 ψ_d(Ω_c)。

#### 要做的（按序）
0. **陈述**：写出限在读回域推导上的链步证据（例如对 `YiGLDom.Dom` 的推导归纳，携带源关系，不携带折叠后的结论），以及它在同步对象孩子 `a₁ (suc d)` 上要证的那一条（`YiTLReduce.TightStep` 的限制版）；说明为什么它不撞 `no-stepU′-tw1`、`no-tight′`（那两条用的是宽量化的分支）。在 d = 1 上确认类型与可满足。不成立就停下回报。
1. **证 d = 1 的那一条**，用补偿机制（叶子下标槽位加自折叠）。
2. 推到一切 d，接 `YiTLReduce.k2′-from-keep` 的限制版，得到第 3 站的对位下界（`Kᴱ′ 2`）；挡住就交第一个挡住的引理，说明是数学上还是工程上挡住，以及它与审核一路（YiVA）要裁决的问题的关系。

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

