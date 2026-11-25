# 编译否定：第 1 层的值上界语义（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 00:18 至 01:22 |
| 工具调用 / agda 编译 (粗数) | 90 / 27 |
| token (usage 字段，按消息去重) | 输出 304390；新写入缓存的输入 501012；读缓存的输入 24473940；其余输入 164 |
| 写过的仓库文件 | `YiUSBound.lagda.md`, `YiUSUni.lagda.md` |
| 文件前缀 | `YiUS` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0；Refute 归到 γ₁ 不是读法（single、single⁻），继承底每层的形状（base-form），d = 2 时目标层保留的是 Ω₁ 槽位结点（leaf-node₂），第 1 层一切读法低于 Ω₂（bL1，判定不了 Cand）；统一阈值工具的闭合引理被编译否定（no-uniform₂、no-uniform₁，三个前提各自可满足）；掉值仍是判断 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b74/YiUS.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### YiUS 回报：第 1 层的值上界语义（执行方 Opus 5.5）

##### 1. 判决

**对纲领与目标意味着什么。** 本路没有把审核意见 "会掉值" 做成编译否定，也没有证出 `Refute`。所以 "现行折叠在塔第 1 项前缀层号上会掉值" 仍是判断，既没有被证实，也没有被推翻。主线定义一行没动。因为没有得到值层面的否定，"停下交作者" 的条件没有触发。

编译出来的有四样：
- 把 `Refute` 归到一个项上（`single`）；
- 继承底在每一层的形状（`base-form`）；
- 目标层上保留下来的结点种类（`leaf-node₂`）；
- 对工具 (a) 的配对否定（`no-uniform₂/₁`）：`YiTFBound` 那种 "对推导归纳、整类用同一个阈值" 的做法，在含 γ₁ 的区间里不能闭合。

**各步到哪一步。**
- 第 0 步：目标取 `Refute 2 (natT 2)` 与 `Refute 1 κ*`。
  - 工具 (a)（语法类加统一阈值）试了，结果是对它的闭合引理的编译否定。
  - 工具 (b)（树侧值加 "读法对值可靠"）没有写代码。判断它缺 "第 1 层以上记号项到树侧值的解释"。
  - 第 0 步不成立，按简报停下。
- 第 1 步：未走通。
- 第 2 步：未开始。
- 第 3 步：每条否定否定的是什么，见定理表。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `Refute d κ` 等价于 "γ₁ 不是 `fd` 的下界读法"，对一切 d、κ | `YiUSBound.single`、`single⁻` | 编译定理 |
| 继承底在每层 i、每条路径 u 上逐字是 `(Ωt i ⊞ Y₁) ⊞ Y₂`，对一切 d | `base-form` | 编译定理 |
| 朝 `h₁ 2`、经孩子 3 时，tw 1 叶子的下标槽位保留成 `h₁ 2` 的 Ω₁ 槽位结点（分支是可数树），不是 Ω₂ 槽位 | `leaf-node₂` | 编译定理 |
| 第 `h₁ 1` 层一切树的读法低于 Ω₂；d = 1 的 γ₁ 也低于 Ω₂，所以这个界判定不了 `Cand` | `bL1`、`γ₁*<Ω₂` | 编译定理 |
| 形如 ψ₂(a) 的阈值（γ₁(2) 在其中）不能同时满足 ℕ 极限、Ω₁ 结点、Ω₂ 结点三行的闭合要求；ψ₁(a)（γ₁(κ*) 在其中）不能同时满足前两行 | `YiUSUni.no-uniform₂`、`no-uniform₁`，实例 `no-uniform-γ₂`、`no-uniform-γ₁*` | 编译否定（工具的接口） |
| 三条要求各自可满足 | `reqL-Ω₂`、`req₀-Ω₂`、`req₁-θ₁` | 编译定理 |
| `fd₂` 的范式顶上是 `lim (cum (λ n → lim (iter …)))`；下集里有 Ω₂ 槽位结点（沿第 0 项走 8 层碰到）；路径 `kh₂` 的范式以 `inc 3 (inc tt self)` 收尾 | 临时目录 `USShape.agda`，交互范式化 | 有限测试（未进仓库） |
| `fd₂` 的下集里有 `leaf-node₂` 那一类 Ω₁ 结点：经 e₀ = zero 那条链，进 tw 1 层，那里的底是 `Ωt (tw 1) ⊞ …` | 手算，依据 `base-form`、`kp₀ᵍ`、`leaf-node₂` | 判断 |
| `fd₂` 的下集里，三种结点都无界地嵌套 | — | 判断 |
| `Refute 2 (natT 2)`、`Refute 1 κ*` 成立 | — | 判断（方向同 YiVA、YiRQ） |
| 树类里没有 Ω₁ 槽位结点时，统一阈值 ψ₂(Ω₁) 在第 `h₁ 2` 层能闭合：Ω₂ 结点上共尾 Ω₁ 的读法，在下标 Ω₁ 处的哑值等于阈值本身，自相矛盾 | — | 判断（未编译） |

##### 2. 文件表

| 文件 | 物理行 | 代码行（非空） | 冷编 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiUSUni.lagda.md` | 317 | 234 | 删自身接口后 6G 冷编，退出 0，约 17 秒，峰值驻留约 1.4G；日志只有本模块的 `Checking` |
| `<仓库>/probes/OCF/Lean/YiUSBound.lagda.md` | 123 | 73 | 删自身接口后 6G 冷编，退出 0，约 21 秒，峰值驻留约 1.8G；日志只有本模块的 `Checking` |

- 自查结果：
  - 禁用构造、洞、本机路径、`Funext` 的检索都为 0。只命中选项行里必有的 `--without-K`。
  - 文首：`YiUSUni` 4 行，`YiUSBound` 3 行。
  - 两件都标 "读记号"，所以没有跑 `importclosure.py`。
- 临时文件都在 `<实验目录>/work/YiUS/`：
  - `USShape.agda`：形状与范式化。
  - `USBound.agda`、`USBase.agda`、`USUni.agda`、`USSat.agda`：仓库件的草稿，都退出 0。
  - `norm.sh`：交互范式化脚本。
  - 各次日志。

##### 3. 定理表

档都是编译定理，`no-uniform*` 是编译否定。

**`YiUSBound`**

- `single : ∀ d κ → (GR.R (h₁ d) (γ₁ κ) (RQ.Sᵈ.fd d (proj₁ (Ωt (h₁ d)))) → ⊥) → RQ.Refute d κ`
  - 其中 `γ₁ κ = E.γT (E.Ωt (E.Ωs κ)) κ 1`。
  - 白话：只要 γ₁ 不是读法，`Refute` 就成立（用 `mc` 加三歧）。
- `single⁻ : ∀ d κ → RQ.Refute d κ → GR.R (h₁ d) (γ₁ κ) (RQ.Sᵈ.fd d (proj₁ (Ωt (h₁ d)))) → ⊥`
  - 白话：反方向也成立。
- `base-form : ∀ d i (u : i ≤ a₁ (suc d)) → proj₁ (D.dn Bᴱ (suc d) i u) ≡ proj₁ ((Ωt i ⊞ TF.Y₁) ⊞ TF.Y₂)`
  - 白话：链步折叠里用到的每个底，都是该层的 Ω 树加两段可数尾巴。`YiRQDom.start-form` 只说了 `h₁ d` 一层。
- `leaf-node₂ : (B : Base (tw 1)) (β : Tr⁺ (h₁ (suc (suc zero)))) → ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ (suc (suc zero))) (inc three (inc tt self)) β (proj₁ (Ωt (tw 1))) ≡ Ω⁺ q₁₂ (λ z → ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) B (h₁ (suc (suc zero))) (inc three (inc tt self)) β (proj₁ (upz {s = sΩ zero} {h = h₁} z (Ωt (h₁ z)))))`
  - 其中 `q₁₂ = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))`。
  - 白话：d = 2 时目标层保留下来的是 Ω₁ 槽位的结点。
- `bL1 : ∀ {t x} → GR.R L1 t x → t <ᵀ Ω₂`
  - 其中 `L1 = h₁ (suc zero)`，`Ω₂ = E.ψ (E.natT 2) [] ∷ []`。
  - 白话：第 1 层一切树读到的都低于 Ω₂，不用树类。
- `γ₁*<Ω₂ : γ₁ KT.κ* <ᵀ Ω₂`
  - 白话：d = 1 的参照 ψ₁(Ω_{Ω₁}) 在这个界之下。
- `no-uniform-γ₂ : ReqL (γ₁ (E.natT 2)) → Req₀ (γ₁ (E.natT 2)) → Req₁ (γ₁ (E.natT 2)) → ⊥`
- `no-uniform-γ₁* : ReqL (γ₁ KT.κ*) → Req₀ (γ₁ KT.κ*) → ⊥`

**`YiUSUni`**

三条闭合要求的定义：
- `ReqL θ = ∀ t → E.cof t ≡ cω → (∀ n → E.fsn t n <ᵀ θ) → t <ᵀ θ`
- `Req₀ θ = ∀ t → E.cof t ≡ cΩ [] → (∀ η → η <ᵀ E.Ωs [] → E.fsT t η <ᵀ θ) → t <ᵀ θ`
- `Req₁ θ = ∀ t → E.cof t ≡ cΩ (E.𝟏 ∷ []) → (∀ η → η <ᵀ E.Ωs (E.𝟏 ∷ []) → E.fsT t η <ᵀ θ) → t <ᵀ θ`

定理：
- `no-uniform₂ : ∀ a → ReqL (E.ψ (E.natT 2) a ∷ []) → Req₀ (E.ψ (E.natT 2) a ∷ []) → Req₁ (E.ψ (E.natT 2) a ∷ []) → ⊥`
  - 白话：阈值本身就是反例。它的共尾度只有 ω、Ω₁、Ω₂ 三种（`band₂`），落在哪一行，那一行在 t = θ 处就推出 θ < θ（`fsn<`、`fsT<`）。
- `no-uniform₁ : ∀ a → ReqL (E.ψ (E.natT 1) a ∷ []) → Req₀ (E.ψ (E.natT 1) a ∷ []) → ⊥`
  - 白话：Ω₁ 区间同理。
- `fsn< : ∀ t → E.cof t ≡ cω → ∀ n → E.fsn t n <ᵀ t`
- `fsT< : ∀ t {μ} → E.cof t ≡ cΩ μ → ∀ {η} → η <ᵀ E.Ωs μ → E.fsT t η <ᵀ t`
  - 白话：对一切项，基本列项都低于原项，不要标准形。
- `reqL-Ω₂ : ReqL Ω₂`，`req₀-Ω₂ : Req₀ Ω₂`，`req₁-θ₁ : Req₁ θ₁`（`θ₁ = E.ψ (E.natT 2) Ω₁ ∷ []`）
  - 白话：否定的三个前提各自可满足，而且都在区间之内满足（Ω₂ 是 a = []，θ₁ 是 a = Ω₁）。
- `mLΩ₂ : ∀ s → E.cof s ≡ cω → E.fsn s 2 <ᵀ Ω₂ → s <ᵀ Ω₂`，`LΩ₂ : ∀ {s μ} (v : VΩ s μ) → μ ≡ [] → fΩ v (E.natT 2) <ᵀ Ω₂ → s <ᵀ Ω₂`
  - 白话：阈值 Ω₂ 的两条引理，`bL1` 用。

**每条否定否定的是什么。**
- `no-uniform*` 否定的是一个工具接口：三条对一切项量化、不看树类的闭合引理，不能同时成立。
  - 它不否定下界关系的陈述，不否定链步接口，也不涉及实际对象的值。
  - "因此 YiTFBound 式的统一阈值不能证 `Refute`" 是对它的读法，属于判断。理由是，对含自嵌套 ℕ 极限、Ω₁ 结点、Ω₂ 结点的树类做统一阈值的归纳，t = θ 处要用的正是这三条。
- 落在两个 γ₁ 上，挡住的行不同：
  - d = 2 的 γ₁ 共尾度是 Ω₂，挡在 Ω₂ 结点一行；
  - d = 1 的 γ₁ 共尾度是 Ω₁，挡在 Ω₁ 结点一行。

##### 4. 第一个障碍

**引理**：`fd₂` 的 ◃ 下集上逐棵树的上界证书。
- 其中 `fd₂ = RQ.Sᵈ.fd 2 (proj₁ (Ωt (h₁ 2)))`。
- 也就是给每棵子树 x 一个界项 θ_x，使 ℕ 极限、Ω₁ 结点、Ω₂ 结点、嵌入四行，在子树各自的界上局部闭合。
- 这需要两样东西，仓库里都没有：
  1. 对一族参数化的界项（Ω₂·α 一类）成立的阈值引理，即标准形阈值之上基本列共尾的一般引理。现有的只对单个阈值（Ω₁、Ω₁+Ω₁、Ω₂、ψ₂(Ω₁)）逐个写。
  2. 沿折叠逐层（`h₁ 2`、`M z`、`N c`、tw 1）算出 α_x 的上界模拟。

**是数学上挡住。**
- 统一阈值这条路已有编译否定（`no-uniform₂`）。
- 工具 (b) 要一个从记号项到第 1 层以上树侧值的解释，并且要与基本列相容。判断：这等于在第 1、2 层重做一遍折叠函数的构造。
- 两条路的根源相同：读法是下界关系。在 Ω₁ 结点上，要从可数多个子树的界取一个共同的上界项，构造性地做不到；只有在第 0 层，有树侧的值，可以取上确界。

**判断**：真正挡住统一阈值的只有 Ω₁ 槽位结点。没有它们时，ψ₂(Ω₁) 能闭合（问题表最后一行）。而 `fd₂` 里有这类结点（`leaf-node₂` 加手算）。

##### 5. 偏离与事故；没有读、只凭转述引用的东西

**事故与偏离**
- **一次 251。** `single` 的第一版对真目标 `with tri t (γ₁ κ)`，6G 堆耗尽，约 55 秒。
  - 二分：去掉 `base-form` 后仍是 251，定位到 `with` 对含 `fd` 的上下文做抽象。
  - 按 E-2、C-9 改成在变量谓词上消费三歧（`below`），退出 0。没有原样重跑。
- 临时目录里交互范式化 `walk 3 200 fd₂` 时 251 一次，只是诊断，没有重跑。`fd₂` 的完整范式约 3.7MB，只取了顶层形状。
- 第一个编译的临时文件 `USShape.agda` 在读完定义之后才写，没有计时，可能超过 30 分钟。
- 没有用 Q-1 的 profile：仓库文件没有撞墙，那次 251 已由二分定位。
- 第 0 步 (b) 只做了判断，没有编译最小件。

**没有读、只凭转述引用的**
- 通读或检索过的：
  - 通读：`YiRQDom`、`YiKTSlot`、`YiTFBound`、`YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`、`YiTBRow`、`YiMTTab`、`YiLKIface`、`YiSYReduce`、`YiSYDesc`、`YiGIRel`、`YiHCRel`、`EboLeanDef`。
  - 只读相关段落：`EboLeanView`、`EBO`。
- 只读了文首、签名或部分段落：`YiTFTight`（Y₁、Y₂、`β-form`）、`YiTFTw1`、`YiVALeaf`（`leaf-node`）、`YiVWVal`、`YiNLCeiling`、`YiCNTw1`、`YiLLLeafNeg`、`YiTUReduce`、`YiXUFirst`。
- 完全没读：`YiDXFold`、`YiDXValue`、`YiDXTest`，同批的 `YiKF`、`YiCA`。
- 转述引用：YiVA 的估计（ψ₀(Ω_Ω·Ω₂)）、YiRQ 的 "d ≥ 2 按大小"，来自 `Reports-2026-11-16/YiVA.md`、`YiRQ.md` 回报正文。YiVA 的封存附件没有读。
- 手册：`EBOHandbook` 4.2、4.6 节读了。Bedrock 性能手册的 C-9、C-10、S-1、S-3、C-24、Q-1、Q-23、H-6 只读了规则段。

没有改任何已有文件，没有提交。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：编译否定，第 1 层的值上界语义（前缀 YiUS，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路要把审核意见 "现行折叠在塔第 1 项前缀层号上会掉值" 做成编译过的否定。同批另两路与你互不导入。AGENTS："否定定理与条件定理的每个前提，给一个实例或说明为何可满足"；"归到已知的墙要逐条核机制"。

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

#### 本路的问题
`YiRQDom.refute` 说：只要一棵具体树（`Sᵈ.fd d (proj₁ (Ωt (h₁ d)))`，即塔第 1 项前缀下链步的那一次回灌）的一切下界读法 t 都严格低于 γ 链第 1 项，限制版链步 `TightDom d` 就不成立。审核意见缺的、YiTU 缺的，都是 "第 1 层（及以上）的树的值上界"：`readRW` 只对第 0 层；`GR.R` 是下界读法；YiVA 判断第 1 层只有一个槽位、Ω 结点同型，语法类不变量难写；但 `YiTFBound` 已在第 1 层写过两个语法类（`D0`、`S`）及其读法上界（`bD`、`bS`），可作起点。

#### 要做的（按序）
0. **选目标与工具**：(a) 目标取 `Refute d κ`：先 d = 2、κ = d 的读法（YiRQ 判断按大小可满足），再 d = 1、κ 为 `KT.κ*`（即 `Cand` 为假）；(b) 工具二选一或都试：语法类（照 `YiTFBound`，定义一个对 `drop`、`fall`、`start-form`、`leaf-branch` 封闭的树类，证它的读法上界），或第 1 层树侧值 `YiVWVal.val` 加 "下界读法对值可靠" 的引理（`GR.R k t x` ⇒ 参照值 ≤ `val k x`，再加值到项序的比较）。在临时文件里先编译最小一件。不成立就停下回报。
1. **证 `Refute`**（d = 2 起），得到 `¬ TightDom d`；再试 d = 1，得到 `Cand → ⊥`。
2. **往值走**（若有余力）：同步对象的输出严格低于里程碑。这要第 2 站闭项的上界（`YiTUReduce` 只到前两个链点）；做不到就写清还差哪一条。**若得到值层面的编译否定，停下交作者**（定义层面的信号）。
3. 说明每条否定否定的是什么（下界关系的陈述、链步的接口、还是实际对象的值），不多说。

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

