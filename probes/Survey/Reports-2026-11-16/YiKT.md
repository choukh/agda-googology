# 构造：塔第 1 项上的 LowKeep（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-16 15:24 至 15:58 |
| 工具调用 / agda 编译 (粗数) | 30 / 7 |
| token (usage 字段，按消息去重) | 输出 191014；新写入缓存的输入 1006231；读缓存的输入 5046862；其余输入 50 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `YiKT` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 1 件退出 0，禁用构造 0；新证据 KeepSpec′ 与结点行 node-above 编译；实际对象 d = 1 的一个槽位上新旧证据都为空（no-above、no-spec*，只否定证据域）；TightStep 1 在具体点上归约到 Cand（tight-at，两条前提未实填）；执行方判断 Cand 不成立、同步对象值低于 ψ₀(Ω_{Ω₂})，未编译 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b72/YiKT.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiKT 回报：构造，塔第 1 项上的 LowKeep（执行方 Fable 5.2）

#### 1. 判决

**对纲领与目标意味着什么。** 只新增一个第 4 层验收文件（读记号），树、折叠、合法性、比较表都没有改，没有新增序数值下界。本路在第 0 步停下：新证据设计出来并编译了，但在 d = 1 的实际对象上有一个槽位，新旧证据都为空（编译否定，只否定证据域）。`TightStep` 没有证，也没有被否定。

对决定性问题，我的判断是（未编译，见第 4 节）：塔第 1 项为前缀的层号上，紧的 κ 处的 LowKeep 在中间层 `h₁ d` 上不成立，机制是折叠 `kp` 的那一行加上最小比较表的退路行。这若属实，就是第 4 层逼出的定义改动，须作者定。

**各步到哪里。**
- **第 0 步：完成，结论是"不成立，停下"。**
  - 新证据 `KeepSpec′`：只改"树走链"一支。记号也走链时沿用原条件；记号保留时，要求槽位有读法 κ″ 满足 κ+1 ≤ κ″（`Above`）。
  - 对应的结点一行 `node-above` 已编译，一般层号、一般目标；只用链的第 1 项、底的前缀 `PrefixU` 和记号一侧的新引理 `above`，不用 `StepU′`。
  - 与三种被否定的证据域的差别：
    - 不用精确标签 `Lbl`，所以不撞 `no-lbl-hh`。
    - `block-frame` 判为只容 ν = 0 的结点 `hh d z`，在新证据下对一切 ν ≤ Ω₁、一切 κ 有居民（`spec-hh`）。
    - `TightStep` 自己的顶槽位对一切 κ 有居民（`spec-top`）。
    - `no-index-top` 挡的是嵌入的退路行（表缺项），不是结点行；新证据没有处理这一行。
  - d = 1 上不可满足：实际证据 `oᴱ` 下，`a₁ 2` 里有槽位 `p*`（孩子 `hh 1 z*` 内，下标层为第 0 层的 Ω 形状层号自己的下标槽位），朝 `h₁ 1` 折时走链；目标下标 ν = 1 时记号保留；第 0 层只有读法 0，所以 `Above` 为空，原条件也不成立（`no-spec*`）。
  - 对照：同一孩子里前缀 `tw 1` 叶子的下标槽位 `p₀`，分支类型同为 `Tr zero`、读法同为 0，却保留（`kp₀`）。
- **第 1 步：未走通。** 得到一条条件定理 `tight-at`：`TightStep 1` 连同底的 `OK`、`PrefixU … []` 推出具体命题 `Cand`，即一棵 ℕ 极限树承载共尾度 Ω₁ 的参照 ψ₁(Ω_{Ω₁})。其中两条关系前提已实填（`hyp₁`、`hyp₂`）；`OK` 与 `PrefixU` 两条没有实填，所以 `tight-at` 的前提可满足性没有完全交代。`Cand` 未判定。
- **第 2 步：没有做。**

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 共尾 Ω_{κ+1} 的项 a，在 η ≥ Ω_{κ+1} 处 a ≤ a[η]（项序） | `above` | 编译定理 |
| "树走链、记号保留"的结点，槽位有不低于 κ+1 的读法时保持 | `Row′.node-above`、`node-at′` | 编译定理（条件是 `PrefixU` 与分支上的归纳假设） |
| Ω 形状朝自己下标层折，顶槽位对一切 κ 有新证据 | `spec-top` | 编译定理 |
| `hh d z` 的孩子槽位，ν ≤ Ω₁ 时对一切 κ 有新证据 | `spec-hh`、`spec-hh₁` | 编译定理 |
| 实际证据下 `p*` 走链、`p₀` 保留 | `kp*`、`kp₀` | 有限测试（d = 1 的一个点，按定义计算） |
| `p*` 上新旧证据都为空（κ = 0，ν = 1） | `no-above`、`no-spec*` | 编译否定（只否定证据域） |
| 候选点上结论的参照共尾度是 Ω₁ | `goal-term`、`goal-cof` | 编译（`refl`） |
| 候选点上回灌出来的树是 ℕ 极限 | `feed-lim` | 有限测试 |
| 候选点上 `TightStep 1` 的两条关系前提成立 | `hyp₁`、`hyp₂` | 编译定理 |
| `TightStep 1` 加底的两条前提推出 `Cand` | `tight-at` | 编译条件定理（`OK`、`PrefixU` 未实填） |
| `Cand` 是否成立 | — | 未判定 |
| `p*` 处结点的折叠值严格低于记号一侧的值 | 第 4 节 | 判断 |
| 朝 `h₁ 1` 的折叠值都低于 ψ₁(Ω_{Ω₁})；同步对象的值低于 ψ₀(Ω_{Ω₂}) | 第 4 节 | 判断（把握低于上一条） |
| `TightStep d` 对一般 d | — | 未做 |

#### 2. 文件表

| 文件 | 物理行 | 代码行（非空） | 冷编 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiKTSlot.lagda.md` | 273 | 187 | 删自身接口后 6G 冷编，退出 0；日志只有本模块一行 `Checking`；最大驻留约 1.55G，约 17 秒 |

- 检索禁用构造、本机路径、`Funext`：均为 0。
- 文首 5 行。文首标"读记号"，没有跑 importclosure。
- 临时文件 `KT0.agda` 到 `KT3.agda` 及日志在 `<实验目录>/work/YiKT`，四个都退出 0。
- 全程没有 251，没有超时。

#### 3. 定理表（文件均为 `YiKTSlot`）

| 名字 | 逐字的陈述 | 白话 | 档 |
|---|---|---|---|
| `above` | `∀ a {κ η} → cof a ≡ cΩ κ → E.Ωs κ ≤ᵀ η → a ≤ᵀ fsT a η` | 把共尾 Ω_{κ+1} 的项在不低于 Ω_{κ+1} 处取基本列，项序上不降 | 编译 |
| `Above` | `Above ℓ p κ = Σ E.T λ κ″ → GR.Nu ℓ p κ″ × (E.sucT κ ≤ᵀ κ″)` | 槽位有不低于 κ+1 的读法 | 定义 |
| `KeepSpec′` | `KeepSpec′ ℓ j ν p κ nothing = (E.cmpᵀ (E.sucT κ) ν ≡ gt) ⊎ Above ℓ p κ`；`KeepSpec′ ℓ j ν p κ (just K) = KeepSpec ℓ j ν p κ (just K)` | 新证据，只改走链一支 | 定义 |
| `Row′.node-above` | `PrefixU B t → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → cof a ≡ cΩ κ → Above ℓ p κ → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ fsT a η) ∷ []) (proj₁ (F (g c)))) → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (node⁺ nothing (λ c → F (g c)) (feed ℓ o r B p g)))`（模块参数 `ℓ j o r B w ν t β`，`F x = ψ ℓ o r B j w β x`） | 记号保留、树走链时，由链的第 1 项加向下封闭得到保持 | 编译 |
| `Row′.node-at′` | 同 `YiGTNode.Core.node-at`，前面多一个 `PrefixU B t`，最后的证据换成 `KeepSpec′ ℓ j ν p κ K` | 三种情形合成一行 | 编译 |
| `spec-top` | `∀ k h (o : Ok (nd (sΩ k) h)) ν → GR.Rd k ν → ∀ κ → KeepSpec′ (nd (sΩ k) h) k ν (inj₁ (inj₁ tt)) κ (kp (nd (sΩ k) h) o (inj₁ (inj₁ tt)) (ink self))` | 顶槽位朝自己的下标层：目标下标自己就是槽位读法 | 编译 |
| `rd-pre` | `∀ X → GR.Rd (tw 1 ⊕ X) Ω₁`（`Ω₁ = E.Ωt (𝟏 ∷ [])`） | 以 `tw 1` 为前缀的层号都读作 Ω₁ | 编译 |
| `spec-child` | `(h : ⊤ → L) (o : Ok (nd sS h)) {j : L} (w : j ≤ nd sS h) → NotSelf w → ∀ ν ρ → GR.Rd (h tt) ρ → ν ≤ᵀ ρ → ∀ κ → KeepSpec′ (nd sS h) j ν (inj₂ (tt , inj₁ tt)) κ (kp (nd sS h) o (inj₂ (tt , inj₁ tt)) w)` | 后继形状的孩子槽位：孩子层号有不低于 ν 的读法即可 | 编译 |
| `spec-hh` | `∀ d z (o : Ok (hh d z)) (w : h₁ d ≤ hh d z) ν → ν ≤ᵀ Ω₁ → ∀ κ → KeepSpec′ (hh d z) (h₁ d) ν (inj₂ (tt , inj₁ tt)) κ (kp (hh d z) o (inj₂ (tt , inj₁ tt)) w)` | `block-frame` 的结点在新证据下有居民 | 编译 |
| `kp*` / `kp₀` | `IsNothing (kp (a₁ (suc one)) (proj₂ oᴱ (suc one)) p* (ink self))` / `IsJust (kp (a₁ (suc one)) (proj₂ oᴱ (suc one)) p₀ (ink self))`；`p* = inj₂ (z* , inj₂ (inj₂ (tt , inj₂ (inj₁ (inj₁ tt)))))`，`z* = proj₁ (Ωt (h₁ one))` | 实际证据下一个走链、一个保留 | 有限测试 |
| `no-above` | `∀ κ → Above (a₁ (suc one)) p* κ → ⊥` | `p*` 没有更高读法（经 `YiCNTw1.rd-zero`） | 编译否定 |
| `no-spec*` | `KeepSpec′ (a₁ (suc one)) (h₁ one) (𝟏 ∷ []) p* [] (kp (a₁ (suc one)) (proj₂ oᴱ (suc one)) p* (ink self)) → ⊥` | 新证据在 `p*`、κ = 0、ν = 1 处为空；原 `KeepSpec` 是它的第一支，同样为空 | 编译否定（只否定证据域） |
| `goal-cof` | `cof (E.γT ([] ++ a*) κ* 1) ≡ cΩ []`（`κ* = 𝟏 ∷ []`，`a* = E.Ωt (E.Ωt (𝟏 ∷ 𝟏 ∷ []))`） | 候选点上结论的参照 ψ₁(Ω_{Ω₁}) 共尾度是 Ω₁ | 编译 |
| `feed-lim` | `IsLim (feed (a₁ (suc one)) (proj₂ oᴱ (suc one)) (rbᶻ (a₁ (suc one))) (D.dn Bᴱ (suc one)) (inj₁ (inj₁ tt)) g* z*)` | 回灌出来的树顶构造子是 `lim` | 有限测试 |
| `hyp₁` / `hyp₂` | `GR.R (h₁ one) (E.Ωt κ*) z*` / `GR.R (a₁ (suc one)) (fsT a* (E.Ωt κ*)) (g* z*)` | 候选点上两条关系前提成立 | 编译 |
| `tight-at` | `TightStep one → OK (D.dn Bᴱ (suc one)) → PrefixU (D.dn Bᴱ (suc one)) [] → Cand`；`Cand = GR.R (h₁ one) (E.ψ κ* (E.Ωt (E.Ωt κ*)) ∷ []) (feed (a₁ (suc one)) (proj₂ oᴱ (suc one)) (rbᶻ (a₁ (suc one))) (D.dn Bᴱ (suc one)) (inj₁ (inj₁ tt)) g* z*)` | `TightStep 1` 在一个具体点上的结论 | 编译条件定理 |

#### 4. 第一个障碍

**引理：`Cand`**（陈述见上表），即 `TightStep 1` 在 t = 0、κ = 1、a = Ω_{Ω₂}、n = 0、z = `z*`（第 `h₁ 1` 层的 Ω 树）、g = Ω 树的实际分支处的结论。
- 它是 `YiSUIface.StepU′ (a₁ 2)` 在顶槽位的实例，也就是"塔第 1 项上的 LowKeep"一般形式的实例。
- 它内部要用的，是孩子层号里 `p*` 型结点朝 `h₁ 1` 的保持；那一处现有证据与新证据都为空（`no-spec*`）。

**是数学上挡住**，没有工程问题。

**判断一（未编译）：`Cand` 不成立。**
- 机制：层号读回 `↑` 把第 `h₁ d` 层树里的 Ω 结点变成 Ω 形状层号，它的下标层低于 d。层号证据让这个下标层经前缀 `tw 1` 的指定孩子 `suc d` 到达孩子，`psh` 于是把下标槽位推成 `tw 1` 叶子的孩子槽位；目标路径也经 `inc (suc d)`，落在 `kp (nd (sΩ k) h) _ (inj₂ _) (inc _ _) = nothing` 一行。
- 后果：`p*` 处的链在第 0 层，结点的值是可数多个第 1 层值的上确界；记号一侧 ψ₁(t ++ a′)（a′ 共尾 Ω₁）共尾度是 Ω₁。所以树在这一处严格更低，这一步与底的大小无关。
- 这一步依赖 `GR.R` 对值可靠，而这没有编译的定理；带 `mc` 的关系在非标准形项上是否可靠我没有核。所以 `Cand` 只能写"未判定"。
- 配对否定一路可以直接用这个候选点。要把它做成编译否定，需要第 1 层折叠值的上界语义；我试过用"T 低于某个阈值"作不变量，它在保留的 Ω 结点上不成立，没有做下去。

**判断二（未编译，把握低于判断一）：同步对象的值低于 ψ₀(Ω_{Ω₂})。**
- 最小表下，`tw 1` 朝 `h₁ 1` 的退路行只加一个可数项，再加上面那一行，任何朝 `h₁ 1` 的折叠都把共尾 Ω₁ 的对角换成可数的闭包点，值低于 ψ₁(Ω_{Ω₁})。
- 于是第 1 层的链越不过 ψ₁(Ω_{Ω₁})，而 ψ₀(Ω_{Ω₂}) 需要这条链走到 ψ₁(Ω_{ψ₁(Ω_{Ω₁})}) 以上。
- 若属实，`FirstMissing`（ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})）与 `Tail` 在现行折叠下为假；到 `Kᴱ′ 2` 的这条归约（经同步对象）走不通。`Kᴱ′ 2` 本身我没有分析到能下判断。
- 没有核实的环节：继承底 `Bᴱ` 的具体内容；d ≥ 2 的情形；朝第 0 层折叠时"先闭包"可能使第 0 层的值偏高，我只粗略估过它不足以越过上述界。
- 旁证只有一条：`YiXUFirst` 文首写明"不判定 ψ₀(Ω_{Ω₂})"。它不构成依据。

**要越过它涉及的定义（判断，交作者）：**
- `kp` 的"Ω 形状、槽位在孩子里、路径经 `inc`"一行。要在槽位孩子与路径孩子可比时继续，就需要孩子下标上的比较证据；这要先对照 `obs→dec` 一族的前提。
- `Ωt` 用层号自己的下标槽位。`p₀` 的保留说明同一分支类型换一个槽位就不走链。
- 最小表在 `tw 1` 上的退路行。

这三处我都没有动，也没有试改。

#### 5. 偏离与事故

- **30 分钟时限**：没有计时。第一个编译的文件 `KT0.agda` 之前读定义并做了很长的纸面分析，很可能超过 30 分钟。
- **超出简报**：加了候选点一节（`hyp₁`、`hyp₂`、`tight-at`、`feed-lim`）和 `spec-top`、`spec-hh`。
- **没有做**：第 1 步的一般 d、第 2 步；`OK (D.dn Bᴱ 2)` 与 `PrefixU (D.dn Bᴱ 2) []` 的实填；d ≥ 2 上的同类测试。
- **导入**：导入了 `YiTLReduce`（`hh`、`NotSelf`、`not-self`、`noΩ-h₁`、`TightStep`）与 `YiCNTw1.rd-zero`、`YiLLCheck.read0`、`YiGLDom`、`YiNLCtx`。没有导入也没有读同批 `YiTF`、`YiMG`、`YiTA`、`YiRR` 的文件。
- **没有读、只凭转述或检索引用的**：
  - Bedrock 性能手册原文没有读，只读了 `EBOHandbook` 4.2、4.6 节；本路没有遇到性能问题。
  - `YiXP*`、`YiEL*`、`YiGL*` 的正文没有读，只读了 YiXP、YiTL 的回报、`YiGLDom` 的域定义、`YiNLCtx` 的一段。
  - `YiGTEmb`、`YiGTUp`、`YiGTSelf`、`YiSYSmall`、`YiKSDesc`、`YiFRStep`、`YiGIInst`（`baseᴱ`、`pre`）没有读。
  - `oᴱ` 给出的路径形状，是照 `Ok-tw`、`OkO↑` 的构造推想的，只在 `p*`、`p₀` 两个槽位上由 `kp*`、`kp₀` 验证过。
  - 第 4 节的值分析全部是纸面的。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：构造，塔第 1 项上的 LowKeep（前缀 YiKT，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。本路选项原文 "构造：塔第 1 项上的 LowKeep (Recommended)"。配对否定一路 `YiTF` 对同一问题找反例，你们共用的陈述是 `YiTLReduce.TightStep`、`Gvᴱ.KeepOut`/`KeepFeed` 与（若你定义了）塔第 1 项上的 LowKeep 陈述；不导入彼此的文件。

#### 作者的决定与背景（2026-11-16）
- 作者定：主线停逐项，改攻整体引理（读回域上的 Leaf 加 LowKeep）；参照只用记号关系 M。第七十二批选项原文："构造：塔第 1 项上的 LowKeep (Recommended), 配对否定：找塔第 1 项上的反例 (Recommended), 合流两个关系族 (Recommended), 记号侧：截断加法与部分和链点"；摆脱侧 "右边放宽的底关系 (Recommended)"。同批五路：构造 `YiKT`（Fable 5.2）、配对否定 `YiTF`、合流 `YiMG`、截断加法 `YiTA`、摆脱侧 `YiRR`（Opus 5.5），互不导入。
- **第七十一批的结果**（主审 8G 冷编复核过，读陈述；回报在 `probes/Survey/Reports-2026-11-16/`）：
  - `YiXPExact.lowKeepAt-noΩ : ∀ ℓ → NoΩ ℓ → LowKeepAtˣ ℓ`、`lowKeepˣ`：精确标签 `YiGLFrame.Lbl` 下 LowKeep 对一切不含 Ω 形状的层号无条件成立；保持引理族的一般各行不用槽位标签的性质（`YiXPRel`、`YiXPRows`、`YiXPFold` 对抽象 `Lab` 参数化），框架只靠 `uniq`、`below`、`YiXPFrame.lbl-path`。`YiXPNeg.no-index-tree-tw1ˣ`：折叠 `YiRWFold.kp` 对 "Ω 形状、槽位在孩子里、路径经 `inc`" 恒为 `nothing`（走链），记号一侧在孩子里更深的槽位处保留，于是逐槽位证据域 `IndexTree` 在塔第 1 项上为空（只否定证据域）。
  - `YiELLim.limAt : ∀ u → cof u ≡ cω → LimAt u`；`YiELZero.no-all`（带下界证据 `M⁰` 的第 0 层树不都有精确标签）→ 第 0 层分支前提要换精确读回 `Ex⁰ η d = Lbl (↑ zero d) η`（`ex→M⁰`、`ex-lower`、`child-lbl`）；`YiELOmega.Lblᵒ`（下标层为第 0 层的 Ω 形状层号有精确标签，带 `CofΩ` 字段）、`uniqᵒ`、`belowᵒ`（要 `PosOk`）、关系族 `Rᵉ`（第 0 层分支前提用 `Ex⁰`）、`topᵉ`、`lbl-layer`；`YiELChain.ex-next`、`ex-add`（要 `HdLe p s`）。`Rˣ` 与 `Rᵉ` 之间没有映射。
  - `YiWBNeg.Neg.no-next`、`no-base`：只放宽左边的底关系（含最宽的 `Ω≼`）给不出两条实际链前缀 2 的底前提；`val-left-right`：值序上成立，用的是右边一个第 1 层槽位结点的**非首分支**（该槽位层号自己的 Ω 树）。
  - `YiTLReduce`：同步对象（`kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`）各孩子层号 `a₁ c` 上 Leaf 无前提（`leaf-a₁`）；`tail-fromᴱ`、`k2′-from-keep : (∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → Kᴱ′ 2`（`KeepOut c = ∀ {s} → GR.R (a c) s (proj₁ (Ωt (a c))) → (h : E.HC (E.ψ [] s ∷ [])) → Rt h ≼ K.readRW (proj₁ (out c))`）；`no-lbl-a₁`（这些层号没有 `Lbl`）；第一个挡住的引理 `TightStep d`（顶槽位上紧的链的一步，`StepU′ (a₁ (suc d))` 的实例，陈述已编译），三种现有证据在那里都为空（`no-index-top`、`block-frame`、`no-lbl-hh`）。纸面方向（YiTL 判断）：把框架换成只在实际推导的 κ 处检查，量化域限在读回域的推导上（前缀读空，退路行只承载平凡参照）。
- **决定性问题**（主审判断）：塔第 1 项（及以它为前缀的层号）上的 LowKeep 成不成立。成立要一种新证据；不成立就要改折叠的那一行（第 4 层逼出的定义改动，交作者）。
- 其他已编译的事实：`YiVNIdx.Gen.no-value-index-mono≈`（下标的树侧值序不能作下标单调的前提）；`YiFOValue.fallback-prefix`（退路保留此前折叠的值）；`YiXUFirst.first-ceiling`（干净对象第一支 ≤ ψ₀(Ω₄)）；`YiORBound.original-neg`（封闭关系下原行仍不过判据）。

#### 要做的（按序）
0. **设计新证据**（最小检查）：写出一种证据形式，处理 "树走链、记号保留" 的结点（例如只在实际推导到的 κ 处检查框架，量化域限在读回域，前缀读空；或别的你认为对的设计），说明它与三种已被否定的证据域（`IndexTree`、下界读法的 `NodeFrame`、精确标签 `Lbl`）差在哪里、为什么不撞 `no-index-top`、`block-frame`、`no-lbl-hh`。在 d = 1（`a₁ (suc (suc zero))`）上确认可满足。不成立就停下回报。
1. **证 `TightStep d`**：先对 d = 1，再对一切 d（或对实际链点）。
2. **接上**：由它得到 `Kit (a₁ (suc d))` 的相应分量，进而 `KeepOut`、`KeepFeed`，经 `k2′-from-keep` 得 `Kᴱ′ 2`（第 3 站对位下界，值是 ψ₀(Ω_{Ω_Ω})——若成，就是主线值前沿的大步移动）。挡住就交第一个挡住的引理（在对象上精确陈述），说明是数学上还是工程上挡住；并说明它是否是 "塔第 1 项上的 LowKeep" 的一般形式的实例。

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

