# 出口条件与核心证明的耦合（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 07:15 至 07:45 |
| 工具调用 / agda 编译 (粗数) | 66 / 9 |
| token (usage 字段，按消息去重) | 输出 172457；新写入缓存的输入 421740；读缓存的输入 9767285；其余输入 100 |
| 写过的仓库文件 | `YiXCEnd.lagda.md`, `YiXCVar.lagda.md` |
| 文件前缀 | `YiXC` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0（验收文件）；出口条件恰好就是向下封闭步可以消去（toᴴ、exᴺ、ofᴴ、elim）；终点不再要出口条件（ebo-endᶜᵁ），但多出第 0 层的换基行与闭合行两条前提；闭合行必要（close-needed），标准形时成立（close←nf），一致陈述的标准形条件被否定（¬closeNF-all），局部数据推不出（¬close-local、¬push-local） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b81/YiXC.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### 回报（YiXC，Opus 5.5）

##### 1. 判决

**对纲领与目标意味着什么。** 这一路只做了验收一侧（第 4 层）的工作。树、折叠、合法性一行没改，对"树自足"没有贡献，强度也没有提升，终点仍是条件定理。

按翻译账算：新增的两条第 0 层行都写成 ψ₀ 参照的形式，是读记号的验收行，不是树侧的定义。它做到的是：原来出口条件挂在 `folded n` 这个证明项上，依赖各前提证明项的内容（审查 F 路 G5）；现在它被收成核心证明里的**一行**，即第 0 层目标上的向下封闭行（闭合行）。这一行是只关于类型的命题，并且已证明它是必要的。

**做法与关键事实（编译）。**
- 在第 0 层，"推导连同 `Exᴴ`" = 把 NF、Ctbl 放进 mc 的变体 `Mᴺ`，两者一一对应。它又可以消去 mc，成为 `YiKVRel.M⁰` 的推导，下标与树都不变（`elim`）。也就是说，出口条件恰好就是"mc 可以消去"。
- 于是把第 0 层目标单独做一次归纳（`low⁰`），输出直接用不带 mc 的关系，出口就是无条件的。各行的情况：
  - 后继步：不再需要前缀步上的标准形。
  - 结点：在第 0 层目标上只有走链一格，不用 `NodeMis`。
  - 嵌入各行：递归即可，不需要新前提。
  - 剩下的只有两格：换基行的第 0 层目标版 `RebRow⁰`，和闭合行 `CloseRow⁰`。

**各步完成情况。**
- **第 0 步 (A) 完成。** 变体、一一对应、无条件出口、消去 mc 都已编译。在变体上核了已有的封闭引理：
  - `closeᴿ`（带证据）与 `weakenᴿ` 照搬成立。
  - `m-add` 的前缀步不能照搬（`¬push-local`）。
  - 核心证明的闭合步 `closeᴿ j (app≤ν κ K le)` 不能照搬（`¬close-local`）。
  - `dom-top` 只给了判断，没有编译。
- **第 0 步 (B) 没有按原样做**（"规范推导满足 `Exᴴ`"），改成了上面的结构归约。理由见第 4 节。
- **第 1 步完成。** 新终点 `ebo-endᶜ` / `ebo-endᶜᵁ` 不含出口条件。但它的前提并不是只剩原来那几条核心前提：多了两条第 0 层的行。
- **第 2 步：** 交付如下。

**前提清单（`ebo-endᶜᵁ`）。**
- 域 `𝒟 : Domˢ`
- `UpMis`（或 `SelfRow`）
- `NodeMis`
- `RebRow`
- `RebRow⁰`（新）
- `CloseRow⁰`（新）
- `RootBd`
- `RootIn`

不再有 `∀ n → H.Exᴴ (folded n)`。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 出口条件收成两条第 0 层的行，终点不再要它 | `YiXCEnd.Zero.Main⁰.ebo-endᶜ`、`ebo-endᶜᵁ` | 编译定理（条件） |
| 闭合行必要：第 0 层目标陈述 `Low⁰` 推出它；反方向是 `low⁰-all` | `close-needed`、`low⁰-all` | 编译定理 |
| 两个参照都是标准形时闭合行成立 | `close←nf` | 编译定理 |
| 这个标准形充分条件对一切上下文一致陈述时不成立（上下文 K = 1+ω，层号 0） | `¬closeNF-all` | 编译定理（否定，读作量化域太宽） |
| 现参照 ψ₀(K+s) 是标准形、s、t 是标准形、t 可数、s ≤ t，仍推不出 ψ₀(K+t) 是标准形 | `¬close-local` | 编译定理（否定） |
| 变体上前缀步：NFP p、NF s、NF t、Ctbl t、s ≤ t 推不出 NF (p ∷ t) | `¬push-local` | 编译定理（否定） |
| `CloseRow⁰`（值的形式）在全域上不成立 | — | 判断：把 `YiMXNote` 的 1+ω+1 <ᵀ ω 包进 ψ₀，项序上 ψ₀(1+ω+1) <ᵀ ψ₀(ω)，值却是 ω^{ω+1} 大于 ω^ω；未编译 |
| 塔上实际出现的闭合对（`dom-top` 的 `dc`、链点 `closeᴿ (Ω≤ψ …)` 经 Low 参数流入的 mc）连同上下文是否是标准形 | `folded⁰` 的推导 | 未查 |
| `RebRow⁰`、`CloseRow⁰` 实填 | — | 未做 |
| `dom-top` 在变体上：第 0 层的 `Dom` 只有空读法，mc 只是 [] ≤ [] | — | 判断，未编译 |
| 前提联合可满足 | `ebo-endᶜ` | 未知。两条新行在空域上各自成立（`close-none`、`rebrow⁰-none`），但 `RootIn` 在空域上不成立 |

##### 2. 文件表（代码行 = agda 块内非空行；两件删接口后一起冷编，6G，退出 0，日志只有这两件的 `Checking` 行）

| 文件 | 代码行 | 冷编 |
|---|---|---|
| `<仓库>/probes/OCF/Lean/YiXCVar.lagda.md` | 118 | 0 |
| `<仓库>/probes/OCF/Lean/YiXCEnd.lagda.md` | 190 | 0 |

自查结果：
- 禁用构造（`postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、`--irrelevant-projections`）为 0，本机路径为 0。
- 两件都是读记号的验收文件，不需要查导入闭包。
- 临时文件 `<实验目录>/work/YiXC/XC0.agda` 是第 0 步的草稿，编译退出 0，内容已并入 `YiXCVar`。

##### 3. 定理表（全部为编译定理）

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `toᴴ` / `exᴺ` / `ofᴴ` | `∀ {s x} → Mᴺ s x → H.M⁰ s x` / `∀ {s x} (m : Mᴺ s x) → H.Exᴴ (toᴴ m)` / `∀ {s x} (m : H.M⁰ s x) → H.Exᴴ m → Mᴺ s x` | 变体与"推导连同出口条件"一一对应 | YiXCVar |
| `exitᴺ` | `∀ {s x} → Mᴺ s x → (h : HC s) → Rt h ≼ readRW x` | 变体上出口无条件 | YiXCVar |
| `ctbl≤` | `∀ {s t} → NF s → Ctbl t → s ≤ᵀ t → Ctbl s` | 标准形沿项序向下保持可数 | YiXCVar |
| `down⁰` | `∀ {s t} {v : Tr zero} → NF s → NF t → Ctbl t → s ≤ᵀ t → K.M⁰ t v → K.M⁰ s v` | 标准形对上，不带 mc 的第 0 层关系向下封闭 | YiXCVar |
| `elim` / `elimᴴ` | `∀ {s x} → Mᴺ s x → K.M⁰ s x` / `∀ {s x} (m : H.M⁰ s x) → H.Exᴴ m → K.M⁰ s x` | 带出口条件的推导可以消去 mc | YiXCVar |
| `¬push-local` | `(∀ {p s t} → NFP p → NF s → NF t → Ctbl t → s ≤ᵀ t → NF (p ∷ t)) → ⊥` | 前缀步不保持标准形（反例：1 加在 ω 前） | YiXCVar |
| `¬close-local` | `(∀ {K s t} → NF (ψ [] (K ++ s) ∷ []) → NF s → NF t → Ctbl t → s ≤ᵀ t → NF (ψ [] (K ++ t) ∷ [])) → ⊥` | 闭合步的标准形不由局部数据决定（反例：K = 0，s = 0，t = ψ₀(Ω₁)） | YiXCVar |
| `Zero.Main⁰.ebo-endᶜ` | 模块参数 `𝒟 nm sr rr rr⁰ cl`，再加 `(rb : RootBd) (ri : End.RootIn 𝒟)`；结论 `toL ET.EBO-tree′ ≼ K.readRW EBOᴮ` | 不要出口条件的终点下界（条件） | YiXCEnd |
| `ebo-endᶜᵁ` | `(𝒟 : Domˢ) → UpMis → Sys.NodeMis 𝒟 → Sys.RebRow 𝒟 → Zero.RebRow⁰ 𝒟 → Zero.CloseRow⁰ 𝒟 → RootBd → End.RootIn 𝒟 → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ` | 同上，自身行换成 `UpMis` | YiXCEnd |
| `Zero.Main⁰.folded⁰` | `∀ n → K.M⁰ (E.ψ [] (E.Ωt (Keel⁻.kt keelᴱ n)) ∷ []) (twcᴮ n)` | 塔各项朝第 0 层的推导，不带 mc | YiXCEnd |
| `Zero.Main⁰.low⁰-all` / `Zero.close-needed` | `Low⁰` / `Low⁰ → CloseRow⁰` | 闭合行与第 0 层目标陈述等价（在其余各行之下） | YiXCEnd |
| `Zero.close←nf` | `CloseNF⁰ → CloseRow⁰` | 参照对是标准形时闭合行成立 | YiXCEnd |
| `Zero.rebrow⁰←ᴱ` | `RebRowᴱ → RebRow⁰` | `RebRow⁰` 由"目标第 0 层的 `RebRow` 连同 `Exᴴ`"给出 | YiXCEnd |
| `¬closeNF-all` | `Zero.CloseNF⁰ allˢ → ⊥` | 全域上的标准形充分条件不成立 | YiXCEnd |
| `close-none` / `rebrow⁰-none` | `Zero.CloseRow⁰ noneˢ` / `Zero.RebRow⁰ noneˢ` | 两条新行各自可满足（空域） | YiXCEnd |

几个定义的原文：
- `Z (o , r , B) K t x = (w : zero ≤ a) (β : Tr⁺ zero) → K.M⁰ (E.ψ [] K ∷ []) (proj₁ β) → K.M⁰ (E.ψ [] (K ++ t) ∷ []) (proj₁ (BS.ψ a o r B zero w β x))`
- `CloseRow⁰ = ∀ {a} (o : Ok a) (r : Rb a) (B : Base a) → Good a r → ∀ K → SlotBd (o , r , B) K → ∀ {s t x} → s ≤ᵀ t → GR.R a t x → Dm (o , r , B) x → Z (o , r , B) K t x → Z (o , r , B) K s x`
- `RebRow⁰`：就是 `YiSOLow.Sys.RebRow` 取 j = 0、κ = []，假设与结论都换成 `K.M⁰`。

##### 4. 第一个障碍

障碍是 `YiXCEnd.Zero.CloseRow⁰`，即第 0 层目标上的闭合行：从输入推导里一个 mc 结点（s ≤ t）上 t 的那一份，得出 s 的那一份。

- 它在值上要的是：参照对 ψ₀(K++s) ≤ ψ₀(K++t) 上项序推出值序。标准形时由 `mono≤ⁿ` 给出（`close←nf`）。
- 它是必要的（`close-needed`），换写法绕不开。
- 标准形充分条件一致陈述时有编译的否定（`¬closeNF-all`，上下文不受约束）；局部数据也推不出（`¬close-local`）。

所以：一致的写法在数学上被挡住（编译）；限制到读回域上的写法是开放的，属于量化域的设计问题，未知是否被挡。要约束的是上下文 K，以及输入推导里实际被消费的 mc 对。

判断（未编译）：这些 mc 对来自 `dom-top` 的 `dc`（`rdown`），以及核心证明自己的链点 `Node.chain` 里的 `closeᴿ (Ω≤ψ …)`、槽位层的闭合像，后两者经 Low 参数由 `dom-top` 的 `dC`/`raiseR` 流入输入推导。这是"对任意下标量化太宽"第六次以同一形状出现，应当并入 YiQV 的统一量化域检验，不应单开一路。

##### 5. 偏离与事故；只凭转述引用的东西

**偏离。**
- (B) 没有按原样证，改成了结构归约。理由：规范推导里的 mc 有一部分由核心证明自己的链点经 Low 参数产生，要证 `Exᴴ` 就得跟踪同一个量化域问题（判断）。
- 第 1 步的前提不是"只剩核心那几条"：出口条件换成了 `RebRow⁰` 与 `CloseRow⁰` 两条。`RebRow⁰` 与主线 `YiMXEnd.LowKeepᴱ` 同形，即连同 `Exᴴ` 返回。
- `inv-suc`、`sem→M⁰` 从 `YiKCSem` 照抄，文首已写明来源。

**事故。**
- 第一次编译套了 `/usr/bin/time -l`，因沙箱禁 `sysctl`，包装命令退出 1，去掉包装后通过。所以没有测峰值内存（各次编译只用了几秒到十几秒）。
- 第一个文件超过了 30 分钟时限，读定义用时较长，没有精确计时。
- 期间有一次 42：解析错误，块内顶格写了定义，已改正。

**没读、只凭简报或审查转述引用的：**
- `YiXTIface.stuck`、`YiSDRead.CellRaise`、`YiWCWire.StepW`、`YiLLLeafNeg.noLeafOk`、`YiQDFold`、`YiUFDom`、`YiBCCover`、`YiBAEbo`、`YiSDRead` 的读回形式都没读。
- `raiseR` 只看了签名与分派行，"Low 参数经 `raiseR` 进入输入推导"一句依据的是 `dom-top` 的定义体与审查 F 路 G5 的说法。
- 同批 YiQV、YiMI、YiAB 的文件没读。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：出口条件与核心证明的耦合（前缀 YiXC，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。同批另三路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者要求（原文）："更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。作者选项原文："统一收量化域的检验 (Recommended), 合并同类接口 (Recommended), 出口条件与核心证明的耦合, 辅助系统的底取目标层起点（改候选定义）"。前缀 `YiQV`（Fable 5.2）、`YiMI`（Opus 5.5）、`YiXC`（Opus 5.5）、`YiAB`（Fable 5.2），互不导入。**主线定义不动**；换基折叠 `YiBSFold` 是候选。
- **现状（主审复核过，都在 `probes/OCF/Lean/`）**：换基候选上的终点条件定理有两版：`YiWREnd.Wire.ebo-endˢ`（前提 `LowSlot` 与出口条件；两个具体不变式下 `LowSlot` 被审查 F 路编译否定，加强不变式后接线合上，见留档 `probes/Survey/Reports-2026-11-16/AuditF.md` 与附件 `attachments/AuditF-*.txt`），以及不经原接线、带域的 `YiSOEnd.End.ebo-endᴬ`、`YiSOTw1.EndU.ebo-endᵁ`（前提：域 `Domˢ`、`NodeMis`、`RebRow`、`RootBd`、`RootIn`、`UpMis`，加出口条件）。`YiSOLow.Sys.Main.lowAll`、`YiSOUp.UpAll.upAll`：多目标系统里保留判定与参照一致的格对一切层号一次归纳证出。
- **剩下的义务（判断：都出自量化域太宽，第四、五次同形出现）**：`YiSOLow.Sys.NodeMis`（树走链而参照保持 Ω 余尾：审查 F 路 FCross 那一格、`YiXTIface.stuck` 的情形；树保留而参照坍缩：读法允许取空时出现）、`YiSOUp.UpMis`（上折同类一格）、`YiSOLow.Sys.RebRow`（换基行：路由落在地板之上时替身加第 0 层尾项，域取全体时判断为假；`YiSDRead.CellRaise` 未走通）、`YiSOEnd.RootBd`（塔第 2 项起根状态每个槽位每个读法上的 Leaf；全域 Leaf 在 Ω 形状上有否定 `YiLLLeafNeg.noLeafOk`）、`YiWCWire` 的 `StepW`（链的步：上下文前缀可以超出链的上确界）。出口条件 `YiHCRel.Exᴴ` 要求推导里每个向下封闭步 `mc` 两边是标准形、较大一边可数，与核心证明里 `mc` 的用法耦合（审查 F 路 G5）。
- 可用的读回域工具：`YiGLDom`（`Dom`、`dom-top`、`leafᴰ`、`liftᴰ`、`dom-keel`；`rd-not-dom`）、`YiQDFold`（树的域 `KD`、`kd-dw`、`Ωt-in`/`Ωt-out`）、`YiUFDom.QDTw.Ωt-tw`、`YiBCCover`（证据在读回域上处处满）、`YiSDRead.sub-read`/`top-read`（读回形式）、`YiBAEbo.BelowE`（参照取 ψ_ν、条件 `KeepAt`）、`YiSOTw1.root-bd1`（塔第 1 项根状态无前提）。

#### 本路的问题
终点从关系推到值经出口 `YiHCRel.exitᴴ`，要求出口条件 `Exᴴ`（推导里每个 `mc` 两边是标准形 `NF`、较大一边可数 `Ctbl`）。审查 F 路判断：出口条件依赖核心证明里 `mc` 的用法（例如链步里的 `closeᴿ (Ω≤ψ …)`、调下标与调派发），两者不独立；YiSO 判断第 0 层目标的推导里 `mc` 只来自向下封闭一条（未编译）。主线 `YiMXEnd` 已把出口证据并进保持（`LowKeepᴱ`）。

#### 要做的（按序）
0. 先读 `YiHCRel`（`Mᴴ`、`Exᴴ`、`exitᴴ`）、`YiMXEnd`（`LowKeepᴱ`）、`YiWREnd`（`ExitCondition`）、`YiSOEnd`（`ebo-endᴬ` 的出口条件）。二选一或都试：(A) 写一个验收侧的关系变体，把 `NF`、`Ctbl` 放进向下封闭规则，核已有的封闭引理（`closeᴿ`、`weakenᴿ` 一类、`dom-top`）在变体上是否仍成立；(B) 证 "规范推导满足出口条件"：在核心证明会产生的推导形状上证 `Exᴴ`。临时文件编译类型。不成立就停下回报。
1. 对换基候选的终点条件定理（`YiSOEnd.End.ebo-endᴬ`），给出一个出口条件不再单独作前提的版本（前提只剩核心的那几条），或写清为什么做不到。
2. 交：所选做法、新的终点条件定理、前提清单。

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

