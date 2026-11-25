# 派发改型后的值关系族 (YiWay)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 07:45 至 08:36 |
| 工具调用 / agda 编译 (粗数) | 62 / 4 |
| token (usage 字段，按消息去重) | 输出 337317；新写入缓存的输入 1258849；读缓存的输入 17295786；其余输入 118 |
| 写过的仓库文件 | `YiWayAsk.lagda.md`, `YiWayBtbo.lagda.md`, `YiWayInto.lagda.md`, `YiWayOne.lagda.md`, `YiWayRel.lagda.md`, `YiWayStep.lagda.md` |
| 文件前缀 | `YiWay` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 派发改型后的值关系族一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 回归集在产出端的折叠上成立；ψ₀(Ω_Ω·2) 条件；被问到的位置带证据并保留，缺非零目标层的值下界；六件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的方针: "边重构边做, 只动值的前沿碰到的那块"; 你这一路是 **派发改型后的值关系族**: 保留带搬运的三套折叠共用, 先把回归集搬到产出端的折叠上, 再在那里重做卡住的单步比较, 朝 ψ₀(Ω_Ω·2). 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 背景 (事实)

- 产出端的折叠 (都在 `probes/OCF/Lean/`): `YiProdFold.lagda.md` (`module Prod (D) (E)`, 消费端 `Ψᵖ`, 产出端 `Φ`, 闭项 `TΛᵖ`, `T⁺ʷᵖ`, `Twᵖ`), `YiProdArith.lagda.md`, `YiProdTest.lagda.md` (卡住的那一对在一个坐标上保留: `marked`, `kept-here`, `node-kept`; `inner-all`). 派发结果是 `YiZipWay` 的 `Way′` (保留带搬运 `Mv`). 回报 `probes/Survey/Reports-2026-11-12/YiProd.md` 全读, 特别是 §5: `btbo-TΛ` 没搬过来, 原因是 `YiDlVRel` 依赖的 `YiNextValRel`, `YiNextValPath`, `YiNextValLgl` 的 `ΨNR`, `ΨnR`, `ΨNDnP`, `ΨnLglR`, `ΨNLglR`, `substR`, `cmpR` 都是对 `Way` 陈述的; 缺的类型 (未写, 执行方给的): `WR′`, `ΨNR′`, `ΨNDnP′`, `ΨNLglR′`, `ΨRᵖ`, `ΨLglRᵖ`, `ΦR`, `ΦLglR`; 估 220 到 270 行.
- 回归集 (都无前提): `YiDlVBtbo.btbo-TΛ`, `YiIntoTw3.T⁺ʷ≼TΛ`, 以及 `YiDlVOne.χ₁≼ʷ` (下界一路的起点).
- 卡住的单步比较: `YiDlVStep.lagda.md` 的 `Stepᴳʷ` 与条件定理 `T2≼ᴳʷ : Stepᴳʷ → GL.T2ᴸ ≼ NA.read W.T⁺ʷ` (ψ₀(Ω_Ω·2) 的带标签参照 `GL.T2ᴸ`, `GL.T2-label`). 在燃料搜索的折叠上它卡在被问到的位置源层号是 ℕ 极限而派发折叠 (`YiDlLost`); 产出端的折叠在那一对上保留.
- 已有的较高下界的办法: `YiSyncRel`, `YiSyncDiag`, `YiSyncFold`, `YiSyncTwo` (第 1 层关系 `_⊴⁺_` 的对角规则, 得 ψ₀(Ω_Ω+Ω₂)), `YiL1*` (第 1 层的 BTBO 下界).

#### 要交的, 分步; 每做成一步先交

1. **值关系族** (验收文件): 主线折叠 (或燃料搜索的折叠) 与产出端折叠之间的读回关系, 对 `Way′` 陈述 (上面那些类型, 或你认为更省的写法). 由它把 `btbo-TΛ` 搬到 `TΛᵖ` 上 (`D.BTBOᴵ ≼ NA.read TΛᵖ`), 并搬 `T⁺ʷ≼TΛ` 与 `χ₁≼ʷ` 的对应.
2. **卡住的那一步**: 在产出端的折叠上证 `Stepᴳʷ` 的对应 (或它的足够部分), 得到 ψ₀(Ω_Ω·2) 的带标签参照不高于读法 ψ₀(Ω_{Ω+1}) 的闭项 (以及 `TΛᵖ`). 做不过去时给出值停在哪里的编译事实, 或缺的引理的确切类型, 并说清是否与派发有关.

只要下界 (作者 2026-11-11 的原则). 下界从已闭合的最高锚点往上做.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽 (先按手册 §4.2). 没有编译的否定时只写 "未走通".

#### 先读什么

`AGENTS.md` (Agda 一节, 文字预算, 结论的写法); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5 与 §5.4; 上面列的 YiProd 文件全读; `YiZipWay`, `YiZipMove`, `YiZipSim` (检索 `Way′`, `Mv`, `run`, `Sim`, `mv-sim`); `YiDlVRel`, `YiDlVBtbo` 全读; `YiNextValRel`, `YiNextValPath`, `YiNextValLgl` 检索上面那些名字; `YiDlVStep`, `YiDlVOne`, `YiDlLost`. 查签名用检索, 大文件不要整篇读.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiWay` (模块名 `OCF.Lean.YiWay…`). 值关系与值定理放验收文件 (文首标 "验收文件"). 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞 (写入文件时也不要留洞), `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录. 搬运用的临时副本不要写进 `probes/`.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/way`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 25 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (回归集在产出端折叠上是否成立; ψ₀(Ω_Ω·2) 的下界是否证出).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法.
5. 第一个障碍: 精确到引理与位置, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1. 判决

第 1 步做完了，第 2 步只做到"归约到一条单步比较"（条件定理），单步本身未走通。

对目标意味着什么：
- **回归集在产出端的折叠上全部成立，都无前提。** 三条分别是：
  - `btbo-TΛᵖ : D.BTBOᴵ ≼ NA.read P.TΛᵖ`；
  - `T⁺ʷᵖ≼TΛᵖ`；
  - `χ₁≼ᵖ : S2.χ 1 ≼ NA.read T⁺ʷᵖ`（参照由 `S2.χ1-label` 验收为 ψ₀(Ω_Ω+Ω₁)）。
- **搬运的部件。** 搬运经值关系族 `YiWayRel`。它对 `Way′` 陈述，对一切派发 `Dp` 与证据来源 `E` 成立，YiProd 回报 §5 列的缺的类型都已写出。
- **ψ₀(Ω_Ω·2) 的下界没有证出。** 编译的只是条件定理 `T2≼ᴳᵖ : Stepᵖ → GL.T2ᴸ ≼ NA.read T⁺ʷᵖ`。
- **与派发的关系（编译事实）。** 新坐标 `ξaᵖ` 处的结点确实被 `T⁺ʷᵖ` 的值问到（`askedᵖ`）。旧派发卡住的那类位置（源层号是 ℕ 极限的 `pNᵖ`）在这里带证据 `refl`（`markedᵖ`），派发保留（`keptᵖ`）；不带证据时折叠（`lostᵖ`）。
- **剩下的缺口（判断）。** 至少在这一对上，缺的已经不是派发。缺的是：对层号非零的内层链给出值的下界的办法。

#### 2. 文件表

全部在 `probes/OCF/Lean/`，都是验收文件。每个文件都删掉自己的 `.agdai` 后冷编，日志里只有本模块一行 `Checking`。

| 文件 | 代码行 / 总行 | 冷编退出码 | 常驻内存峰值 |
|---|---|---|---|
| `YiWayRel.lagda.md` | 420 / 519 | 0 | 2.30 GB |
| `YiWayBtbo.lagda.md` | 62 / 88 | 0 | 1.72 GB |
| `YiWayInto.lagda.md` | 66 / 94 | 0 | 1.90 GB |
| `YiWayOne.lagda.md` | 226 / 311 | 0 | 1.77 GB |
| `YiWayStep.lagda.md` | 143 / 196 | 0 | 1.78 GB |
| `YiWayAsk.lagda.md` | 71 / 115 | 0 | 1.81 GB |

- 选项行都是 `--safe --without-K --lossy-unification`。
- 禁用构造与本机路径的检索为 0：postulate、洞、TERMINATING、NO_POSITIVITY、trustMe、irrelevant-projections、cubical、funext。

#### 3. 定理表

##### YiWayRel（关系族）

`ΨRᵖ`、`ΨLglRᵖ`、`ΦR`、`ΦLglR`、`chR`、`chLR` 在 `module WayRel (Dp : ∀ k K → Z.Ext′ k K) (E : Ev)` 内。全部是编译定理。

**`WR′`、`MvR`**（定义）
- 陈述：`WR′ m m′ {j′ = j′} (MF.keep s refl) (Z.keep′ s′ t) = PR m m′ s s′ × MvR (MF.lev m s) (NB.lev m′ s′) j′ t`；fold 对 fold 是 `⊤`，其余是 `⊥`。
- 白话：保留项对保留项。槽位要相关，搬运要保树的关系、合法性的关系、第一位置的路径。
- 另有 `mvR-eq : MvR u u′ u′ (Z.byEq refl)`。

**`ΨNR′`、`ΨNDnP′`、`ΨNLglR′`、`ΨsR`、`ΨsLglR`**
- 陈述：同 `ΨNR`、`ΨNDnP`、`ΨNLglR` 的形状，把 `NB.ΨN` 换成 `Z.ΨN′`，把 `WR` 换成 `WR′`。
- 白话：结点两行对 `Way′` 互模拟。

**`cmpRᵖ`**
- 陈述：`VRʷ V V′ → ∀ q q′ → PR k k′ q q′ → ∀ r r′ → PR k k′ r r′ → ∀ ε → WR′ (MF.lev k q) (NB.lev k′ q′) (MF.cmp V q r) (cmpe V′ q′ r′ ε)`
- 白话：在不含 Ω 结点的公共上界上，`cmpe` 对一切证据都与主线 `cmp` 相关。

**`ΨRᵖ`**
- 陈述：`∀ {m m′} → LR m m′ → ∀ {k k′} {V : MF.Lv k} {V′ : WL.Lw k′} → VRʷ V V′ → ∀ {Sb x x′} → XRᵖ m m′ k k′ {Sb} x x′ → ∀ {ξ ξ′} → RR k k′ ξ ξ′ → ∀ μ π → RR m m′ (MF.Ψ m V x ξ) (Ψᵖ m′ V′ Sb x′ ξ′ μ π)`
- 白话：消费端与主线互模拟，对一切标注。

**`ΨLglRᵖ`**
- 陈述：`… (d : RR k k′ ξ ξ′) {l l′} → LglR k k′ ξ ξ′ l l′ → LglR m m′ (MF.Ψ m V x ξ) (Ψᵖ m′ V′ Sb x′ ξ′ noM noP) (ML.Ψ-lgl m V x ξ l) (Ψᵖ-lgl m′ V′ Sb x′ ξ′ noM noP (lglA-no Sb ξ′ l′))`
- 白话：合法性证明的路径对应。只对不带标注的输入。

**`ΦR`、`ΦLglR`**
- 陈述：`… → XΦ m m′ k k′ x X → ∀ {ξ ξ′} → RR k k′ ξ ξ′ → RR m m′ (MF.Ψ m V x ξ) (Φ m′ V′ X ξ′)`；`ΦLglR` 是对应的 `LglR` 版本。
- 白话：产出端的自折叠与主线的 `self` 折叠对应。

**`chR`、`chLR`**
- 陈述：`RR k k′ (MF.chain k (λ η → MF.Ψ k V (MF.self k) η) n) (chT k′ V′ n)`，以及对应的 `LglR`（`ML.chain-lgl …` 对 `chLb k′ V′ n`）。
- 白话：链点相关。

##### YiWayBtbo（编译定理）

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `Tw2-formᵖ` | `P.Twᵖ 2 ≡ N.G.lim (NB.psum N.zero obsᵖ)` | 形状（`refl`） |
| `btbo-Twᵖ2` | `D.BTBOᴵ ≼ NA.read (P.Twᵖ 2)` | 塔第 2 项不低于 BTBO |
| `btbo-TΛᵖ` | `D.BTBOᴵ ≼ NA.read P.TΛᵖ` | 回归 1 |

##### YiWayInto（编译定理）

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `at-T⁺ʷᵖ` | `Ψ₀ (desc path₃ s₃) ≡ T⁺ʷᵖ` | 同一条 `path₃` 下降到达 `T⁺ʷᵖ`（`refl`） |
| `T⁺ʷᵖ≼Tw3` | `NA.read T⁺ʷᵖ ≼ NA.read (Twᵖ 3)` | |
| `T⁺ʷᵖ≼TΛᵖ` | `NA.read T⁺ʷᵖ ≼ NA.read TΛᵖ` | 回归 2 |

##### YiWayOne（编译定理）

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `topᵖ` | `∀ m {k} (V : Lw k) S x ξ μ π → Cp m G.top (Ψᵖ m V S x ξ μ π)` | `top` 是消费端一切值的第一位置 |
| `topΦ` | 同形，对 `Φ` | 对产出端同理 |
| `cpInd` | `Cp k a t → ∀ μ π → Σ (Mk S a) λ μ₀ → Σ (Pv a) λ π₀ → CpA S (a , μ₀ , π₀) t μ π` | 沿路径诱导出带标注的第一位置 |
| `btbo-gen` | `∀ S (x : Xm zero (tw 2) S) → D.BTBOᴵ ≼ NA.read (Ψᵖ zero V2 S x G.top noM noP)` | 根值下界对一切 `S`、`x` |
| `Ctx.ctx` | 对满足四条单步 `hz hs ht hl` 与 `hb` 的任意 `F : R → R`：`y ≼ b → ∀ ξ → b ≡ NA.read ξ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (F ξ)` | 上下文引理，对一族函数 |
| `ΩΩ+1ᵖ` | `L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read T⁺ʷᵖ` | |
| `χ₁≼ᵖ` | `S2.χ 1 ≼ NA.read T⁺ʷᵖ` | 回归 3 |

`ch1`、`pB-form`、`pM-form`、`term₁ᵖ`、`top-form` 是有限测试（`refl`）。

##### YiWayStep

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `irr₀` | `∀ {k} (V : Lw k) S S′ (x : Xm zero k S) (x′ : Xm zero k S′) t μ μ′ π → E₀ (Ψᵖ zero V S x t μ π) (Ψᵖ zero V S′ x′ t μ′ π)` | 目标层 0 上的折叠只依赖树与 `Pv` | 编译定理 |
| `Fo≅gk` | `∀ ζ → NA.read (Fo ζ) L.≅ NA.read (gk₁ᵖ ζ)` | 外层观察与内层折叠同值；燃料搜索的折叠上两者定义性相同，这里只到 `≅` | 编译定理 |
| `χ₁-topᵖ` | `S2.χ 1 ≼ NA.read (Fo G.top)` | | 编译定理 |
| `χ₁-d1ᵖ` | `S2.χ 1 ≼ NA.read (dᵖ 1)` | | 编译定理 |
| `Stepᵖ`（定义） | `∀ k m → GL.χ k ≼ NA.read (dᵖ m) → GL.χ (suc k) ≼ NA.read (Fo (dᵖ (suc m)))` | 缺的单步 | — |
| `T2≼ᴳᵖ` | `Stepᵖ → GL.T2ᴸ ≼ NA.read T⁺ʷᵖ` | 单步推出 ψ₀(Ω_Ω·2) 的带标签参照不高于读法 ψ₀(Ω_{Ω+1}) 的闭项 | 条件定理 |

`T2≼ᴳᵖ` 的前提：`Stepᵖ` 是否可满足未知，没有给出实例。在它被证出之前，这条定理什么也没说。

##### YiWayAsk

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `askedᵖ` | `NA.read (Fo ξaᵖ) ≼ NA.read T⁺ʷᵖ` | 坐标被值问到 | 编译定理 |
| `asked-nodeᵖ` | `NA.read (Ψᵖ zero V2 S₀ x₀ (G.lc rNᵖ bNᵖ) noM π₁ᵖ) ≼ NA.read T⁺ʷᵖ` | 那个结点的值被问到 | 编译定理 |
| `asked-stepᵖ` | `∀ m → NA.read (Fo ξaᵖ) ≼ NA.read (Fo (dᵖ (suc m)))` | 也在 `Stepᵖ` 结论之下，对一切 `m` | 编译定理 |
| `gK-formᵖ`、`gKc-1ᵖ` | `gK′ ξaᵖ ≡ G.lim gKcᵖ`；`gKcᵖ 1 ≡ G.lc rNᵖ bNᵖ` | | 有限测试 |
| `markedᵖ` | `walk pathN (bNᵖ G.top) (pM π₁ᵖ G.top) ≡ just (pNᵖ , just refl)` | 链第一步里 ℕ 极限层号位置上的结点带证据 | 有限测试 |
| `keptᵖ` | `IsK (cmpe₀ rNᵖ pNᵖ (just refl))` | 有证据时保留 | 有限测试 |
| `lostᵖ` | `cmpe₀ rNᵖ pNᵖ nothing ≡ fold′` | 没有证据时折叠 | 有限测试 |

#### 4. 办法

**WR′ 与 MvR。**
- 主线的 `keep s refl` 在 `WR′` 的定义里按 `refl` 匹配，主线一侧的搬运因此是恒等。
- `MvR` 要三样：保 `RR`、保 `LglR`、保第一位置的路径。三样正是 `ΨnLglR′` 的保留情形（`brRun`）所需要的。
- 在不含 Ω 结点的公共上界上，`cmpe` 只产生 `byEq refl`，由 `mvR-eq` 给出；ℕ 极限处经 `substR′`。

**Φ 的关系是这一路新加的部件。**
- 主线 `self` 折叠的结点经 `nodeAt` 沿槽位造，`Φ` 直接造 `G.lc (pos X r)`。两边分支域的类型只在位置具体时才相同。
- 所以按源位置陈述两个混合类型的关系：`RRL` 关系 M 侧 `Raw j` 与 N 侧 `Lay.A (Lo k′ r′)`，`LLL` 关系两侧的合法性证明。
- 派发的关系 `WΦ` 带搬运 `mvx`、`mlg`、`mle` 的三条保持。走位置时用 `WΦ-s₂` 与 `WΦ-sℕ` 换下标。
- 单侧引理 `nodeAtLcR`、`nodeAtLcLglR`、`nodeAtC` 处理"主线沿槽位造、产出端直接造"。

**消费端的合法性。** 只对 `noM`、`noP`、`lglA-no` 陈述。在这些层号上链点不带标注；`chC`、`chL`、`chP` 只在层号具体时化简，所以 `top` 那一句按内层层号分三种（`topPL`）。

**χ₁。**
- 单调要 `CpA`。它由 `plusA-weak`、`plusA-cp`、`KfkA-cp`、`Φ-cpA` 与 `cpInd` 拼出，外层用 `fgC` 去掉标注。
- 上下文引理写成对一族函数的模块 `Ctx`，实例化两次：外层观察 `Fo` 与内层折叠 `gk₁ᵖ`。
- 第 2 步里改用 `irr₀` 把各实例换到同一个形状 `GK₃`。

**翻译账。**
- 没有新构造子，没有 `Lab`，没有改任何折叠。
- 新部件都由类型不匹配或带标注的第一位置逼出：`RRL`、`LLL`、`WΦ`、`cpInd`、`irr₀`。
- 带标签的参照只出现在 `YiWayOne`（`S2`）与 `YiWayStep`（`GL`、`Lab`）的陈述里，用法同 YiDlVOne、YiDlVStep。

#### 5. 第一个障碍：`Stepᵖ`（未走通）

没有检查器报错，因为没有写它的证明。缺的引理就是 `Stepᵖ`，Agda 类型如第 3 节逐字所列（在 `YiWayStep`）。

**是否与派发有关。**
- 编译事实：在被问到的结点 `rNᵖ` 的链第一步里，旧派发卡住的那类位置 `pNᵖ` 带证据，派发保留（`markedᵖ`、`keptᵖ`；`askedᵖ` 与 `asked-stepᵖ` 说明这处的值在 `T⁺ʷᵖ` 与一切 `Fo (dᵖ (suc m))` 之下）。所以 YiDlLost 那个原因在这一对上不再出现。
- 判断：同一路径上其他的对是否仍折叠，没有检查。已知缺口是 `plusP` 把左加数里的结点相对右加数标 `noM`，`bNᵖ` 正是左加的形状。

**缺的东西（判断）。**
- 从 χ_k 到 χ_{k+1}，要对 y ≼ read ξ 的每一层给 ψ₀(Ω_Ω+Ω_y) 的下界。
- y 的后继那一步，下界要落在结点 `rNᵖ` 的内层链上。这条链的目标层是 `LNᵖ`，不是 0。
- 现有的值工具（`NA.read`、`cp≼`、`Ctx.ctx`）都只在目标层 0 上。缺的是给非零目标层的折叠值下界、再经外层折叠传到层 0 的引理。这一路没有写出它的类型。

#### 6. 偏离与事故

**设计上的偏离。**
- 被问到的坐标用了新的 `ξaᵖ = top + suc Bi`，其中 `Bi` 是产出端内层折叠的根值。YiProdTest 的 `ξa` 含燃料搜索折叠的 `Tw 2`，不是产出端值里的子项。这补上了 YiProd 回报 §1 的保留意见（"ξa 是不是新折叠真被问到的坐标没有检查"），但是换了坐标。`sᵖ`、`pathN` 沿用 YiDlLost 的搜索结果，经 `refl` 核过。
- `Fo` 与 `gk₁ᵖ` 在燃料搜索的折叠上定义性相同，这里不同。条件定理里 `stp` 一步用 `Fo≅gk` 换过去。
- 关系族只覆盖不含 Ω 结点的公共上界（`VRʷ`）与不带标注的输入。这够回归用，没有更一般的版本。

**编译中的小改动。** 以下都不是同一处的重新设计：
- 一次语法错：`∀ ml me` 少写了 `∀`。
- `WΦ` 的隐式参数推不出，加了别名 `MLg`、`MLe`。
- 走位置时 `WΦ` 下标不化简，改为在子句里用 `WΦ-s₂`、`WΦ-sℕ` 显式转换。
- `ΨsLglR` 的一个 `_` 推不出，改为显式写出。
- `YiWayOne` 里 `NE-Φ` 与 `topΦ` 的参数推不出，加了 `VT`、`XT`。

**其他。**
- 一次性试验 `AskTest.agda` 放在 `<实验目录>/agents/way/scratch/`，结果已搬进 `YiWayAsk`。日志在 `<实验目录>/agents/way/`。
- 没有改任何已有文件，没有提交。
