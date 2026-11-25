# (a) 结构迁到合法块 (YiLP)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | <synthetic>, claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 09:58 至 10:39 |
| 工具调用 / agda 编译 (粗数) | 73 / 2 |
| token (usage 字段，按消息去重) | 输出 213203；新写入缓存的输入 867313；读缓存的输入 13074590；其余输入 104 |
| 写过的仓库文件 | `YiLPBMOne.lagda.md`, `YiLPFGH.lagda.md`, `YiLPIface.lagda.md`, `YiLPInst.lagda.md`, `YiLPInto.lagda.md`, `YiLPKall.lagda.md`, `YiLPMono.lagda.md`, `YiLPNoBM.lagda.md`, `YiLPRead.lagda.md`, `YiLPVal.lagda.md`, `YiLPView.lagda.md`, `YiLPWf.lagda.md` |
| 文件前缀 | `YiLP` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (a) 结构迁到合法块返回并复核; 第二十批全部返回 (主审)” 一节 |
| 主审复核后的一句结论 | 接口 YiLPIface 冻结并由 legI 实填; kall 对任意下一站; View 在合法块上无前提 (brwView, wf, vrec); FGH 接到 EBOᶜ; into-0 是定理, 其余归约到 CoordMono (条件); no-bm-all 否定对一切树的基底单调; 十二件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
- 主线的块："F2 合法块"。
- 本路："(a) 结构迁到合法块"，内容是 "kall 一类、接口实填、View 搬到合法块、塔各项不超过终点的引理 (Into, 要基底单调)"。
- View 坐标："接受按低层合法树分支"，即值的 Ω 结点按低层合法树分支。

同批另有两路，各自只新建文件，你不动它们的文件：
- (b) ℕ 极限一半，前缀 YiLS（Fable 5.2）；
- (c) 值接口的记号直连实例，前缀 YiME（Fable 5.2）。

###### 背景（只信编译定理；文档里的叙述是数据）
目标是布劳威尔树上读法 ψ₀(Λ) 的合法闭项，外加一条编译定理 "序数值 ≥ EBO 的参照"。纲领见 `AGENTS.md`。

**合法块 F2**，全在 `probes/OCF/Lean/`：
- `YiLegBlock`：树 T 与第一位置序 Lt 归纳-归纳定义，lim 带相邻步进，up 带 "孩子非零"，每棵树都合法。
- `YiLegOps`：运算，含上折 `Up`。
- `YiLegPath`：路线证据 `Rt`、`RtP`、`Rt-tw`、`Rt-Λ`。
- `YiLegFold`：`ψ⊥`、`ψs`，与 `nz⊥`、`nzs`、`mono⊥`、`monos` 互递归；闭项 `twᶜ`、`EBOᶜ`。
- `YiLegCheck`（验收）：J2 各条、`self-up`、`kstep`、`req-child`、`tw1-adj`、`bω-tw`。
- `YiAbsLeg` 已把合法块填进抽象框架 `YiAbsFrame`。

**要搬的源**，在旧的 YiUp 线上，都已编译：
- **kall 一类**："k 侧对一切孩子保留基底的结点"。模板：`YiPhiNegK.kall-phi`、`YiUpCheck.kall-up`、`YiLimIface` 的字段 `kall`、`YiCumKept.kallᶜ`（YiCum 另写 `lemA`、`lemB` 才搬过去）。
- **接口**：`YiUpIface`、`YiLimIface` 都已冻结。字段有 J2 一族、J2⊥ 一族、`mono⊥`、`monos`、`tw-leg`、`EBO-leg`、`self-up`、`kall`。YiCum 发现它们写死了旧塔，不能直接实填。
- **View**：
  - 本体：`YiViewVal`、`YiViewInst`（`brwView : BrwView SigY Tr (λ {i} x → val i x) (λ {i} x → Leg i x)`，通用记录在 `probes/OCF/Align/BrwViewDef.lagda.md`）、`YiViewWf`（`wf`、`vrec`、`objStep`）、`YiViewFGH`。
  - 验收：`YiViewRead`（`FGH-read`）。
- **Into**：`YiRefTw2` 里 `Into n = read (twᶜ n) ≼ read EBOᶜ`，对的是旧块。YiRef 指出：`EBOᶜ` 的第 n 支用的是由前缀折出的底，不是 `B₀ (tw n)`，缺 "底变大，折叠值不降" 一类的基底单调引理（台账 V91）。

###### 要做（按次序，能做到哪一步就做到哪一步）
1. **合法块的接口记录**：新文件，冻结后只增不改。
   - 字段按 `YiLimIface` 选，但塔与 Λ 不写死成某一个塔的定义：要么对块参数化，要么用合法块自己的 `tw`/`Λ`，由你定，写清理由。
   - 合法性在合法块里是类型，`tw-leg` 一类字段可以退化或去掉，写清楚。
   - 用 `YiLegFold` 实填，能复用 `YiLegCheck` 的就复用。
2. **kall** 在合法块上成立，编译定理。
3. **View**：在合法块上做出 `BrwView` 实例，与 `YiViewInst.brwView` 同一个通用记录，再加部分良基（`wf`/`vrec`）。
   - 值的 Ω 坐标按低层合法树分支（作者已接受）。
   - FGH 接到 `EBOᶜ`。`FGH-read` 一类对参照框架的验收放验收文件。
4. **基底单调与 Into**：先证一条一般的基底单调引理，陈述由你定，但要能推出 Into；再在验收文件里证 `Into n`（对一切 n），或者证到第一个挡住的引理。
   - 另一路 (b) 若需要基底单调，会把它当显式前提，所以你的陈述要写得一般。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiLP`（模块名 `OCF.Lean.YiLP…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 第 1 到 3 件是成品候选：不导入记号与参照框架，`python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 要 OK。涉及 `read`、参照、记号的放验收文件，文首标 "验收文件"。
- **先验检查**（作者 2026-11-13 采纳为工作规则，见 `AGENTS.md`）：若要给折叠新写一行或换写法，先查目标是指定孩子的还是一致的、孩子下标有没有证据函数、有没有按存在性保留；对上 `YiAbsObs`/`YiAbsFrame` 的 `obs→dec` 一族的前提就不写。本路是搬运，原则上不该新写折叠行。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行；一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。无关参数可以用。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 堆墙的写法见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 临时目录：`<实验目录>/agents/lp`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；6G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：对纲领与目标意味着什么，再列关键路径上暴露的问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存、是否成品候选、importclosure。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 有限测试 / 判断）。
4. 接口记录的逐字字段，以及冻结状态。
5. 第一个障碍，精确到引理。
6. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-13 10:18 (UTC)：

主审：刚才网络与认证出错（API 403），你的任务被中途打断。作者已重新登录，请从断点接着做，简报与规则不变。
- 你已写出 YiLPIface、YiLPInst、YiLPKall、YiLPVal、YiLPView、YiLPWf 六个文件。先看 <你的临时目录>/agents/lp/ 里最后几份日志，确认哪个文件最后一次编译的状态。
- 断开时可能有一个 agda 进程还在跑。重新编译前先确认它的日志已经写完，或者已经结束；同时只跑一个 agda，堆 6G。
- 做完后按简报的格式回报。

Address this before completing your current task.

转录时间戳 2026-11-13 10:19 (UTC)：

主审：续派后又遇到一次 API 403，再试一次。请从断点接着做，简报与规则不变。
- 先看 <你的临时目录>/agents/lp/ 的日志，确认你已写出的六个 YiLP 文件最后的编译状态。
- 同时只跑一个 agda，堆 6G。

Address this before completing your current task.

转录时间戳 2026-11-13 10:23 (UTC)：

主审：作者重新登录了，请从断点接着做，简报与规则不变。
- 你已写出 YiLPIface、YiLPInst、YiLPKall、YiLPVal、YiLPView、YiLPWf 六个文件。先看 <你的临时目录>/agents/lp/ 的日志，确认最后的编译状态。
- 断开时可能有 agda 进程还在跑，先确认它已结束；同时只跑一个 agda，堆 6G。
- 做完后按简报的格式回报。

Address this before completing your current task.

## 回报原文

#### 1. 判决

**这对纲领与目标意味着什么**
- **纲领第 1 条，在合法块 F2 上：** View 已搬到合法块，是成品候选。每层每个对象都可以看成零、后继、ℕ 极限或 Ω 极限。
  - ℕ 极限的相邻项按值的第一位置序 `_◁_` 步进。
  - Ω 坐标是 `Br ℓ p`，即低层的树。合法块里树都合法，所以坐标与对象的合法性都是 `⊤`。
  - 与 `YiViewInst.brwView` 用同一个通用记录 `BrwViewDef.BrwView`，并有部分良基：`wf`、`vrec`、`objStep`。
  - FGH 接到合法块的 `EBOᶜ`。
  - 这些都是无前提的编译定理，导入闭包干净。
- **kall：** 在合法块上成立，编译定理，无前提。陈述对任意带证据与路线的层号 a 的下一站 `Nx a`，不对某个塔写死。塔各项是它的实例，证据逐字相同（`refl`）。
- **接口：** 新记录 `YiLPIface.Iface` 已由合法块折叠实填（`legI`），定稿冻结。
- **Into：** 未走通，没有否定。
  - 已证（编译定理）：`Into 0`。
  - 已证（条件定理）："坐标单调 `CoordMono (tw n)` ⇒ `Into (n+1)`"，以及 "`BaseMonoΩt` ⇒ 一切 `Into n`"。
  - `CoordMono` 未证，也未否定。我给不出它的实例，所以这两条条件定理的前提能否满足，目前不知道。
- **基底单调的陈述必须限在规范域：** 对一切树的基底单调已有编译否定（`no-bm-all`）。路线 (b) 若把基底单调当显式前提，不能取 "对一切树" 那一版。

**关键路径上暴露的问题**

| 问题 | 位置 | 档 |
|---|---|---|
| `Into n`（n ≥ 1）未证，归约到 `CoordMono (tw (n-1))` | `YiLPInto.into-coord`、`into-all-coord` | 条件定理；前提未证、未否定 |
| 对一切树的基底单调不成立：底变了，回灌链坐标随之改变，而分支函数对坐标不单调 | `YiLPNoBM.no-bm`、`no-bm-all` | 编译定理（否定） |
| `Into 1` 用到的两条回灌链从第 1 项起坐标不同（右边第 1 项是左边第 1 项的 `next`），分支孩子层 0 ⊕ ↑c 随坐标变 | `YiLPInto.chain-B₀`、`chain-B₁` | 有限测试 |
| 分支层号不随坐标变的情形下，基底单调成立（第 1 层的 Ω 树） | `YiLPBMOne.bm-one` | 编译定理 |
| 底不变、只换起点时，对一切树单调 | `YiLPMono.ψs-start` | 编译定理 |
| `YiViewVal.incl`（值放回块里）没有搬：合法块的 ℕ 极限要交树序步进，值合法性的证明不唯一，逐项放回的相邻两项对不上 | `YiLPVal` 文末 | 判断，未编译否定 |

#### 2. 文件表

都在 `probes/OCF/Lean/`。最后一轮做法：删掉自己 12 个模块的 `.agdai`（字面路径），按依赖次序逐个冷编；每份日志只有自己模块的 `Checking` 行；禁用构造检索为 0；仓库文件里没有本机路径。

| 文件 | 代码行 | 冷编退出码 | 最大驻留 | 成品候选 | importclosure |
|---|---|---|---|---|---|
| YiLPIface | 147 | 0 | 169 MB | 是（接口） | OK |
| YiLPKall | 55 | 0 | 163 MB | 是 | OK |
| YiLPInst | 57 | 0 | 170 MB | 是 | OK |
| YiLPVal | 228 | 0 | 378 MB | 是 | OK |
| YiLPView | 93 | 0 | 137 MB | 是 | OK |
| YiLPWf | 112 | 0 | 168 MB | 是 | OK |
| YiLPFGH | 40 | 0 | 161 MB | 是 | OK |
| YiLPMono | 164 | 0 | 217 MB | 是 | OK |
| YiLPBMOne | 74 | 0 | 187 MB | 是 | OK |
| YiLPNoBM | 94 | 0 | 180 MB | 否（否定，验收） | OK |
| YiLPRead | 56 | 0 | 557 MB | 否（验收文件） | FAIL：导入 `OCF.Align.Value`，预期如此 |
| YiLPInto | 59 | 0 | 577 MB | 否（验收文件） | FAIL：同上 |

#### 3. 定理表

陈述逐字摘自文件。

| 名字 | 陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `kall` | `(a : L) (ea : Ev a) (ra : Rt a) (B : Base (Nx a)) (β : Tr a) (nβ : a ⊢ zero ◃ β) (x : Tr (Nx a)) (c : Tr a) {t : Pos (a ⊕ ↑ a c)} (G : Br (a ⊕ ↑ a c) t → Tr (a ⊕ ↑ a c)) (e : a ⊕ ↑ a c ⊢ zero ◃ Ω t G) (i : InB a (↑ a c) t) (p : Pos a) → prE i (evc a ea c) ≡ inj₂ p → Kept p (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ (up x c (Ω t G) e))` | 下一站折到下标层 a 时，任一孩子里槽位严格在基底的结点，以基底槽位保留 | YiLPKall | 编译定理 |
| `kall-tw` | 同上，`a := tw n`，证据 `Ev-tw n`、`Rt-tw n` | 塔各项的实例 | YiLPKall | 编译定理 |
| `legI` | `legI : Iface` | 合法块折叠填满接口 | YiLPInst | 编译定理 |
| `tw-Nx`（另有 `Ev-tw-Nx`、`Rt-tw-Nx`） | `(n : ℕ) → tw (suc n) ≡ Nx (tw n)` | 塔第 n+1 项就是下一站 | YiLPInst | 编译定理（`refl`） |
| `brwView` | `BrwView SigY Tr (λ {i} x → val i x) (λ _ → ⊤)` | 合法块每层每个对象有 View | YiLPView | 编译定理 |
| `val-mono` | `(ℓ : L) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → val ℓ x ◁ val ℓ y` | 树的第一位置序推出值的第一位置序 | YiLPVal | 编译定理 |
| `val-leg` | `(ℓ : L) (x : Tr ℓ) → LegV ℓ (val ℓ x)` | 值合法 | YiLPVal | 编译定理 |
| `valCh-≈` | `(ℓ : L) (c : Ch ℓ) (y : ChT ℓ c) → valCh ℓ c y ≈ val (chL ℓ c) (chT ℓ c y)` | 抬升不改值 | YiLPVal | 编译定理 |
| `parts⊆` | `(ℓ : L) (x : Tr ℓ) {t : Tr ℓ} → Part (view ℓ x) t → Pt ℓ t x` | View 的部分都在部分关系里 | YiLPWf | 编译定理 |
| `wf` | `(ℓ : L) (x : Tr ℓ) → Acc ℓ x` | 部分关系良基 | YiLPWf | 编译定理 |
| `vrec` | `(ℓ : L) (P : Tr ℓ → Set) → ((x : Tr ℓ) → ((t : Tr ℓ) → Part (view ℓ x) t → P t) → P x) → (x : Tr ℓ) → P x` | 沿 View 递归 | YiLPWf | 编译定理 |
| `objStep` | `(ℓ : L) (x : Tr ℓ) → ObjStep (view ℓ x)` | View 的 ℕ 极限相邻项在树序里步进 | YiLPWf | 编译定理 |
| `FGH-val` | `(x : Tr zero) (n : ℕ) → FGHᵥ (val zero x) n ≡ FGH x n` | 树与值的 FGH 相同 | YiLPFGH | 编译定理 |
| `fgh-1` | `FGH EBOᶜ 1 ≡ 2` | 闭项 FGH 在 1 处为 2 | YiLPFGH | 编译定理 |
| `test₀` | `fgh 0 ≡ 0` | 闭项能沿第 0 项求值到底 | YiLPFGH | 有限测试 |
| `FGH-read` | `(x : Tr zero) (n : ℕ) → L.FGH (readᴸ x) n ≡ FGH x n` | 参照框架的 FGH 与本块逐点相等 | YiLPRead | 编译定理 |
| `≼→read` | `{x y : Tr zero} → val zero x ≼ val zero y → readᴸ x ≼ᴸ readᴸ y` | 值前序推出参照的 ≼ | YiLPRead | 编译定理 |
| `ψs-start` | `(ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β β′ : Tr j) (nβ : j ⊢ zero ◃ β) (nβ′ : j ⊢ zero ◃ β′) (x : Tr ℓ) → val j β ≼ val j β′ → val j (ψs ℓ ε ρ B j w β nβ x) ≼ val j (ψs ℓ ε ρ B j w β′ nβ′ x)` | 起点单调，对一切树 | YiLPMono | 编译定理 |
| `Up-base` | `∀ {ℓ} (j : L) (d : Dn ℓ j) (b b′ : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (nb′ : ℓ ⊢ zero ◃ b′) (y : Tr j) → val ℓ b ≼ val ℓ b′ → val ℓ (Up j d b nb y) ≼ val ℓ (Up j d b′ nb′ y)` | 上折对底单调 | YiLPMono | 编译定理 |
| `bm-zero⊥`（另有 `bm-zeros`） | `(x : Tr zero) → BM⊥ zero x` | 第 0 层每棵树基底单调 | YiLPMono | 编译定理 |
| `bm-Nx` | `(a : L) (ea : Ev a) (ra : Rt a) → CoordMono a ea ra → BM⊥ᵉ (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) (Ωt (Nx a))` | 坐标单调 ⇒ 下一站 Ω 树基底单调 | YiLPMono | 条件定理（前提 `CoordMono`） |
| `am⊥`（另有 `ams`） | `(B B′ : Base zero) → B ⊴ B′ → (c c′ : Tr zero) → val zero c ≼ val zero c′ → val zero (ψ⊥ zero tt tt B c) ≼ val zero (ψ⊥ zero tt tt B′ c′)` | 第 0 层折叠对参数按值单调 | YiLPBMOne | 编译定理 |
| `bm-one` | `BM⊥ one (Ωt one)` | 第 1 层 Ω 树基底单调 | YiLPBMOne | 编译定理 |
| `B₀⊴dL` | `(n : ℕ) (x : Tr Λ) → B₀ (tw n) ⊴ dL tw Ev-Λ Rt-Λ (B₀ Λ) n x` | EBOᶜ 各支的底不低于 B₀ | YiLPInto | 编译定理 |
| `into-bm` | `(n : ℕ) → BM⊥ᵉ (tw n) (Ev-tw n) (Rt-tw n) (Ωt (tw n)) → Intoᵛ n` | 塔第 n 项基底单调 ⇒ Into（值版） | YiLPInto | 条件定理 |
| `into-0` | `Into 0` | 塔第 0 项不超过终点 | YiLPInto | 编译定理 |
| `into-all-bm` | `BaseMonoΩt → (n : ℕ) → Into n` | 规范域基底单调 ⇒ 一切 Into | YiLPInto | 条件定理 |
| `into-coord` | `(n : ℕ) → CoordMono (tw n) (Ev-tw n) (Rt-tw n) → Into (suc n)` | 坐标单调 ⇒ Into (n+1) | YiLPInto | 条件定理 |
| `into-all-coord` | `((n : ℕ) → CoordMono (tw n) (Ev-tw n) (Rt-tw n)) → (n : ℕ) → Into n` | 同上，对一切 n | YiLPInto | 条件定理 |
| `chain-B₀` | `st₁ (B₀ (tw 1)) zero ≡ next (suc zero) ◃s` | Into 1 左链第 1 项 | YiLPInto | 有限测试 |
| `chain-B₁` | `st₁ B₁ zero ≡ next (st₁ (B₀ (tw 1)) zero) (ns B₁ zero (ink self))` | 右链第 1 项是左链第 1 项的 next | YiLPInto | 有限测试 |
| `no-bm` | `(B₀ one ⊴ B′) × (val zero (ψ⊥ one tt tt (B₀ one) xbad) ≼ val zero (ψ⊥ one tt tt B′ xbad) → ⊥)` | 第 1 层有一棵非规范树，底变大后值反而下降 | YiLPNoBM | 编译定理（否定） |
| `no-bm-all` | `((ℓ : L) (x : Tr ℓ) → BM⊥ ℓ x) → ⊥` | 对一切树的基底单调不成立 | YiLPNoBM | 编译定理（否定） |

几个陈述的说明：
- `Into n = readᴸ (twᶜ n) ≼ᴸ readᴸ EBOᶜ`，与 `YiRefTw2.Into` 同形，只是读回用的是本块的 `readᴸ`。
- `Intoᵛ n = val zero (twᶜ n) ≼ val zero EBOᶜ`，`ᵛ→ᴿ` 把它推到 `Into n`。
- `_⊴_`：
  ```
  B ⊴ B′ = (val zero (b⊥ B) ≼ val zero (b⊥ B′)) × ((j : L) (w : j ≤ ℓ) → val j (bs B j w) ≼ val j (bs B′ j w))
  ```
- `BaseMonoΩt = (ℓ : L) → BM⊥ ℓ (Ωt ℓ)`。
- `CoordMono a ea ra`：
  ```
  (B B′ : Base (Nx a)) → B ⊴ B′ → (c c′ : Tr a) → val a c ≼ val a c′
    → (val zero (ψ⊥ (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B (Gc a c)) ≼ val zero (ψ⊥ (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B′ (Gc a c′)))
    × (val a (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) (bs B a (ink self)) (ns B a (ink self)) (Gc a c))
       ≼ val a (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B′ a (ink self) (bs B′ a (ink self)) (ns B′ a (ink self)) (Gc a c′)))
  ```
  其中 `Gc a c = up zero c (Ωt (a ⊕ ↑ a c)) (Ωt-nz (a ⊕ ↑ a c))`。

#### 4. 接口记录 `YiLPIface.Iface`（逐字）

**冻结状态：** 定稿（2026-11-13），文首已写 "只增不改"。已由 `YiLPInst.legI` 实填。

**塔与 Λ 的处理：** `kstep`、`kall` 对任意 `(a, ea, ra)` 陈述在下一站 `Nx a = Ωₗ a (λ c → a ⊕ ↑ a c)` 上；`Ev-Nx`、`Rt-Nx` 照 `Ev-tw`、`Rt-tw` 的后继一行。这样塔第 n+1 项及其证据与 `Nx (tw n)` 逐字相同（`refl`），其他按同样方式造的塔也能用。没有字段提到 Λ。

**相对 `YiLimIface` 的增删：**
- 去掉 `kp-none`、`J2-lim-none`：路线必带，`Way` 只有 `fwd`、`bwd`。
- 去掉 `LegB`、`pres⊥`、`press`、`tw-leg`、`EBO-leg`：合法块里合法就是类型，`twᶜ n : Tr zero`、`EBOᶜ : Tr zero` 本身就是合法性。
- 新增 `nz⊥`、`nzs`：合法块要 "非零" 的证明。
- 新增 `node⊥`：到第 0 层的结点行。
- 没收 `J2-Ωb`（回退行），与 `YiLimIface` 一致。
- 下表里 `InB`、`prE`、`brE`、`liftBr`、`Kept`、`Nx`、`evc`、`Ev-Nx`、`Rt-Nx` 在同一文件里定义。

```
ψ⊥  : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → Tr ℓ → Tr zero
ψs  : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → (j : L) → j ≤ ℓ → (β : Tr j) → j ⊢ zero ◃ β → Tr ℓ → Tr j
nz⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (x : Tr ℓ) → zero ⊢ zero ◃ ψ⊥ ℓ ε ρ B x
nzs : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ) → j ⊢ zero ◃ ψs ℓ ε ρ B j w β nβ x
kp⁼ : (a : L) (ε : Ev a) (ρ : Rt a) (p : Pos⁼ a) {j : L} (w : j ≤ a) {X : Set} → ((q : Pos j) → (Br j q → Br⁼ a p) → X) → X → X
-- 记录内定义 (非字段): dS, dL, dW (经 chB, 由 ψ⊥ ψs nz⊥ nzs 给出), step ℓ ε ρ B p G z = fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (G z))
J2-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) (j : L) (w : j ≤ a) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (suc a)) (y : Tr a) (e : a ⊢ zero ◃ y) → ψs (suc a) ε ρ B j (ins w) β nβ (up x tt y e) ≡ ψs a ε ρ (dS a ε ρ B x) j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) y
J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g n)) (e : g n ⊢ zero ◃ y) → ψs (lim g) ε ρ B j (inl n w) β nβ (up x n y e) ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) y
J2-limu : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (j : L) (ws : (n : ℕ) → j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (m : ℕ) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) → ψs (lim g) ε ρ B j (inlu ws) β nβ (up x m y e) ≡ ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (ws m) (ψs (lim g) ε ρ B j (inlu ws) β nβ x) (nzs (lim g) ε ρ B j (inlu ws) β nβ x) y
J2-Ωk : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (w : j ≤ k) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → ψs (Ωₗ k h) ε ρ B j (ink w) β nβ (up x c y e) ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) y
J2-Ωu : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (ws : (c : Tr k) → j ≤ h c) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ (up x c y e) ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) y
J2⊥-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) (x : Tr (suc a)) (y : Tr a) (e : a ⊢ zero ◃ y) → ψ⊥ (suc a) ε ρ B (up x tt y e) ≡ ψ⊥ a ε ρ (dS a ε ρ B x) y
J2⊥-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (x : Tr (lim g)) (n : ℕ) (y : Tr (g n)) (e : g n ⊢ zero ◃ y) → ψ⊥ (lim g) ε ρ B (up x n y e) ≡ ψ⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) y
J2⊥-Ω : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → ψ⊥ (Ωₗ k h) ε ρ B (up x c y e) ≡ ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) y
mono⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε ρ B x ◃ ψ⊥ ℓ ε ρ B y
monos : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε ρ B j w β nβ x ◃ ψs ℓ ε ρ B j w β nβ y
self-up : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (β : Tr ℓ) (nβ : ℓ ⊢ zero ◃ β) (x : Tr ℓ) (c : Ch ℓ) (y : ChT ℓ c) (e : RCh ℓ c (chZ ℓ c) y) → ψs ℓ ε ρ B ℓ self β nβ (up x c y e) ≡ Upc ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y
node : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (p : Pos ℓ) (G : Br ℓ p → Tr ℓ) → ψs ℓ ε ρ B j w β nβ (Ω p G) ≡ kp⁼ ℓ ε ρ (inj₂ p) w (λ q cv → Ω q (λ z → ψs ℓ ε ρ B j w β nβ (G (cv z)))) (limc (λ n → ψs ℓ ε ρ B j w β nβ (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n))) (λ n → nzs ℓ ε ρ B j w β nβ (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n))))
node⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (p : Pos ℓ) (G : Br ℓ p → Tr ℓ) → ψ⊥ ℓ ε ρ B (Ω p G) ≡ limc (λ n → ψ⊥ ℓ ε ρ B (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n))) (λ n → nz⊥ ℓ ε ρ B (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n)))
kp-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n) {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g m ≤ g n) → way g (proj₂ ρ) m n ≡ fwd v → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d ≡ kp⁼ (g n) (ε n) (proj₁ ρ n) (psh v p) w (λ q cv → K q (λ z → pshBr v p (cv z))) d
kp-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n) {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g n ≤ g m) → way g (proj₂ ρ) m n ≡ bwd v → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d ≡ kp⁼ (g m) (ε m) (proj₁ ρ m) p (w ∙ v) K d
J2-lim-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L) (w : j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) (v : g n ≤ g m) → way g (proj₂ ρ) m n ≡ bwd v → ψs (lim g) ε ρ B j (inl n w) β nβ (up x m y e) ≡ ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (w ∙ v) (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) y
J2-lim-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L) (w : j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y) (v : g m ≤ g n) → way g (proj₂ ρ) m n ≡ fwd v → ψs (lim g) ε ρ B j (inl n w) β nβ (up x m y e) ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) (emb (g n) (ε n) v y e)
kstep : (a : L) (ea : Ev a) (ra : Rt a) (B : Base (Nx a)) (β : Tr a) (nβ : a ⊢ zero ◃ β) (x : Tr (Nx a)) (p : Pos a) (g : Br a p → Tr a) (e : a ⊢ zero ◃ Ω p g) → ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ (up x zero (Ω p g) e) ≡ Ω p (λ z → ψs a ea ra (dW a (λ c → a ⊕ ↑ a c) (Ev-Nx a ea) (Rt-Nx a ra) B zero x) a self (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ x) (nzs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ x) (g z))
kall : (a : L) (ea : Ev a) (ra : Rt a) (B : Base (Nx a)) (β : Tr a) (nβ : a ⊢ zero ◃ β) (x : Tr (Nx a)) (c : Tr a) {t : Pos (a ⊕ ↑ a c)} (G : Br (a ⊕ ↑ a c) t → Tr (a ⊕ ↑ a c)) (e : a ⊕ ↑ a c ⊢ zero ◃ Ω t G) (i : InB a (↑ a c) t) (p : Pos a) → prE i (evc a ea c) ≡ inj₂ p → Kept p (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ (up x c (Ω t G) e))
```

#### 5. 第一个障碍（精确到引理）

**挡住的引理：** `YiLPMono.CoordMono (tw 0) tt tt`，即 `Into 1` 所需的那一条。我没能证它，也没能否定它；`into-coord 0` 就要它。

**为什么卡在这里：**
- 塔第 1 项 Ω 树的折叠是两条回灌链的部分和。
- 底由 `B₀ (tw 1)` 换成 `B₁`（EBOᶜ 第 1 支的底）之后，链的第 1 项从 `next 1` 变成 `next (next 1)`（`chain-B₁`，有限测试）。
- 于是第 1 项起要比较的是两个**不同孩子层** `0 ⊕ ↑c`、`0 ⊕ ↑c′` 上 Ω 树的折叠，c 与 c′ 只按值相关。
- 下一步链坐标又由这两个不同层上的折叠给出，所以链上从此不再有共同层号。

**已排除或已覆盖的部分：**
- 只换起点不换底：`ψs-start` 对一切树成立。
- 分支层号不随坐标变的情形（第 1 层 Ω 树）：`bm-one` 成立，靠的是第 0 层折叠对参数按值单调（`am⊥`、`ams`）。
- 对任意分支函数：基底单调不成立（`no-bm-all`）。所以前提只能对规范分支族 `Gc` 陈述，`CoordMono` 正是这样写的。

**判断：** `CoordMono` 等价于 "规范分支族跨孩子层按坐标的值单调"。要证它，需要一个跨层号的比较理论，本路没有做。

#### 6. 偏离与事故

- **改名：** 简报里的 `nxt` 与 `YiLegPath` 的 `_<ₙ_` 构造子撞名，改叫 `Nx`、`Ev-Nx`、`Rt-Nx`。`BrwViewDef.Sig` 与 `YiLegBlock.Sig` 撞名，导入时改名为 `BSig`。
- **接口：** 比 `YiLimIface` 多了 `nz⊥`、`nzs`、`node⊥` 三个字段，删减见第 4 节。`kstep` 与 `kall` 推广到任意下一站 `Nx a`，不再写死塔。
- **复用验收文件：** `YiLPInst`（成品候选）复用了 `YiLegCheck` 的 J2 各条。`YiLegCheck` 文首标的是 "验收文件"，但它的导入闭包干净，importclosure 也 OK；是否允许成品候选这样导入，请主审定。
- **没搬 `incl`：** 理由是判断，没有编译否定（见第 1 节表）。
- **Into 的读回：** `Into` 用本块自己的 `readᴸ` 读进参照框架 `OCF.Align.Level`、`OCF.Align.Value`，没有用 `YiFreshValRead.read`；那个是旧块的读回。
- **折叠：** 没有新写任何折叠行，所以开新行前的先验检查不适用。新写的只有引理：`kp-ind₂`、`ψs-start`、`Up-base` 等。
- **事故：** 中途两次 API 403 中断。续派后核对了临时目录的日志：先前写的 6 个文件都已结束编译，退出码 0，`.agdai` 都已写出。沙箱禁止 `ps`，无法直接查进程；从日志与 `.rts` 统计都已写完判断，没有残留的 agda。
- **一次删除被拦：** 删接口文件的 `rm` 写成 shell 变量形式，被安全检查拦下，没有执行；改用字面路径后完成。
- **没有完整读、只检索或凭转述的材料：**
  - `YiAbsObs` 只检索了 `obs→dec` 一族的位置；`YiAbsFrame` 只读了文首到 `Fold` 记录开头。
  - `YiPhiNegK` 只读了第 20 到 185 行。
  - `IdeaLedger` V91 只看了检索出的那一行；YiCum 的 `lemA`、`lemB` 只读了 `YiCumKept`。
  - 记忆里 "ψ⁰ 对高层参数不尊重值" 一句是转述，没有用在任何结论里。
