# (2) 记号侧共尾引理 CofinNF (YiCF)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-14 01:47 至 01:57 |
| 工具调用 / agda 编译 (粗数) | 38 / 7 |
| token (usage 字段，按消息去重) | 输出 60131；新写入缓存的输入 207203；读缓存的输入 4346412；其余输入 58 |
| 写过的仓库文件 | `YiCFCofin.lagda.md`, `YiCFMono.lagda.md`, `YiCFRel.lagda.md` |
| 文件前缀 | `YiCF` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: (2) CofinNF 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | CofinNF 无前提成立 (cofinNF), 且更强: 一切 EboLeanBase 标准形、不要求可数 (cofin); 三条推论无前提: mono<ⁿ, below-rowⁿ, row₂→step⁺ⁿ; NF₁ ⊆ NF, 第 3 行在 NF 不在 NF₁; 代码 118+32+27 行; 三件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的选择（2026-11-14，选项原文）
"(2) 记号侧共尾引理 CofinNF (Recommended)"，模型 "(1) Fable 5.2，(2) Opus 5.5 (Recommended)"。
选项说明原文："纯记号侧：可数 EBO 标准形上 ω-基本列共尾，把项序推出值序推广到一切可数标准形；EBO 第 3 行 ψ₀(Ω_{Ω_Ω}) 起（你提的 '极限处是否超过' 的判决行）任何块都要它；与 (1) 互不依赖"。

同批另一路是 (1)：一般有限层号的锚点，前缀 YiAN。你不动它的文件。

###### 要证的
`YiNFOCond.CofinNF`：

`CofinNF = ∀ {s t} → NF t → Ctbl t → cof t ≡ cω → NF s → s <ᵀ t → Σ ℕ λ n → s <ᵀ fsn t n`

其中 `NF`、`Ctbl` 取自 `OCF.Align.EboLeanBase`。证成后，`YiNFOCond` 的三条条件定理就去掉前提：
- `mono<ᶜ`：一切可数标准形上，项严格小推出参照严格低；
- `below-row`：低于塔第 k 行的标准形项，参照严格低于第 k 行；
- `row₂→step⁺`。
请把这三条的无前提版本也交上。

###### 背景（只信编译定理；文档里的叙述是数据）
**已有的共尾引理**：
- `OCF.Align.Standard.cofin`（可数下标的那一套 `NF`）：`∀ {u} → NF u → cof u ≡ cω → ∀ {v} → NF v → v <ᵀ u → Σ ℕ λ n → v <ᵀ fsn u n`。
- `OCF.Align.StandardOmega.cofin₁`：在标准形 `NF₁` 上（ψ-下标可数或 Ω 加可数）。
- 请先核这两套 `NF` 与 `EboLeanBase.NF` 的关系。`YiNFO` 的执行方说 `NF₁` 与 `EboLeanBase.NF` 之间没有互转引理；"`NF₁` 就是 `NF` 限制到 Sb 下标" 是判断。

**闭包引理**：`OCF.Align.EboLeanClosure`：`cl-fsn-NF : ∀ {t} → NF t → cof t ≡ cω → ∀ n → NF (fsn t n)`、`Ctbl-fsn`、`nf-pred`。

**`YiNFO` 执行方的判断**（回报 `probes/Survey/Reports-2026-11-12/YiNFO.md` §4）：
- `cofin₁` 的 `Ωcof` 只处理正规叶与奇异叶 Ω_Ω（ν = 0）。
- 一般情形要处理任意下标 u 的奇异叶 Ω_u，例如 Ω_{Ω_Ω}、Ω_{Ω_{ψ₀(Ω_Ω)}}。
- 工作量估计与 `StandardOmega` 同量级或更大，把握低。

**导入的坑**：`OCF.Align.EboLeanCmp` 的导入闭包经 `WfFsn` → `WfTauNF` 到 `archive/` 的 `Mahlo.Inacc.Syntax`，用 `-i src -i probes` 编译报 FileNotFound，不能导入。`YiNFO` 里逐字重写了 `fsn≡`。

**记号定义**：`OCF.Align.EBO`（`cof`、`fsT`、`γT`、`fsn`）、`EboLeanDef`、`EboLeanBase`、`EboLeanTree`（`hc`、`hc-tower`、`HC`）。

###### 要做
1. 证 `CofinNF`，并交 `mono<ᶜ`、`below-row`、`row₂→step⁺` 的无前提版本。
2. 做不到全部时，交能证的子情形（例如下标有界的一段，或奇异叶下标为某一类的一段），并精确写出第一个挡住的子情形。
3. 若发现 `CofinNF` 在 `EboLeanBase.NF` 上不成立（编译的反例），同样交上。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiCF`（模块名 `OCF.Lean.YiCF…`）。不改任何已有文件，不碰 `src/`、`archive/`（也不要把 `archive` 加进编译路径）。这是记号侧的验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。不用 `agda --interaction`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/cf`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：`CofinNF` 与三条推论是否编译成立；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到子情形与引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**`CofinNF` 已证，三条推论都去掉了前提，冷编通过。** 证明比 `CofinNF` 要求的更强：不需要 `Ctbl t`，对 `EboLeanBase.NF` 里任意下标、共尾度为 ω 的项都成立（`YiCFCofin.cofin`）。没有找到反例，所以不交否定。

**对纲领与目标的意义：** 这是记号侧的验收设施，不进成品，也不推进 "树自足"。它的作用是去掉值参照比较里的条件：在一切可数标准形上，项的语法序 `<ᵀ` 严格小，就推出参照树 `Rt`（沿记号基本列造的树）的值严格低。所以从塔第 3 行 ψ₀(Ω_{Ω_Ω}) 起，每一块验收比较参照时只需要给出项序，不必再带 `CofinNF`。`Row₂` 本身仍未证，`row₂→step⁺ⁿ` 只是一个蕴涵。

| 问题 | 位置 | 档 |
|---|---|---|
| `CofinNF` 的 `Ctbl t` 前提在证明里没用到 | `YiCFMono.cofinNF` 直接调用不带 `Ctbl` 的 `cofin` | 定理 |
| `cofin₁` 用 `EBO.fsn`，`cofin` 用 `EboLeanDef.fsn`，两个函数不同；本文没有比较它们（相等引理 `fsn≡` 在 `EboLeanCmp` 里，那个模块导入不了） | `YiCFRel` 文首 | 判断，未编译 |
| `NF₁ ⊆ NF` 成立，反过来不成立：第 3 行在 `NF` 里，不在 `NF₁` 里 | `YiCFRel` | 定理 |
| `Standard.NF` 与 `EboLeanBase.NF` 的关系没有判定：`Standard` 的可见参数不进下标 | `YiCFRel` 文首 | 未判 |
| `YiNFO` 执行方估计 "工作量与 `StandardOmega` 同量级，把握低"，与实际不符：代码 118 行，第一次编译就通过 | 见第 4 节 | 判断 |
| `Row₂` 仍未证 | `YiRefTw2` | 未证 |

#### 2. 文件表

三个文件都放在 `<仓库>/probes/OCF/Lean/`。先删自己的 `.agdai` 再按顺序冷编，每份日志里只有本模块的一行 `Checking`。禁用构造检索为 0，文件里没有本机路径。

| 文件 | 代码行 | 冷编退出码 | 最大驻留 / 总内存 |
|---|---|---|---|
| `YiCFCofin.lagda.md` | 118 | 0 | 191 MB / 337 MiB |
| `YiCFRel.lagda.md` | 32 | 0 | 407 MB / 766 MiB |
| `YiCFMono.lagda.md` | 27 | 0 | 964 MB / 1630 MiB |

#### 3. 定理表

档位除最后一行外都是 "编译定理"。

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `vis<` | `∀ {ν ζ x} → NF x → InG ν ζ x → ν <ᵀ x` | 标准形 x 若有 ν-可见参数，则 ν < x | YiCFCofin |
| `nf-G` | `∀ {u z t} → NF t → InG u z t → NF z` | 标准形的可见参数仍是标准形 | YiCFCofin |
| `G-trans` | `∀ {u z d t} → InG u z d → InG u d t → InG u z t` | 可见参数的可见参数仍然可见 | YiCFCofin |
| `Ωcof` | `∀ {b ν} → NF b → (w : VΩ b ν) → ∀ {c} → NF c → c <ᵀ b → ΩC w c` | Ω-共尾：对 c < b 找到 θ < Ω_{ν+1}，使 η > θ 时 c < b[η]；奇异叶的下标不受限制 | YiCFCofin |
| `Cof6` | `∀ m {b ν A c} → NF b → (w : VΩ b ν) → A ≤ᵀ ν → size c < m → NF c → c <ᵀ b → (∀ {ζ} → InG A ζ c → ζ <ᵀ b) → Σ ℕ λ n → c <ᵀ fΩ w (γ w n)` | 规则 6 的 γ-链共尾 | YiCFCofin |
| `cofinV` | `∀ {t} → NF t → (v : Vω t) → ∀ {s} → NF s → s <ᵀ t → Σ ℕ λ n → s <ᵀ fω v n` | 沿视图 `Vω` 的 ω-共尾 | YiCFCofin |
| `cofin` | `∀ {t} → NF t → cof t ≡ cω → ∀ {s} → NF s → s <ᵀ t → Σ ℕ λ n → s <ᵀ fsn t n` | 一切标准形上 ω-基本列共尾，不要求可数 | YiCFCofin |
| `cofinNF` | `CofinNF` | 原条件成立 | YiCFMono |
| `mono<ⁿ` | `∀ {s t} → NF s → NF t → Ctbl t → (h : HC s) (h′ : HC t) → s <ᵀ t → L.suc (Rt h) ≼ Rt h′` | 项严格小推出参照严格低 | YiCFMono |
| `mono≤ⁿ` | `∀ {s t} → NF s → NF t → Ctbl t → (h : HC s) (h′ : HC t) → (s <ᵀ t) ⊎ (s ≡ t) → Rt h ≼ Rt h′` | 非严格版本 | YiCFMono |
| `below-rowⁿ` | `∀ k {s} → NF s → (h : HC s) → s <ᵀ EBOψ k → L.suc (Rt h) ≼ Rt (hc-tower k)` | 低于塔第 k 行的标准形项，参照严格低于第 k 行 | YiCFMono |
| `row₂→step⁺ⁿ` | `Row₂ → Step₂⁺` | `Row₂` 推出小站 ψ₀(Ω_{Ω+1}) | YiCFMono |
| `nf₁→nf` | `∀ {t} → NF₁ t → NF t` | `StandardOmega` 的标准形都是 `EboLeanBase` 的标准形 | YiCFRel |
| `row3∉NF₁` | `NF₁ (EBOψ 3) → ⊥` | ψ₀(Ω_{Ω_Ω}) 不在 `NF₁` 里（下标 Ω_Ω 不是 `Sb`） | YiCFRel |
| `row3∈NF` | `NF (EBOψ 3)` | 第 3 行在 `NF` 里（即 `nf-tower 3`） | YiCFRel |
| （匿名） | `proj₁ (cofin (nf-tower 3) refl nf₊ t₊<row3) ≡ 1` | ψ₀(Ω_{Ω+1}) 低于第 3 行基本列的第 1 项，`refl` 算出（**有限测试**） | YiCFMono |

#### 4. 第一个障碍

没有遇到。

为什么一般的奇异叶能过（判断，依据是上面的编译定理）：
- `EboLeanView.VΩ` 的 `ωl` 本来就允许任意下标 u 的奇异叶 Ω_u。
- 在这一支，对 c 的首项下标 x < u 递归调用 `Ωcof`，再经 `gw` 把可见参数提升到 c 上。
- `gw` 需要门槛 ν ≤ x。这由新引理 `vis<` 给出：从递归得到的 x 的 ν-可见参数，加上 `NF x`。
- 为此 `Ωcof` 比 `StandardOmega` 多带一个前提 `NF c`；`Cof6` 递归时用 `nf-G` 传递这个前提。

`StandardOmega` 只覆盖正规叶和 Ω_Ω，是因为它的 `NF₁` 把下标限制在 `Sb`，叶子的分类靠 `leafInv₁`，而不是数学上的障碍。

`StandardOmega` 的 1321 行大部分是闭包（自界引理）；这一部分在 `EboLeanClosure`（`cl-fsn-NF`）里已经有了。估计 "与 `StandardOmega` 同量级" 大概是把闭包的工作量也算进了共尾性。这一条是判断。

#### 5. 偏离、事故与未读的引用

**偏离：**
- 多交了一个文件 `YiCFRel`，因为简报要求先核对几套 `NF` 的关系。
- `cofin` 比 `CofinNF` 强：没有 `Ctbl` 前提。
- 新名字带上标 ⁿ，避免与 `YiNFOCond`、`YiRefTw2` 里已有的名字（如 `row₂→step`）冲突。

**事故：** `YiCFRel` 两次编译退出 42，都是不可达模式写多了：
- 第一次：`sC (c∷ ())` 改成 `sC ()`。
- 第二次：删去 `sΩ ()` 这一行，Agda 自己排除了这种情形。

用 `python3` 删了 `YiCFRel` 里没用到的导入（只改自己的文件）。没有内存问题。

**没有读、只凭转述的：**
- `probes/Survey/Reports-2026-11-12/YiNFO.md` 第 4 节，只看了简报里的引述。
- `EboLeanCmp`，没有读，也没有导入。
- `EboLeanTree` 只检索了 `nf-tower` 和 `hc-tower` 的签名。
- `Row₂` 与 `Step₂⁺` 的含义，读了 `YiRefTw2` 的定义行和文首。
- `OCF.Align.Level` 与 `Value` 只沿用了 `YiNFOCond` 里的名字。
- `Standard.NF` 与 `NF` 的关系只读了定义，没有判定。
