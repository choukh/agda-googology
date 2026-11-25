# (2) 把下降引理与主线值搬到候选 A (YiKA)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 17:56 至 18:54 |
| 工具调用 / agda 编译 (粗数) | 67 / 13 |
| token (usage 字段，按消息去重) | 输出 313273；新写入缓存的输入 807105；读缓存的输入 19410273；其余输入 110 |
| 写过的仓库文件 | `YiKABY.lagda.md`, `YiKAEnd.lagda.md`, `YiKAMono.lagda.md`, `YiKARel.lagda.md`, `YiKATw1.lagda.md` |
| 文件前缀 | `YiKA` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: (2) 候选 A 的值返回并复核; 第三十批全部返回 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 候选 A 塔第 1 项 ≥ BTBO 参照 (btbo-tw1ᴷ, 与主线同值 same-tw1ᴷ), 终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) 参照 (tA≼EBOᴷ), 终点严格高于 BTBO (btbo≺EBOᴷ); 路线 (b) 变体: 候选 A 对 F2 的逐构造子关系 (不含 Ω 形状层号) 加两个闭项的手算下降; 单向关系 (a) 未尝试; 五件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的选择（2026-11-14，选项原文）
"(2) 把下降引理搬到候选 A (Recommended)"，模型 "(1)(3) Fable 5.2，(2) Opus 5.5 (Recommended)"。
选项说明原文："在候选 A（地板证书块）上证塔第 1 项 ≥ BTBO 与终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂))，让候选在已编译的值上与主线持平，供将来换主线时对照；不依赖 Tower"。

同批另一路是 (1)：证 Tower，前缀 YiTW。你不动它的文件。

###### 要证的
在候选 A 的块上证以下几条。候选 A 的闭项是 `YiKVFold` 的塔项与终点闭项，读回同 `YiBRValue.readRW`。
- `D.BTBOᴵ ≼ readRW (候选 A 的塔第 1 项)`；
- `(h : HC tA) → R2.Rt h ≼ readRW (候选 A 的终点闭项)`；
- 推论：候选 A 的终点闭项严格高于 BTBO 的参照。

###### 背景（只信编译定理；文档里的叙述是数据）
**主线**是精简块：`probes/OCF/Lean/YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`。主线上已编译、无前提：
- `YiBRValue`：`btbo-tw1ᴿ`、`btbo-EBOᴿ`、`btbo-twᴿ`、`bho-lowerᴿ`。这些是经 F2 与主线之间的逐层关系 `YiBRRel`、`YiBRFold`、`YiBRTw` 搬过来的。
- `YiEVEnd`：`tA≼EBOᴿ`、`btbo≺EBOᴿ`；`YiEVTw2`：`tA≼tw2ᴿ`。证法在 F2 上，用一般下降引理 `YiEVReach.reach`，再经 `EBOᶜ-R` 搬到主线。

**候选 A**（回报 `probes/Survey/Reports-2026-11-12/YiKV.md`）：
- 文件：`YiKVPath`、`YiKVFold`（成品候选），`YiKVCheck`（形状），`YiKVRel`、`YiKVValue`、`YiKVInst`（验收）。
- **与主线共用树与层号的类型**（`YiRWBlock`、`YiRWOps`），证据与折叠不同。
  - 证据：Ω 形状层号带地板与证书。
  - 折叠与主线的差别只在 Ω 形状层号上、目标经指定孩子 c′ 的情形：`cut`、`φ`、`kpA`。
  - 其余各行与主线逐字同式：`J2-u`、`J2⊥`、`J2-k`、`J2-s`、`J2-lim`、`self-up`。
- 候选 A 的执行方判断：底认得左项，所以值不低于主线（未编译）。
  - 依据：地板以上 `φ` 保留的结点比主线多；`kpA` 保留落在地板上的槽位，主线不保留；`φ` 的地板叶子加一。
- 已有：`bho-lowerᴷ`（ψ₀(Ω₂)），`a1-2`；`btbo-A0` 是条件的。执行方说塔第 1 项 ≥ BTBO 没有无条件转移。

###### 可能的两条路（由你定）
- **(a) 单向的跨块值关系 "主线 ≼ 候选 A"**：两块共用树类型，可以对同一棵树比较两边折叠的读回。若能证 "对规范域里的树，主线的折叠读回 ≼ 候选 A 的折叠读回"，主线已有的全部下界一次搬过去：`btbo-tw1ᴿ`、`btbo-EBOᴿ`、`tA≼EBOᴿ`、`tA≼tw2ᴿ`。
  - 先例是双向的逐层关系 `YiBR*`（F2 与主线，`RelL`/`RelT`/`RelD`/`RelE`/`RelW`，派生包括在关系里）与块侧值关系 `YiVR*`（`Le`、`fl`）。
  - 单向关系可以照它们写，在不同的行上只要求 ≼。
  - 量化域先取规范读回域（AGENTS "量化域先取带证据的读回域"）。
- **(b) 直接在候选 A 上重做**：照 `YiLS*`（塔第 1 项 ≥ BTBO）与 `YiEVReach`/`YiEVEnd` 的证法，在候选 A 的块上重写。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiKA`（模块名 `OCF.Lean.YiKA…`）。不改任何已有文件（包括 `YiKV*`），不碰 `src/`、`archive/`。这是验收文件，文首标明；树、折叠、合法性一行不改。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`，对一般推导陈述再代入；见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 临时目录：`<实验目录>/agents/ka`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；连续两条同形的退化反例。没有编译的否定时只写 "未走通"。若发现 "主线 ≼ 候选 A" 在某棵规范树上不成立，把反例写成编译定理交上，那本身是重要信息。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：三条是否编译成立；走的哪条路；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档；值写成 ψ₀(Ω_x)。
4. 第一个障碍，精确到引理（若有）。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 候选 A 下降引理 (前缀 YiKA) 回报

##### 1. 判决

三条都已编译成立，无前提，冷编退出码均为 0：
- **候选 A 的塔第 1 项**：`btbo-tw1ᴷ : D.BTBOᴵ ≼ readRW (twᶜ 1)`，即不低于 ψ₀(Ω_Ω)，也就是 BTBO 的参照。
- **候选 A 的终点闭项**：`tA≼EBOᴷ : (h : HC tA) → R2.Rt h ≼ readRW EBOᶜ`，即不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照。
- **推论**：`btbo≺EBOᴷ : L.suc D.BTBOᴵ ≼ readRW EBOᶜ`，终点严格高于 BTBO 的参照。

这里的 `twᶜ`、`EBOᶜ` 都是 `YiKVFold` 的闭项，读回用 `YiBRValue.readRW`。另有 `same-tw1ᴷ`：候选 A 与主线的塔第 1 项读回 `≅`。

**走的路**：是 (b)，但没有在 A 上重写 `YiLS*`/`YiEVReach`，也没有做 (a) 的 "主线 ≼ A"。
- **不含 Ω 形状的层号**（零、后继、ℕ 极限）：写了候选 A 对 F2 的逐构造子关系 `YiKARel`。它照 `YiBRFold` 删去 Ω 形状各行；候选 A 在这些层号上的各行与精简块逐字同式。
- **Ω 形状的层号**（Λ、`tw 2`、`tw 1`）：只对这两个闭项逐步手算。
- **用到的 F2 定理**（原样引用）：`YiLSBtbo.btbo-tw1`、`YiEBBtbo.Btbo.btbo-B`（一般底）、`YiEVReach.reach`。
- 终点处候选 A 的底不能与 F2 逐构造子相关，先用对底的单调 `flK` 把底降成 "第 0 层取第 1 支，其余取标准底"，再转到 F2。

**为什么不走 (a)：判断，没有编译依据，也没有尝试。**
- (a) 在 `tw 1` 这一层，要让折叠对一个值关系单调，而 `Ωt (tw 1)` 不在规范域里（`YiVRRel.β-not`、`YiVRFold.Dflt-tw2-not`）。
- 链的推进还需要 G 对下标按值单调（`YiVRRead` 里的 GMono，未证）。
- BTBO 的链论证要的是层号的结构嵌入，不是值的上下界（`YiPEStep` 文首：FUNC 在 Tri 下成立，Tri 推出 LPO）。

**对纲领与目标**：
- 全部是验收文件，树、折叠、合法性一行未改。没有新下标类型，没有函数外延，不碰壁垒。
- 对 "让树自足" 没有定义上的进展。作用是：在这两个闭项上，候选 A 的编译值定理与主线的 `btbo-tw1ᴿ`、`tA≼EBOᴿ`、`btbo≺EBOᴿ` 持平，可供换主线时对照。
- 主线的 `tA≼tw2ᴿ`（塔第 2 项）与 `btbo-twᴿ n`（塔各项）在 A 上没有做。

**发现**（编译定理；对照主线的说法是判断）：
- **塔第 1 项**：候选 A 不经分支侧一行（左项都是零），与 F2 的塔第 1 项逐构造子相关。
- **终点下降**：经过 `tw 2` 第 0 个孩子的底，`tw 2` 的 inc 0 一行切到地板 (`here`)，走树自己的孩子；主线在这里回退。
- **这个底在第 0 层的分量**：经 `tw 1` 任一孩子的分量，读回与第 1 支同值 (`TY≅`)；主线同位置是 `β + ι(twᶜ 1)`。
- **地板以上的分量**来自 φ 行。本证明只用到它们不低于标准底（第一位置序）。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `AK`/`SK` 只对零、后继、ℕ 极限形状的层号；是 `YiBRFold` 删去 Ω 形状各行的复制，约 370 行验收脚手架 | YiKARel | 编译定理的范围 |
| Ω 形状层号（Λ、`tw 2`、`tw 1`）上只对这两个闭项手算，不是一般定理 | YiKATw1, YiKABY, YiKAEnd | 编译定理的范围 |
| 塔第 2 项、塔各项（主线有 `tA≼tw2ᴿ`、`btbo-twᴿ`）未做 | — | 未做 |
| "主线 ≼ 候选 A" 的跨块关系未做，理由见上 | — | 判断 |
| 终点证明靠定义展开：`desc`、`EB1≡ : EB 1 ≡ β₂Y`、`path₂ᴷ` 由类型检查确认。YiKAEnd 冷编 4.13 GB / 72 s | YiKAEnd | 工程 |
| 地板以上的底分量（φ 输出）只用到 "不低于标准底"，没有更细的值 | YiKAEnd.`hB` | 编译定理（下界只需这么多） |
| `BY` 的分量公式：第 0 层用 `BY0`；其余层 `BYN` 没有单独陈述，只内联在 `rBY` 里（经 `cutN` 与 φ 的 `here` 子句） | YiKABY | 编译定理（写法说明） |

##### 2. 文件表

都在 `probes/OCF/Lean/`。冷编 `+RTS -M8G`；每个文件只删自己的接口，按依赖顺序编；日志里只有自己模块的 `Checking` 行。

| 文件 | 代码行 / 总行 | 冷编退出码 | 最大驻留 / 时间 |
|---|---|---|---|
| YiKARel.lagda.md | 367 / 415 | 0 | 2.11 GB / 22 s |
| YiKATw1.lagda.md | 56 / 91 | 0 | 1.07 GB / 12.5 s |
| YiKAMono.lagda.md | 168 / 206 | 0 | 0.26 GB / 2.5 s |
| YiKABY.lagda.md | 224 / 320 | 0 | 1.16 GB / 14.8 s |
| YiKAEnd.lagda.md | 127 / 189 | 0 | 4.13 GB / 72 s |

禁用构造检索为 0：postulate、TERMINATING、NO_POSITIVITY_CHECK、trustMe、洞、`--cubical`、K、`--irrelevant-projections`、funext、本机路径。选项行都是 `--safe --without-K --lossy-unification`。

##### 3. 定理表

全部是编译定理，无前提。

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `twᶜ-RK1` | `RelT zero F.zero (twᶜ 1) (F.twᶜ 1)` | A 的塔第 1 项与 F2 的逐构造子相关 | YiKATw1 |
| `btbo-tw1ᴷ` | `D.BTBOᴵ ≼ readRW (twᶜ 1)` | A 的塔第 1 项 ≥ ψ₀(Ω_Ω) | YiKATw1 |
| `same-tw1ᴷ` | `readRW (twᶜ 1) L.≅ readRW (RW.twᶜ 1)` | A 与主线的塔第 1 项同值 | YiKATw1 |
| `tA≼EBOᴷ` | `(h : HC tA) → R2.Rt h ≼ readRW EBOᶜ` | A 的终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) | YiKAEnd |
| `btbo≺EBOᴷ` | `L.suc D.BTBOᴵ ≼ readRW EBOᶜ` | A 的终点 > ψ₀(Ω_Ω) | YiKAEnd |
| `AK`, `SK` | 对 `RelEK ℓ ℓ′ o ε ρ`、`RelBase`、`RelW`、相关的起点与树：`RelT zero F.zero (proj₁ (ψ ℓ o B zero (z≤ ℓ) β x)) (F.ψ⊥ ℓ′ ε ρ B′ x′) × RelD …`（`SK` 对一般目标与 `F.ψs`） | 不含 Ω 形状的层号上，A 的折叠与 F2 的折叠相关 | YiKARel |
| `flK` | `(ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (B B′ : Base ℓ) → B ⊴ B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr⁺ j) → Le j (proj₁ β) (proj₁ β′) → {x x′ : Tr ℓ} → Le ℓ x x′ → Le j (proj₁ (ψ ℓ o B j w β x)) (proj₁ (ψ ℓ o B′ j w β′ x′))` | A 的折叠在这些层号上对底、起点、树单调 | YiKAMono |
| `cut0` | `∀ {m} (U : Ab zero m) (w : zero ≤ m) → NoΩ m → cut U w ≡ inj₁ self` | 目标第 0 层时证书切到地板 | YiKABY |
| `cutN` | `∀ {m s h} (U : Ab zero m) (w : nd s h ≤ m) → cut U w ≡ inj₂ tt` | 目标在地板以上时不切 | YiKABY |
| `btbo‴` | `D.BTBOᴵ ≼ read (Fn 1 B‴)` | F2 上手造的底 B‴ 满足 `OKB` 与起点条件，所以 `btbo-B` 适用 | YiKABY |
| `btbo-β₂Y` | `D.BTBOᴵ ≼ readRW (proj₁ β₂Y)` | A 的第 1 支（以前缀折出的底 `BY` 为底的 `tw 1` 折叠）≥ ψ₀(Ω_Ω) | YiKABY |
| `TY≅` | `(c : Tr zero) (w : zero ≤ h₁ᴷ c) → readRW (proj₁ (TY c w)) L.≅ readRW (proj₁ β₂Y)` | 经 `tw 1` 任一孩子的同一折叠与第 1 支同值 | YiKABY |
| `desc` | `readRW (proj₁ GE) ≼ readRW EBOᶜ` | 第 2 支 → `tw 2` 第 0 行 → `tw 1` 第 1 行（孩子 c₁）的下降 | YiKAEnd |

##### 4. 第一个障碍

三条目标没有挡住的引理。没有尝试的是 (a)，理由是上面的判断。

##### 5. 偏离与事故

- **路线**：是 (b) 的变体，原因见第 1 节。
- **事故**：
  - 第一次编译套了 `/usr/bin/time -l`，被沙箱拦下（sysctl），退出码 1 来自 time，agda 本身已完成。之后改用 `+RTS -s` 读内存。
  - 修过两个检查错误：`{sS}` 触发 `InvalidPun`；`YiRWFold.mapK` 与 `YiCertFold.mapK` 是两个函数，改为自写 `mapKRK`。另修了一处括号。
  - 第一轮冷编之后给 YiKATw1 加了 `same-tw1ᴷ`，之后 YiKATw1、YiKABY、YiKAEnd 重新冷编，退出码 0。
- **只凭签名或文字引用、没有逐行读的**：
  - `YiLSFold.OKB`、`ψs-⊵`，`YiNFOCase.tA`、`hA`、`btbo≺A`，`YiRefTw2.Rt`，`YiEVEnd.btbo≼row₂`。
  - "BTBO 的参照对应 ψ₀(Ω_Ω)" 取自 YiEVEnd 的说明（`Lab-uniq`），不是我核的。
  - 反对 (a) 的理由引用了 `YiVRRead` 里 GMono 的文字说明和 `YiPEStep` 文首的文字。
  - `YiEVReach.reach`、`YiEBBtbo.Btbo`、`YiLSBtbo.btbo-tw1`、`YiLSTw1` 的 `eq0`/`E-cum`、`YiBRFold`/`YiBROps`/`YiBRLem` 读过。
- **写入范围**：只新建了上面 5 个 `YiKA*` 文件，没有改已有文件。日志在 `<实验目录>/agents/ka/`（`cold-*.log`）。
