# View 与 FGH 落到新主线（基础，第一档交付） (YiVW)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十七批；外部模型，作者转发 |
| 前缀 | `YiVW` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：View 与 FGH 落到新主线（基础，第一档交付）（前缀 YiVW）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十七批五路之一（选项原文 "派，不经旧接口直接写 (Recommended)"），与在跑的 YiPJ、YiNX、YiXV 以及本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **纲领第 1 条**（`AGENTS.md`）：中间层若不直接用布劳威尔树，必须有布劳威尔树的 View（内部 View，值上一致）；ℕ 极限的相邻项按目标树自己的合法性步进，不要求按值严格递增（`BrwViewNeg.strict→LPO`）。
- **旧块上已有的**（只在 F2 的 `YiLegBlock` 上）：
  - `YiLPVal`：值类型 `V ℓ`（零、后继、ℕ 极限、Ω 结点）、`val`、跨层值前序 `_≼_`、`emb`、`val-mono`、`val-leg`、`val-+`；
  - `YiLPView`：`brwView`，用通用记录 `BrwViewDef.BrwView`（签名 `SigY : BSig`），一个记录对一切层号成立；`up x c y e` 按 y 的 View 分解（`mapUp`、`upz`）；
  - `YiLPWf`：`parts⊆`、`wf`、`vrec`、`objStep`。更早的同文版本：`YiViewInst`、`YiViewVal`、`YiViewWf`。
- **上一路（YiVF）停在第 0 步**：旧接口 `YiLPIface` 把层号类型写死成 `YiLegBlock.L`，接不上 `YiRWBlock.L`（回报 `probes/Survey/Reports-2026-11-12/YiVF.md`）。本路**不经旧接口**，直接在新块上写。
- View 是块（树的类型与值）的性质，与折叠无关。新主线的块是 `YiRWBlock`：层号 `nd s h`（`sS`、`sL`、`sΩ k`），树的构造子 `zero`、`suc`、`lim f a`、`Ω p g`、`up x c y e`（`e : R S c (z₀ S c) y`），结构前驱 `Lt`（`◃s`、`◃l`、`◃w`、`◃u`）。
- **FGH 主审已验**：临时文件 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC2FGH.agda.txt` 里，`FGH : Tr zero → ℕ → ℕ`（零、后继、ℕ 极限三行，`Ω`、`up` 在第 0 层的位置类型为空）与 `fghᶻ = FGH EBOᶻ` 编译通过（`EBOᶻ` 取自 `YiMTTab`，其导入闭包检查 OK）。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：为 `YiRWBlock` 写出 `BrwViewDef.BrwView` 要的签名（照 `YiLPView.SigY`），确认通用记录能接受新块；对不上的字段列出来。不成立就停下回报，写清是哪个字段。
1. **值**：照 `YiLPVal`，在 `YiRWBlock` 上给出 `V ℓ`、`val`、`_≼_`、`emb`、`val-mono`（树的第一位置序推出值的第一位置序）、`val-leg`。
2. **View**：照 `YiLPView`，`brwView` 对一切层号。
3. **良基**：照 `YiLPWf`，`parts⊆`、`wf`、`vrec`、`objStep`。
4. **FGH**：把主审的临时文件落成成品候选文件，查导入闭包干净。
5. 交一张表：`YiLP*` 的每个结论在新块上的对应（已搬、改写后搬、搬不了及原因）。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiVW`（模块名 `OCF.Lean.YiVW…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiNX`、`YiXV`、`YiLK`、`YiFM`、`YiLL`、`YiPC`）。成品候选文件（值、View、良基、FGH）用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包干净，文首标明 "成品候选"；其余标明 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有八路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；5G 仍耗尽（先在回报里说明）；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。



## 本会话主审复核（2026-11-14）

5 件、443 同口径代码行；主审逐件删自身接口、5G 独立冷编全 0，各仅自身 Checking、源码哈希不变；禁用构造、洞、本机路径、Funext 0。已读五件源码与回报的范围、逐项对应及候选说明。五件全域 importclosure 的本地 3/5/9/8/9 件均无禁用命中，并逐一与主审编译器依赖图集合相等。FGH 三行与空构造子分支、fghᶻ 定义，与作者 SelfCheck-SC2FGH 附件逐字一致。objStep 保对象第一位置，未要求值严格递增；test₀ 仅有限测试。未搬旧 LPRead/折叠接口，不作 EBO 序数强度结论。

## 回报原文（本会话执行）

### YiVW 完整回报（定稿）

定稿时间：2026-11-14T21:31:08+08:00。源码冻结时间：2026-11-14 21:25:28 +0800。执行方已完成下列自查；主审的独立冷编尚待进行。

#### 1. 判决与范围

对纲领第 1 条：在未修改 `YiRWBlock`、折叠与合法性的条件下，新主线块已有内部布劳威尔 View（`brwView`，一个通用记录覆盖一切层号）。View 的部分仍是本层对象，四种分解保持值等价；ℕ 极限相邻项满足目标值树自身的第一位置步进，并由 `objStep` 另证对象自身的第一位置步进。`parts⊆`、`wf`、`vrec` 使该 View 的部分可以良基递归。以上为已冷编的定理/构造。

对纲领第 2、4 条：全部源码使用要求的安全选项，不含公设、洞、停机/正性豁免、K 或函数外延前提。四个成品候选的导入闭包无禁用模块；用编译器依赖图核对，本地模块集合与脚本结果一致。此检查说明不引用记号，不说明定义没有受到记号启发。

对目标：本路完成现有新块的 View 与 FGH 基础验收。证明来源是旧 `YiLPVal`、`YiLPView`、`YiLPWf`、`YiLPFGH` 的搬运，不能据此声称树已自足。未新增关于终点序数值的上下界或 EBO 强度定理。`fghᶻ = FGH EBOᶻ` 是实际主线上的闭函数；这不是它的增长率与参照函数比较。

| 步骤 | 结果 | 档 |
|---|---|---|
| 0 最小检查 | 私有 `YiVWMin.agda` 实填全部 `Sig` 字段，形成 `BrwView` 类型，并实填所有层的零对象 View；首编退出 0 | 编译构造 |
| 1 值 | `V`、`val`、跨层 `_≼_`、`emb`、`val-mono`、`val-leg`、`val-+` 及支撑证明 | 编译定理/定义 |
| 2 View | `SigY`、`mapUp`、`view`、`brwView` | 编译定理/构造 |
| 3 良基 | `parts⊆`、`wf`、`vrec`、`objStep` | 编译定理/构造 |
| 4 FGH | 落地主审临时定义；另搬值一致与参数 1 的一般定理 | 编译定理/定义 |
| 4 有限求值 | `test₀ : fghᶻ 0 ≡ 0` | 有限测试，虽由 refl 编译验证，仍只作测试读 |
| 5 对应表 | 下列 §4 列出简报指定四模块的逐项对应，并另列其余 YiLP 模块的未搬清单 | 盘点 |

第 0 步签名字段：`Ix=L`、`B=V`、`_≼_=新值前序`、`Stp=新值第一位置序`、`Kd=Pos`、`Cd=Br`、`LgC=⊤`、`tg=同层`、`bz=zero`、`bs=suc`、`bl=lim`、`bΩ=Ω`。不匹配字段：0。最小检查源码于本地时间 2026-11-14 21:21:08 +0800 写出并启动检查，日志 21:21:10 完成，处于本轮开始后 30 分钟内。它检查签名可接与具体零实例；完整记录的无条件实例由后续 `brwView` 给出。

| 问题 | 位置 | 档与处置 |
|---|---|---|
| 第 0 步、值、View、良基、FGH 无未解字段 | 五份冻结源码 | 编译检查通过；停止条件均未触发 |
| 值文件首次机械替换把 valCh ℓ 误写为 valCH ℓ | 初稿 YiVWVal 第 59 行 | 工程错误，NotInScope/退出 42；把替换限定为独立词后退出 0，不涉及设计变更 |
| 本路不提供 EBO 下界，也不把参数 0/1 的值当强度 | 全部结果 | 范围说明；不是数学否定 |

#### 2. 文件、冷编与依赖审计

源码只新增以下五份。代码行按 Agda 代码块中非空行计；物理行含空行与文首。内存列均直接取冷编 `+RTS -s`：最大活数据 residency 与 GHC total memory；它们不是操作系统 RSS。累计分配量不等于同时占用的堆。每次上限 5G；依赖保留既有接口，只逐件删自身接口。

| 文件 | 代码行 / 物理行 | 冷编退出码 | 最大 residency（bytes） | GHC total memory（MiB） | 累计分配（bytes） | 耗时（elapsed 秒） |
|---|---:|---:|---:|---:|---:|---:|
| `probes/OCF/Lean/YiVWVal.lagda.md` | 215 / 270 | 0 | 247,711,664 | 586 | 9,571,168,024 | 3.220 |
| `probes/OCF/Lean/YiVWView.lagda.md` | 81 / 107 | 0 | 152,415,648 | 303 | 3,926,941,208 | 1.767 |
| `probes/OCF/Lean/YiVWWf.lagda.md` | 103 / 128 | 0 | 163,630,168 | 281 | 5,009,065,920 | 2.202 |
| `probes/OCF/Lean/YiVWFGH.lagda.md` | 38 / 55 | 0 | 151,010,256 | 255 | 3,897,637,720 | 1.830 |
| `probes/OCF/Lean/YiVWTest.lagda.md` | 6 / 14 | 0 | 144,647,944 | 251 | 3,846,524,424 | 1.829 |

冷编脚本：`<实验目录>/cold.sh`。五份冷编日志中每份 `Checking` 列表都恰为自身模块，无依赖模块的 `Checking` 行。冷编时同时生成依赖图，没有使用 `--ignore-interfaces`，只删了脚本中五条字面路径对应的自身 `.agdai`。

导入审计命令：`python3 probes/Survey/scripts/importclosure.py OCF.Lean.YiVWVal OCF.Lean.YiVWView OCF.Lean.YiVWWf OCF.Lean.YiVWFGH OCF.Lean.YiVWTest`。没有传 `--only`。退出码 0；编译器依赖图与脚本列出的本地模块集合逐个相等。

| 模块 | 本地闭包数 | 禁用命中 | 编译器核对 |
|---|---:|---:|---|
| `YiVWVal` | 3 | 0 | 相同 |
| `YiVWView` | 5 | 0 | 相同 |
| `YiVWWf` | 9 | 0 | 相同 |
| `YiVWFGH` | 8 | 0 | 相同 |
| `YiVWTest` | 9 | 0 | 相同 |

`YiVWVal` 仅导入新块与运算；`YiVWView` 另导入无记号通用记录。`YiVWWf` 为复用 `¬◃z` 导入 `YiRWCheck`，所以其导入闭包包含 `YiRWFold`、`YiRWPath`；实际使用的 `¬◃z` 只有树序递归，未给 View 增加折叠前提。`YiVWFGH` 通过 `YiMTTab` 使用实际主线闭项。

禁用构造检索：代码中的 `postulate`、`TERMINATING`、`NON_TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、`--with-K`、`--irrelevant-projections`、`--cubical`、交互洞标记、问号均命中 0；五份源码本机路径命中 0。每份文首不超过 5 行。所有签名、证明正文已读，冻结后 SHA256 一致。

#### 3. 定理与构造的逐字陈述

以下表列出全部非构造子声明；每表后的 Agda 块由冻结源码提取，保留原签名及换行，作为该表的“逐字陈述”列。数据类型/关系构造子见原源码，其对应另列在 §4。`go` 是 `vrec` 内的局部函数；其签名需在原来的上下文阅读。

##### YiVWVal

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| `chL` | 取字面孩子层。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `chP` | 把孩子层的槽位放进本层。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `chBr` | 读回孩子槽位的坐标。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `br0` | 本层槽位的第一坐标。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `_⊹_` | 值的加法。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `emb` | 把孩子层的值嵌入本层。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `chT` | 孩子对象的换型。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `val` | 新块树的值。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `valCh` | 孩子值嵌入本层。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `_≈_` | 互相不超过。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `≼-refl` | 值前序自反。 | `YiVWVal.lagda.md` | 编译定理 |
| `lim⁻` | 从极限的上界取出任一分支的上界。 | `YiVWVal.lagda.md` | 编译定理 |
| `Ω⁻` | 从 Ω 结点的上界取出任一分支的上界。 | `YiVWVal.lagda.md` | 编译定理 |
| `≼-trans` | 值前序传递。 | `YiVWVal.lagda.md` | 编译定理 |
| `sucT` | 传递证明中后继的辅助引理。 | `YiVWVal.lagda.md` | 编译定理 |
| `≈-refl` | 值等价自反。 | `YiVWVal.lagda.md` | 编译定理 |
| `≈-trans` | 值等价传递。 | `YiVWVal.lagda.md` | 编译定理 |
| `≼-suc` | 右端加后继不减值。 | `YiVWVal.lagda.md` | 编译定理 |
| `≼⊹` | 加法不低于左项。 | `YiVWVal.lagda.md` | 编译定理 |
| `⊹-mono` | 加法对右项单调。 | `YiVWVal.lagda.md` | 编译定理 |
| `⊹-monoˡ` | 加法对左项单调。 | `YiVWVal.lagda.md` | 编译定理 |
| `emb-mono` | 嵌入对值前序单调。 | `YiVWVal.lagda.md` | 编译定理 |
| `F≈` | 前缀加法复合嵌入保持值等价。 | `YiVWVal.lagda.md` | 编译定理 |
| `emb-≼` | 嵌入值不超过原值。 | `YiVWVal.lagda.md` | 编译定理 |
| `≼-emb` | 原值不超过嵌入值。 | `YiVWVal.lagda.md` | 编译定理 |
| `emb-≈` | 跨层嵌入保值。 | `YiVWVal.lagda.md` | 编译定理 |
| `valCh-≈` | 孩子换型与嵌入给相同值。 | `YiVWVal.lagda.md` | 编译定理 |
| `◁→≼` | 值的第一位置步进推出值前序。 | `YiVWVal.lagda.md` | 编译定理 |
| `⊹-mono◁` | 加法保持值的第一位置步进。 | `YiVWVal.lagda.md` | 编译定理 |
| `emb-mono◁` | 嵌入保持值的第一位置步进。 | `YiVWVal.lagda.md` | 编译定理 |
| `val-mono` | 树的第一位置步进推出值的第一位置步进。 | `YiVWVal.lagda.md` | 编译定理 |
| `valCh-mono₀` | 孩子的非零证明给出嵌入值的非零步进。 | `YiVWVal.lagda.md` | 编译定理 |
| `valCh-mono` | 孩子关系映到值的第一位置步进。 | `YiVWVal.lagda.md` | 编译定理 |
| `LegV` | 值合法性的谓词。 | `YiVWVal.lagda.md` | 编译定义/构造 |
| `⊹-leg` | 加法保持值合法。 | `YiVWVal.lagda.md` | 编译定理 |
| `emb-leg` | 嵌入保持值合法。 | `YiVWVal.lagda.md` | 编译定理 |
| `val-leg` | 每棵新块树的值合法。 | `YiVWVal.lagda.md` | 编译定理 |
| `valCh-leg` | 每个孩子嵌入值合法。 | `YiVWVal.lagda.md` | 编译定理 |
| `s≈` | 后继保持值等价。 | `YiVWVal.lagda.md` | 编译定理 |
| `l≈` | 逐点值等价推出 ℕ 极限值等价。 | `YiVWVal.lagda.md` | 编译定理 |
| `Ω≈` | 逐点值等价推出 Ω 结点值等价。 | `YiVWVal.lagda.md` | 编译定理 |
| `⊹-assoc` | 值加法按互相 ≼ 结合。 | `YiVWVal.lagda.md` | 编译定理 |
| `val-+` | 树加法的值等价于值加法。 | `YiVWVal.lagda.md` | 编译定理 |

逐字陈述：

```agda
chL : (ℓ : L) → CH ℓ → L

chP : (ℓ : L) (c : CH ℓ) → Pos (chL ℓ c) → Pos ℓ

chBr : (ℓ : L) (c : CH ℓ) (p : Pos (chL ℓ c)) → Br ℓ (chP ℓ c p) → Br (chL ℓ c) p

br0 : (ℓ : L) (p : Pos ℓ) → Br ℓ p

_⊹_ : ∀ {ℓ} → V ℓ → V ℓ → V ℓ

emb : (ℓ : L) (c : CH ℓ) → V (chL ℓ c) → V ℓ

chT : (ℓ : L) (c : CH ℓ) → ChT ℓ c → Tr (chL ℓ c)

  val : (ℓ : L) → Tr ℓ → V ℓ

  valCh : (ℓ : L) (c : CH ℓ) → ChT ℓ c → V ℓ

_≈_ : ∀ {ℓ₁ ℓ₂} → V ℓ₁ → V ℓ₂ → Set

≼-refl : ∀ {ℓ} (a : V ℓ) → a ≼ a

lim⁻ : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {c : V ℓ₂} (n : ℕ) → lim f ≼ c → f n ≼ c

Ω⁻ : ∀ {ℓ₁ ℓ₂ p} {g : Br ℓ₁ p → V ℓ₁} {c : V ℓ₂} (z : Br ℓ₁ p) → Ω p g ≼ c → g z ≼ c

  ≼-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≼ b → b ≼ c → a ≼ c

  sucT : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≼ b → suc b ≼ c → suc a ≼ c

≈-refl : ∀ {ℓ} (a : V ℓ) → a ≈ a

≈-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≈ b → b ≈ c → a ≈ c

≼-suc : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → a ≼ b → a ≼ suc b

≼⊹ : ∀ {ℓ} (a b : V ℓ) → a ≼ a ⊹ b

⊹-mono : ∀ {ℓ} (a : V ℓ) {b b′ : V ℓ} → b ≼ b′ → a ⊹ b ≼ a ⊹ b′

⊹-monoˡ : ∀ {ℓ} {a a′ : V ℓ} → a ≼ a′ → (b : V ℓ) → a ⊹ b ≼ a′ ⊹ b

emb-mono : (ℓ : L) (c : CH ℓ) {v w : V (chL ℓ c)} → v ≼ w → emb ℓ c v ≼ emb ℓ c w

F≈ : (ℓ : L) (c : CH ℓ) (a : V ℓ) {v w : V (chL ℓ c)} → v ≈ w → a ⊹ emb ℓ c v ≈ a ⊹ emb ℓ c w

emb-≼ : (ℓ : L) (c : CH ℓ) (v : V (chL ℓ c)) → emb ℓ c v ≼ v

≼-emb : (ℓ : L) (c : CH ℓ) (v : V (chL ℓ c)) → v ≼ emb ℓ c v

emb-≈ : (ℓ : L) (c : CH ℓ) (v : V (chL ℓ c)) → emb ℓ c v ≈ v

valCh-≈ : (ℓ : L) (c : CH ℓ) (y : ChT ℓ c) → valCh ℓ c y ≈ val (chL ℓ c) (chT ℓ c y)

◁→≼ : ∀ {ℓ} {x y : V ℓ} → x ◁ y → x ≼ y

⊹-mono◁ : ∀ {ℓ} (a : V ℓ) {b b′ : V ℓ} → b ◁ b′ → a ⊹ b ◁ a ⊹ b′

emb-mono◁ : (ℓ : L) (c : CH ℓ) {v w : V (chL ℓ c)} → v ◁ w → emb ℓ c v ◁ emb ℓ c w

  val-mono : (ℓ : L) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → val ℓ x ◁ val ℓ y

  valCh-mono₀ : (ℓ : L) (c : CH ℓ) (y : ChT ℓ c) → RCh ℓ c (chZ ℓ c) y → zero ◁ valCh ℓ c y

  valCh-mono : (ℓ : L) (c : CH ℓ) {y′ y : ChT ℓ c} → RCh ℓ c y′ y → valCh ℓ c y′ ◁ valCh ℓ c y

LegV : (ℓ : L) → V ℓ → Set

⊹-leg : ∀ {ℓ} (a b : V ℓ) → LegV ℓ a → LegV ℓ b → LegV ℓ (a ⊹ b)

emb-leg : (ℓ : L) (c : CH ℓ) (v : V (chL ℓ c)) → LegV (chL ℓ c) v → LegV ℓ (emb ℓ c v)

  val-leg : (ℓ : L) (x : Tr ℓ) → LegV ℓ (val ℓ x)

  valCh-leg : (ℓ : L) (c : CH ℓ) (y : ChT ℓ c) → LegV ℓ (valCh ℓ c y)

s≈ : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → a ≈ b → suc a ≈ suc b

l≈ : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {g : ℕ → V ℓ₂} → ((n : ℕ) → f n ≈ g n) → lim f ≈ lim g

Ω≈ : ∀ {ℓ} {p : Pos ℓ} {f g : Br ℓ p → V ℓ} → ((z : Br ℓ p) → f z ≈ g z) → Ω p f ≈ Ω p g

⊹-assoc : ∀ {ℓ} (a b c : V ℓ) → (a ⊹ b) ⊹ c ≈ a ⊹ (b ⊹ c)

val-+ : ∀ {ℓ} (x y : Tr ℓ) → val ℓ (x + y) ≈ val ℓ x ⊹ val ℓ y
```

##### YiVWView

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| `SigY` | 通用 View 所需的签名。 | `YiVWView.lagda.md` | 编译定义/构造 |
| `VW` | 新块的 View 类型。 | `YiVWView.lagda.md` | 编译定义/构造 |
| `chT⁻` | 孩子对象的反向换型。 | `YiVWView.lagda.md` | 编译定义/构造 |
| `conv` | 孩子第一位置关系的换型。 | `YiVWView.lagda.md` | 编译定理 |
| `conv₀` | 孩子非零关系的换型。 | `YiVWView.lagda.md` | 编译定理 |
| `chT-β` | 孩子往返换型逐字相等。 | `YiVWView.lagda.md` | 编译定理 |
| `upz′` | 按零或非零证据插入孩子对象。 | `YiVWView.lagda.md` | 编译定义/构造 |
| `upz` | 去除零孩子后的嵌入对象。 | `YiVWView.lagda.md` | 编译定义/构造 |
| `valCh-β` | 孩子的值换型逐字相等。 | `YiVWView.lagda.md` | 编译定理 |
| `val-upz′` | 带显式零分类的嵌入对象的值。 | `YiVWView.lagda.md` | 编译定理 |
| `val-upz` | 嵌入对象的值是前缀值加嵌入孩子值。 | `YiVWView.lagda.md` | 编译定理 |
| `reidx` | 沿值等价换 View 的索引。 | `YiVWView.lagda.md` | 编译定义/构造 |
| `lim≡` | 逐点相等推出 ℕ 极限值等价，无须函数外延。 | `YiVWView.lagda.md` | 编译定理 |
| `Ω≡` | 逐点相等推出 Ω 结点值等价，无须函数外延。 | `YiVWView.lagda.md` | 编译定理 |
| `mapUp` | 由前缀和孩子的 View 分解嵌入。 | `YiVWView.lagda.md` | 编译定义/构造 |
| `view` | 每个层号的每个对象都有 View。 | `YiVWView.lagda.md` | 编译定义/构造 |
| `brwView` | 单个通用记录覆盖所有层号。 | `YiVWView.lagda.md` | 编译定义/构造 |

逐字陈述：

```agda
SigY : BSig

VW : (ℓ : L) → V ℓ → Set

chT⁻ : (ℓ : L) (c : CH ℓ) → Tr (chL ℓ c) → ChT ℓ c

conv : (ℓ : L) (c : CH ℓ) {a b : Tr (chL ℓ c)} → chL ℓ c ⊢ a ◃ b → RCh ℓ c (chT⁻ ℓ c a) (chT⁻ ℓ c b)

conv₀ : (ℓ : L) (c : CH ℓ) {b : Tr (chL ℓ c)} → chL ℓ c ⊢ zero ◃ b → RCh ℓ c (chZ ℓ c) (chT⁻ ℓ c b)

chT-β : (ℓ : L) (c : CH ℓ) (y : Tr (chL ℓ c)) → chT ℓ c (chT⁻ ℓ c y) ≡ y

upz′ : (ℓ : L) (c : CH ℓ) → Tr ℓ → (y : Tr (chL ℓ c)) → (zero ≡ y) ⊎ (chL ℓ c ⊢ zero ◃ y) → Tr ℓ

upz : (ℓ : L) (c : CH ℓ) → Tr ℓ → Tr (chL ℓ c) → Tr ℓ

valCh-β : (ℓ : L) (c : CH ℓ) (y : Tr (chL ℓ c)) → valCh ℓ c (chT⁻ ℓ c y) ≡ emb ℓ c (val (chL ℓ c) y)

val-upz′ : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c)) (s : (zero ≡ y) ⊎ (chL ℓ c ⊢ zero ◃ y))
         → val ℓ (upz′ ℓ c x y s) ≡ val ℓ x ⊹ emb ℓ c (val (chL ℓ c) y)

val-upz : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c))
        → val ℓ (upz ℓ c x y) ≡ val ℓ x ⊹ emb ℓ c (val (chL ℓ c) y)

reidx : ∀ {ℓ} {w w′ : V ℓ} → w′ ≈ w → VW ℓ w → VW ℓ w′

lim≡ : ∀ {ℓ} (a b : ℕ → V ℓ) → ((n : ℕ) → a n ≡ b n) → lim a ≈ lim b

Ω≡ : ∀ {ℓ} (p : Pos ℓ) (a b : Br ℓ p → V ℓ) → ((z : Br ℓ p) → a z ≡ b z) → Ω p a ≈ Ω p b

mapUp : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) → VW ℓ (val ℓ x)
      → {v : V (chL ℓ c)} → VW (chL ℓ c) v → VW ℓ (val ℓ x ⊹ emb ℓ c v)

view : (ℓ : L) (x : Tr ℓ) → VW ℓ (val ℓ x)

brwView : BrwView SigY Tr (λ {i} x → val i x) (λ _ → ⊤)
```

##### YiVWWf

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| `Part` | 指定 View 的直接部分。 | `YiVWWf.lagda.md` | 编译定义/构造 |
| `part-reidx` | 值换索引保持部分。 | `YiVWWf.lagda.md` | 编译定理 |
| `part-mapUp` | 嵌入 View 的部分来自前缀或嵌入的孩子部分。 | `YiVWWf.lagda.md` | 编译定理 |
| `parts⊆` | View 的全部部分都落在 Pt 关系中。 | `YiVWWf.lagda.md` | 编译定理 |
| `accUp` | 两侧可达推出非零孩子嵌入可达。 | `YiVWWf.lagda.md` | 编译定理 |
| `accUpz` | 两侧可达推出去零孩子嵌入可达。 | `YiVWWf.lagda.md` | 编译定理 |
| `wf` | Pt 在所有层的所有对象上良基。 | `YiVWWf.lagda.md` | 编译定理 |
| `vrec` | 可沿 View 的部分递归计算。 | `YiVWWf.lagda.md` | 编译定义/构造 |
| `go` | 良基递归的局部执行函数。 | `YiVWWf.lagda.md` | 编译定义/构造 |
| `ObjStep` | View 的 ℕ 极限在对象关系上步进的命题。 | `YiVWWf.lagda.md` | 编译定义/构造 |
| `upz-step` | 去零孩子嵌入保持对象的第一位置步进。 | `YiVWWf.lagda.md` | 编译定理 |
| `os-reidx` | 值换索引保持对象步进。 | `YiVWWf.lagda.md` | 编译定理 |
| `os-mapUp` | 嵌入的 View 保持对象步进。 | `YiVWWf.lagda.md` | 编译定理 |
| `objStep` | 所有对象的 View 均满足对象步进。 | `YiVWWf.lagda.md` | 编译定理 |

逐字陈述：

```agda
Part : ∀ {ℓ v} → VW ℓ v → Tr ℓ → Set

part-reidx : ∀ {ℓ} {w w′ : V ℓ} (e : w′ ≈ w) (u : VW ℓ w) {t : Tr ℓ} → Part (reidx e u) t → Part u t

part-mapUp : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (vx : VW ℓ (val ℓ x)) {v : V (chL ℓ c)}
  (w : VW (chL ℓ c) v) {t : Tr ℓ} → Part (mapUp ℓ c x vx w) t
  → Part vx t ⊎ Σ (Tr (chL ℓ c)) λ y′ → Part w y′ × (t ≡ upz ℓ c x y′)

parts⊆ : (ℓ : L) (x : Tr ℓ) {t : Tr ℓ} → Part (view ℓ x) t → Pt ℓ t x

  accUp : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) → Acc ℓ x → (y : Tr (chL ℓ c)) (d : chL ℓ c ⊢ zero ◃ y)
        → Acc (chL ℓ c) y → Acc ℓ (up x c (chT⁻ ℓ c y) (conv₀ ℓ c d))

  accUpz : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) → Acc ℓ x → (y : Tr (chL ℓ c)) → Acc (chL ℓ c) y
         → Acc ℓ (upz ℓ c x y)

wf : (ℓ : L) (x : Tr ℓ) → Acc ℓ x

vrec : (ℓ : L) (P : Tr ℓ → Set)
     → ((x : Tr ℓ) → ((t : Tr ℓ) → Part (view ℓ x) t → P t) → P x)
     → (x : Tr ℓ) → P x

  go : (x : Tr ℓ) → Acc ℓ x → P x

ObjStep : ∀ {ℓ v} → VW ℓ v → Set

upz-step : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (a b : Tr (chL ℓ c)) → chL ℓ c ⊢ a ◃ b
         → ℓ ⊢ upz ℓ c x a ◃ upz ℓ c x b

os-reidx : ∀ {ℓ} {w w′ : V ℓ} (e : w′ ≈ w) (u : VW ℓ w) → ObjStep u → ObjStep (reidx e u)

os-mapUp : (ℓ : L) (c : CH ℓ) (x : Tr ℓ) (vx : VW ℓ (val ℓ x)) {v : V (chL ℓ c)}
  (w : VW (chL ℓ c) v) → ObjStep vx → ObjStep w → ObjStep (mapUp ℓ c x vx w)

objStep : (ℓ : L) (x : Tr ℓ) → ObjStep (view ℓ x)
```

##### YiVWFGH

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| `FGH` | 第 0 层树上的 FGH。 | `YiVWFGH.lagda.md` | 编译定义/构造 |
| `FGHᵥ` | 第 0 层值树上的 FGH。 | `YiVWFGH.lagda.md` | 编译定义/构造 |
| `iter-cong` | 逐点相等的函数有相等的有限迭代。 | `YiVWFGH.lagda.md` | 编译定理 |
| `FGH-val` | 树和它的值的 FGH 逐点相等。 | `YiVWFGH.lagda.md` | 编译定理 |
| `FGH-1` | 任何第 0 层树的 FGH 在 1 处等于 2。 | `YiVWFGH.lagda.md` | 编译定理 |
| `fghᶻ` | 实际主线闭项 EBOᶻ 的 FGH。 | `YiVWFGH.lagda.md` | 编译定义/构造 |
| `fghᶻ-1` | 主线闭项的 FGH 在 1 处等于 2。 | `YiVWFGH.lagda.md` | 编译定理 |

逐字陈述：

```agda
FGH : Tr zero → ℕ → ℕ

FGHᵥ : V zero → ℕ → ℕ

iter-cong : {A : Set} (f g : A → A) → ((a : A) → f a ≡ g a) → (a : A) (n : ℕ) → iter f a n ≡ iter g a n

FGH-val : (x : Tr zero) (n : ℕ) → FGHᵥ (val zero x) n ≡ FGH x n

FGH-1 : (x : Tr zero) → FGH x 1 ≡ 2

fghᶻ : ℕ → ℕ

fghᶻ-1 : FGH EBOᶻ 1 ≡ 2
```

##### YiVWTest

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| `test₀` | 检查主线闭项的 FGH 在 0 处求值得到 0。 | `YiVWTest.lagda.md` | 有限测试 |

逐字陈述：

```agda
test₀ : fghᶻ 0 ≡ 0
```

#### 4. YiLP 逐项对应

“已搬”指在新块上重用原证明正文；“改写后搬”指原来分开匹配 `suc a` / `lim g` / `Ωₗ k h` 的代码，合并为 `nd s h`，以及所需的孩子类型换型。两类的类型都由新模块导入的 `YiRWBlock.L`、`Tr` 与新值确定，没有把旧类型当成新类型。

| 旧声明 | 新声明 | 状态与原因 |
|---|---|---|
| `YiLPVal._⊹_` | `YiVWVal._⊹_` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.emb` | `YiVWVal.emb` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.chT` | `YiVWVal.chT` | 改写后搬：统一层号分支。 |
| `YiLPVal.val` | `YiVWVal.val` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.valCh` | `YiVWVal.valCh` | 改写后搬：统一层号分支。 |
| `YiLPVal._≈_` | `YiVWVal._≈_` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.≼-refl` | `YiVWVal.≼-refl` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.lim⁻` | `YiVWVal.lim⁻` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.Ω⁻` | `YiVWVal.Ω⁻` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.≼-trans` | `YiVWVal.≼-trans` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.sucT` | `YiVWVal.sucT` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.≈-refl` | `YiVWVal.≈-refl` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.≈-trans` | `YiVWVal.≈-trans` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.≼-suc` | `YiVWVal.≼-suc` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.≼⊹` | `YiVWVal.≼⊹` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.⊹-mono` | `YiVWVal.⊹-mono` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.⊹-monoˡ` | `YiVWVal.⊹-monoˡ` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.emb-mono` | `YiVWVal.emb-mono` | 改写后搬：统一层号分支。 |
| `YiLPVal.F≈` | `YiVWVal.F≈` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.emb-≼` | `YiVWVal.emb-≼` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.≼-emb` | `YiVWVal.≼-emb` | 改写后搬：统一层号分支。 |
| `YiLPVal.emb-≈` | `YiVWVal.emb-≈` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.valCh-≈` | `YiVWVal.valCh-≈` | 改写后搬：统一层号分支。 |
| `YiLPVal.◁→≼` | `YiVWVal.◁→≼` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.⊹-mono◁` | `YiVWVal.⊹-mono◁` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.emb-mono◁` | `YiVWVal.emb-mono◁` | 改写后搬：统一层号分支。 |
| `YiLPVal.val-mono` | `YiVWVal.val-mono` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.valCh-mono₀` | `YiVWVal.valCh-mono₀` | 改写后搬：统一层号分支。 |
| `YiLPVal.valCh-mono` | `YiVWVal.valCh-mono` | 改写后搬：统一层号分支。 |
| `YiLPVal.LegV` | `YiVWVal.LegV` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.⊹-leg` | `YiVWVal.⊹-leg` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.emb-leg` | `YiVWVal.emb-leg` | 改写后搬：统一层号分支。 |
| `YiLPVal.val-leg` | `YiVWVal.val-leg` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.valCh-leg` | `YiVWVal.valCh-leg` | 改写后搬：统一层号分支。 |
| `YiLPVal.s≈` | `YiVWVal.s≈` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.l≈` | `YiVWVal.l≈` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.Ω≈` | `YiVWVal.Ω≈` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.⊹-assoc` | `YiVWVal.⊹-assoc` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPVal.val-+` | `YiVWVal.val-+` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.SigY` | `YiVWView.SigY` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.VW` | `YiVWView.VW` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.chT⁻` | `YiVWView.chT⁻` | 改写后搬：统一层号分支。 |
| `YiLPView.conv` | `YiVWView.conv` | 改写后搬：统一层号分支。 |
| `YiLPView.conv₀` | `YiVWView.conv₀` | 改写后搬：统一层号分支。 |
| `YiLPView.chT-β` | `YiVWView.chT-β` | 改写后搬：统一层号分支。 |
| `YiLPView.upz′` | `YiVWView.upz′` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.upz` | `YiVWView.upz` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.valCh-β` | `YiVWView.valCh-β` | 改写后搬：统一层号分支。 |
| `YiLPView.val-upz′` | `YiVWView.val-upz′` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.val-upz` | `YiVWView.val-upz` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.reidx` | `YiVWView.reidx` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.lim≡` | `YiVWView.lim≡` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.Ω≡` | `YiVWView.Ω≡` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.mapUp` | `YiVWView.mapUp` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPView.view` | `YiVWView.view` | 改写后搬：统一层号分支。 |
| `YiLPView.brwView` | `YiVWView.brwView` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.Part` | `YiVWWf.Part` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.part-reidx` | `YiVWWf.part-reidx` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.part-mapUp` | `YiVWWf.part-mapUp` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.parts⊆` | `YiVWWf.parts⊆` | 改写后搬：统一层号分支。 |
| `YiLPWf.accUp` | `YiVWWf.accUp` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.accUpz` | `YiVWWf.accUpz` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.wf` | `YiVWWf.wf` | 改写后搬：统一层号分支。 |
| `YiLPWf.vrec` | `YiVWWf.vrec` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.go` | `YiVWWf.go` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.ObjStep` | `YiVWWf.ObjStep` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.upz-step` | `YiVWWf.upz-step` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.os-reidx` | `YiVWWf.os-reidx` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.os-mapUp` | `YiVWWf.os-mapUp` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPWf.objStep` | `YiVWWf.objStep` | 改写后搬：统一层号分支。 |
| `YiLPFGH.FGH` | `YiVWFGH.FGH` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPFGH.FGHᵥ` | `YiVWFGH.FGHᵥ` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPFGH.iter-cong` | `YiVWFGH.iter-cong` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPFGH.FGH-val` | `YiVWFGH.FGH-val` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPFGH.FGH-1` | `YiVWFGH.FGH-1` | 已搬：证明/定义同文，底座换成新块。 |
| `YiLPFGH.fgh` | `YiVWFGH.fghᶻ` | 改写后搬：闭项换成实际主线 EBOᶻ。 |
| `YiLPFGH.fgh-1` | `YiVWFGH.fghᶻ-1` | 改写后搬：闭项换成实际主线 EBOᶻ。 |
| `YiLPFGH.test₀` | `YiVWTest.test₀` | 改写后搬：闭项换成实际主线 EBOᶻ。 档：有限测试。 |

数据声明及构造子也全部对应：`YiLPVal.V` 的 `zero/suc/lim/Ω` → `YiVWVal.V`；`_≼_` 的 `z≼/s≼s/≼l/l≼/≼Ω/Ω≼` → 新跨层前序；`_◁_` 的 `◁s/◁l/◁w/◁t` → 新值第一位置；`YiLPWf.Pt` 的 `ps/pl/pw/pz/pu` 与 `Acc.acc` → `YiVWWf` 的同名声明。新增辅助接口只有 `chL/chP/chBr/br0`，从新块孩子层、槽位和第一坐标定义，不新增假设。

`YiLPVal` 文末提到但该模块未定义的 `YiViewVal.incl` 本路未尝试；不能把旧文末判断当成本路的否定。简报第 1–4 步要求的四个 YiLP 模块，没有一条已有结论被登记为“搬不了”。

为免将通配名 `YiLP*` 误读成已搬全部折叠接口，余下模块逐项列在这里。它们均未搬，原因是其命题涉及旧折叠、旧证据/路线、基底单调或外部值验收，超出本次按序的 View/FGH 第一档交付。本表只盘点源码中的声明，不重申它们已通过本路冷编，也不判断它们搬不了：

| 旧模块 | 未搬声明（含辅助定义与局部声明） | 状态 |
|---|---|---|
| `YiLPBMOne` | `base≼⊥`, `start≼s`, `am⊥`, `ams`, `one`, `bm-one`, `dB`, `hd`, `st`, `ch`, `chain`, `F`, `nF` | 未搬；本路未检验其在新块上的对应。 |
| `YiLPIface` | `Nx`, `evc`, `Ev-Nx`, `Rt-Nx`, `ib0`, `ibS`, `ibL`, `ibW`, `ibK`, `prE`, `liftBr`, `brE`, `Kept`, `ψ⊥`, `ψs`, `nz⊥`, `nzs`, `kp⁼`, `dS`, `dL`, `dW`, `step`, `J2-suc`, `J2-lim`, `J2-limu`, `J2-Ωk`, `J2-Ωu`, `J2⊥-suc`, `J2⊥-lim`, `J2⊥-Ω`, `mono⊥`, `monos`, `self-up`, `node`, `node⊥`, `kp-fwd`, `kp-bwd`, `J2-lim-bwd`, `J2-lim-fwd`, `kstep`, `kall` | 未搬；本路未检验其在新块上的对应。 |
| `YiLPInst` | `kstepᴸ`, `legI`, `kp-fwdᴸ`, `kp-bwdᴸ`, `tw-Nx`, `Ev-tw-Nx`, `Rt-tw-Nx`, `kall-legI-tw` | 未搬；本路未检验其在新块上的对应。 |
| `YiLPInto` | `Intoᵛ`, `Into`, `ᵛ→ᴿ`, `base≼⊥`, `start≼s`, `pre`, `B₀⊴dL`, `branch`, `into-bm`, `into-0`, `into-all-bm`, `into-coord`, `into-all-coord`, `st₁`, `B₁`, `chain-B₀`, `chain-B₁` | 未搬；本路未检验其在新块上的对应。 |
| `YiLPKall` | `lemA`, `lemB`, `kept-self`, `child-kept`, `kall`, `kall-tw` | 未搬；本路未检验其在新块上的对应。 |
| `YiLPMono` | `+≼`, `iter≼`, `next≼`, `cum≼`, `limc≼`, `Up-base`, `Upc-base≼`, `kp-ind₂`, `kp⁼-ind₂`, `ψs-start`, `_⊴_`, `BM⊥ᵉ`, `BM⊥`, `BMs`, `BaseMonoΩt`, `bm-zero⊥`, `bm-zeros`, `Gc`, `CoordMono`, `bm-Nx`, `st`, `chain`, `F`, `nF` | 未搬；本路未检验其在新块上的对应。 |
| `YiLPNoBM` | `natV`, `ωV`, `¬s≼z`, `¬ss`, `¬ω≼n`, `¬sω≼n`, `¬sω≼ω`, `≼⊹ʳ`, `one`, `𝟏`, `bsB`, `nsB`, `B′`, `⊴B′`, `big`, `gg`, `xbad`, `st′`, `gg-c′`, `F′`, `F′≡`, `cum≼n`, `right≼ω`, `1⊹n`, `itn`, `lemN`, `left≽`, `no-bm`, `no-bm-all` | 未搬；本路未检验其在新块上的对应。 |
| `YiLPRead` | `T₀`, `readᴸ`, `readV`, `read≼V`, `V≼read`, `≼→ᴸ`, `≼→read`, `iter-cong`, `FGH-read` | 未搬；本路未检验其在新块上的对应。 |

旧 `YiLPIface` 的记录字段仍固定在旧块，未修改。新 View 直接实例化 `BrwViewDef.BrwView`，没有经过该接口。

#### 5. 第一个障碍、偏离与信息来源

数学上的第一个未解障碍：本简报要求的第 0–4 步没有出现。精确到引理，`val-mono`、`mapUp`、`parts⊆`、`accUp/accUpz`、`wf`、`objStep` 全部通过。不存在需要修改树、折叠或合法性的检查器错误，也没有触发两次重新设计或 5G 耗尽的停止条件。

首个检查器错误是 `YiVWVal` 初稿第 59 行的 `valCH` 不在作用域（NotInScope，退出 42）。生成脚本原来把所有 `Ch ℓ` 字符串替换为 `CH ℓ`，误改 `valCh ℓ` / `RCh ℓ` 的尾部。修正为仅替换独立词后，该文件退出 0。没有数学重设计；首次成功日志与后续冷编日志已保留。

偏离与事故：

- 额外交 `YiVWTest`，用于保留旧 `YiLPFGH.test₀` 的有限测试，正文始终标“有限测试”。额外的一般 FGH 定理均来自该旧模块。没有扩大为新折叠或强度研究。
- 查询 `agda --help` 确认依赖图参数时，上一条有限测试的工具会话尚未回收；没有启动第二个类型检查。严格“一个 Agda 进程”按会话边界未完全做到。所有类型检查命令始终串行，每个均带 `-M5G`，未同时启动两次编译。该 help 命令也带了 5G 上限。
- 未改旧源码、导航、共享接口源文件、台账或留档；未派子路，未提交、推送、装包、pkill，也未删除自身范围外文件。编译依赖均使用既有接口。
- 未做定义级 depslice；本路审计采用导入闭包加实际编译器依赖图。没有把它夸为语义上“不受记号启发”。

已读：本任务完整简报、`AGENTS.md`、手册 §4、`BrwViewDef`、新块 `YiRWBlock`、使用到的 `YiRWOps`/`YiRWCheck` 签名与正文片段、旧四个 YiLP 源模块、主审 `SelfCheck-SC2FGH` 附件全文、`YiMTTab` 的导入与闭项定义、importclosure 脚本。其余 YiLP 模块仅为 §4 盘点读取文首与签名，没有逐件冷编或审查证明正文。

仅读简报转述、没有独立复核而且未用于本证明：`YiGIEnd.eboᵍ`、`YiVF` 的停止结论、YiPJ/YiNX/YiXV 与其他并行成果。主审临时附件本身未重新编译；本路将其定义落地并冷编了新文件。没有引入这些转述作为数学前提。

#### 6. 全部源码、实验目录、日志与冻结清单

仓库源码（绝对路径，供主审定位；本机路径仅在仓库外回报中出现）：

- `<仓库>/probes/OCF/Lean/YiVWVal.lagda.md`
- `<仓库>/probes/OCF/Lean/YiVWView.lagda.md`
- `<仓库>/probes/OCF/Lean/YiVWWf.lagda.md`
- `<仓库>/probes/OCF/Lean/YiVWFGH.lagda.md`
- `<仓库>/probes/OCF/Lean/YiVWTest.lagda.md`

唯一私有实验目录：`<实验目录>`。唯一私有临时 Agda 源码：`<实验目录>/YiVWMin.agda`。库文件：`<实验目录>/libraries`。所有生成/审计脚本均在此私有目录，无外部写入。

编译、工具与审计日志（完整列表）：

- `<实验目录>/YiVWFGH-cold.log`
- `<实验目录>/YiVWFGH-initial.log`
- `<实验目录>/YiVWMin.log`
- `<实验目录>/YiVWTest-cold.log`
- `<实验目录>/YiVWTest-initial.log`
- `<实验目录>/YiVWVal-cold.log`
- `<实验目录>/YiVWVal-initial.log`
- `<实验目录>/YiVWVal-retry1.log`
- `<实验目录>/YiVWView-cold.log`
- `<实验目录>/YiVWView-initial.log`
- `<实验目录>/YiVWWf-cold.log`
- `<实验目录>/YiVWWf-initial.log`
- `<实验目录>/agda-help.log`
- `<实验目录>/importclosure-final.log`
- `<实验目录>/importclosure.log`

其余私有文件（含全部脚本、接口、依赖图、退出码与审计结果）：

- `<实验目录>/YiVWFGH-cold.exit`
- `<实验目录>/YiVWFGH.dot`
- `<实验目录>/YiVWMin.agda`
- `<实验目录>/YiVWMin.agdai`
- `<实验目录>/YiVWTest-cold.exit`
- `<实验目录>/YiVWTest.dot`
- `<实验目录>/YiVWVal-cold.exit`
- `<实验目录>/YiVWVal.dot`
- `<实验目录>/YiVWView-cold.exit`
- `<实验目录>/YiVWView.dot`
- `<实验目录>/YiVWWf-cold.exit`
- `<实验目录>/YiVWWf.dot`
- `<实验目录>/auditdeps.py`
- `<实验目录>/cold-audit.json`
- `<实验目录>/cold.sh`
- `<实验目录>/dependency-audit.json`
- `<实验目录>/frozen.json`
- `<实验目录>/libraries`
- `<实验目录>/portfgh.py`
- `<实验目录>/portval.py`
- `<实验目录>/portview.py`
- `<实验目录>/portwf.py`
- `<实验目录>/report.py`
- `<实验目录>/source-audit.json`
- `<实验目录>/report-final.sha256`（本回报写成后的 SHA256）。

正式完整回报：`<回报原文>`。

冻结源码 SHA256：

| 文件 | SHA256 |
|---|---|
| `probes/OCF/Lean/YiVWVal.lagda.md` | `88584e44528d5fa1af1888413e372d01a74c34e12a84eafce51db2dc3c7499bf` |
| `probes/OCF/Lean/YiVWView.lagda.md` | `32acf9de77c16193530304fe094b3c1c6749859fab51a619946190cca8ac3f2a` |
| `probes/OCF/Lean/YiVWWf.lagda.md` | `39e4e0b2258f013d61835b4320fed9a60b93ac30f36cccbf67cc58d32e5b4c88` |
| `probes/OCF/Lean/YiVWFGH.lagda.md` | `aee6c76ff4d4445607659b0476337ce40778a43bb715f190b781d9966152a325` |
| `probes/OCF/Lean/YiVWTest.lagda.md` | `578e95776937947ff85d5c1b280ee0c7d87eb65da4ca19571e9342d17502526a` |

源码已冻结，回报已定稿。主审可独立逐件冷编；不需等待其他路线。
