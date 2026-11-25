# 第一档成品的提取与行数表（工程） (YiPX)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十九批；外部模型，作者转发 |
| 前缀 | `YiPX` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：第一档成品的提取与行数表（工程）（前缀 YiPX）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十九批四路之一（选项原文 "第一档成品的提取与行数表（工程）"），与在跑的 YiXV、YiFM、YiLL、YiMX 在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- **再上一批**（主审复核过）：`YiLKSlot.steps→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → Laws.LowKeep gradedᵍ domsᵍ`（`YiLKIface`、`YiLKFold`、`YiLKSlot`；回报 `probes/Survey/Reports-2026-11-12/YiLK.md`）：折向第 0 层的各行对一切层号证完，剩每层一条槽位回灌的步进 `StepU`。第一档交付（合法闭项、内部 View、FGH）已在新主线上编译（`YiVW*`）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **第一档交付已编译**：合法闭项 `YiMTTab.EBOᶻ`（块 `YiRWBlock`、`YiRWOps`、`YiRWPath`，折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，合法性是类型 `Ok`）；内部 View `YiVWView.brwView`（`BrwViewDef.BrwView`），值 `YiVWVal`，良基 `YiVWWf`（`wf`、`vrec`、`objStep`）；FGH `YiVWFGH.fghᶻ`。主审已查 `YiVWVal`、`YiVWView`、`YiVWWf`、`YiVWFGH`、`YiMTTab` 的导入闭包干净。
- **AGENTS "审计记号无关性"**：从证书出发做定义级依赖切片，到达的记号定义必须为 0，并用读标签的定理作正对照（`probes/Survey/scripts/depslice.py`）；切片是语法级的；成品候选要提取到导入闭包干净的模块里，由编译器保证不引用（`probes/Survey/scripts/importclosure.py`，以 `agda --dependency-graph` 核对）。
- **行数的口径**（作者 2026-11-02 定，以后说行数一律用此表）：只数 agda 代码块内的非空、非注释行；四层累计：层 1 类型与函数的定义本身（不含折叠与证明）；层 2 加折叠函数与 FGH 的定义；层 3 加合法性自给的证明（树侧：折叠结果可当下标），到此 FGH 才算完成；层 4 加强度的证明。现有脚本 `probes/Survey/scripts/locslice.py`、`locslice_ord.py` 等（读 `--html` 输出做定义级切片），先读脚本再用。
- **标杆**（作者）："记号 EBO 加良基证明能控制在 1500 行以内, 那 EBO 的树序数也理应在这个行数量级之下"；前 3 层的标杆是 1513 行。作者要求每次报行数都带离标杆的余量，行数增长单列来源。

#### 要做的（按序）
0. **最小检查**：写入口模块（例如 `YiPXEntry`），只导入 `EBOᶻ`、`brwView`、`fghᶻ` 并重导出；编译通过；`importclosure.py` 干净，并用 `agda --dependency-graph` 核对闭包集合一致。不干净就停下回报，列出带记号的模块与导入链。
1. **记号无关性审计**：从 `EBOᶻ`、`brwView`、`fghᶻ` 出发做定义级依赖切片，到达的记号定义为 0；用一条读标签的定理作正对照（证明切片能看见记号）。
2. **行数表**：按上面的口径给第一档的四层表（层 1、层 2、层 3 分开；层 4 本档不适用就写 "不适用"），列出每层计入的模块与定义；与标杆 1513 比较，说出余量；与上一次报过的主线切片数（层 1 约 89、到层 3 约 473，只含块、折叠与表）对照，说出 View、良基、FGH 各加了多少。
3. **清单**：第一档成品候选的模块表（模块、作用、代码行、闭包是否干净）。不移动、不改任何已有文件。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiPX`（模块名 `OCF.Lean.YiPX…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiFM`、`YiLL`、`YiMX`、`YiGT`、`YiSU`、`YiPF`）。入口文件只放导入与不超过 10 行的判决（AGENTS 文字预算），文首标明 "成品候选入口"；不新增数学内容。
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



## 主审复核

各新模块均逐件删自身接口5G冷编0，禁用构造、洞、本机路径、Funext 0。完整范围见 probes/LOG.md。

## 回报原文（Codex 独立任务）

### YiPX 完整回报：第一档成品候选提取与行数表

冻结时间：2026-11-14T22:14:48.627571+08:00。本轮两份源码已冻结；执行方自查完成，等待主审独立复核。

#### 1. 判决、范围与问题表

对纲领：既有主线上合法闭项、内部布劳威尔 View 与闭的 FGH 已组成只含重导出的候选入口；完整入口另交塔项、View 部分递归、对象自身步进、值合法性及 FGH 值一致性。没有改树、折叠、合法性或既有数学结论。两入口编译通过，导入闭包与 Agda 依赖图的本地模块集合相同；未命中记号/标签禁用表。定义切片从指定三根出发，记号定义与记号词命中均为 0；读标签正对照命中 47 个记号模块定义块。

对目标：本轮是现有第一档交付的提取与成本审计，没有给出树自足的新判据，也没有增加终点的序数值下界。导入闭包检查保证候选不引用记号；它不证明设计未受记号启发。`EBOᶻ` 是现有闭项的名字，不能从名字读出已验收 EBO 强度。

最新事实按派发消息处理：主审已冷编 `YiLLLeafNeg.noLeaf`，当前全域 `Leaf` 前提为假，规范塔域未被该事实否定。本轮不引用 `YiGIEnd.eboᵍ`，不导入相关组装，不把依赖该假前提的条件终点计作强度成果；也不据此否定规范塔域。该最新否定源码本路未读、未编，事实来自主审通知。

| 步骤 | 到达情况 | 档 |
|---|---|---|
| 0 最小检查 | `YiPXEntry` 恰好重导出 EBOᶻ、brwView、fghᶻ；首编 0；闭包干净；本地集合一致 | 编译构造与工程检查 |
| 1 记号无关性 | 三根均 0；正对照 47；补交的五个根也均 0 | 语法级审计；闭包由编译器图核对 |
| 2 行数表 | 重算旧口径 89 / 473；完整前三层 89 / 481 / 845；余量 668 | 工程计数，不是数学定理 |
| 3 清单 | 14 个本地模块，列作用、全文代码行、各层切片行与闭包检查 | 工程盘点 |

私有目录建于 2026-11-14T22:04:41.166149+08:00；最小入口首编日志结束于 2026-11-14T22:04:55.816384+08:00。首个文件在开始读取简报后数分钟内完成编译，满足 30 分钟最小检查。

| 问题 | 位置 | 档与处置 |
|---|---|---|
| 三项最小入口不导入 View 良基与对象步进 | YiPXEntry 的三条导入 | 编译图事实；另新建 YiPXFull 显式重导出，不修改既有定义 |
| 切片看不见 Agda 求解的隐式依赖 | depslice.py / locslice.py | 工具局限；以干净导入闭包及编译器图补足“不引用记号”的保证 |
| 第 4 层 EBO 强度不在本档交付内 | 本轮全部候选 | 范围限制；写“不适用”，不报 0 行强度证明 |

#### 2. 新文件、冷编与内存

每次实际 Agda 调用均带 `+RTS -M5G`，同时只跑一个；正式编译另加 `-s`。冷编只删除对应 YiPX 自己的接口，依赖保持已有接口；未用 `--ignore-interfaces`。

| 新源码 | 代码行 | 冷编退出码 | maximum residency（字节） | RTS total memory in use |
|---|---:|---:|---:|---:|
| `probes/OCF/Lean/YiPXEntry.lagda.md` | 5 | 0 | 155,012,600 | 295 MiB |
| `probes/OCF/Lean/YiPXFull.lagda.md` | 7 | 0 | 169,159,552 | 296 MiB |

上表是 RTS 数据，不称为操作系统峰值 RSS。两日志的 Checking 名单分别只有 OCF.Lean.YiPXEntry 与 OCF.Lean.YiPXFull；这是“自身接口冷编、依赖热”的验收，不是重编所有借用模块。借用模块未删接口。

复现冷编命令（从仓库根目录，单次执行一项）：

```sh
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/YiPXEntry.agdai
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiPXEntry.lagda.md > <实验目录>/YiPXEntry-cold.log 2>&1
echo exit=$?
rm -f probes/_build/2.8.0.2/agda/OCF/Lean/YiPXFull.agdai
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiPXFull.lagda.md > <实验目录>/YiPXFull-cold.log 2>&1
echo exit=$?
```

#### 3. 编译构造与定理表

本轮没有新增数学定理；下表是入口直接重导出的既有构造/定理。所有数学前提保持原文；它们没有 `Leaf`、`Lift`、`LowKeep` 或函数外延前提。

| 名字 | 一句白话 | 原文件 | 档 |
|---|---|---|---|
| EBOᶻ | 第 0 层上的合法闭项；不从名字推定强度 | YiMTTab | 编译构造 |
| brwView | 每个对象可按四种布劳威尔构造分解，保持值一致 | YiVWView | 编译构造/定理 |
| twᶻ | 每个自然数下标对应一个合法塔项 | YiMTTab | 编译构造 |
| fghᶻ | 对该闭项取树上 FGH，得到闭的 ℕ → ℕ 函数 | YiVWFGH | 编译定义 |
| wf | View 部分所在的 Pt 关系良基 | YiVWWf | 编译定理 |
| vrec | 可沿 View 部分递归计算 | YiVWWf | 编译定义/构造 |
| objStep | ℕ 极限相邻对象沿自身第一位置步进 | YiVWWf | 编译定理 |
| val-leg | 每个对象的值合法 | YiVWVal | 编译定理 |
| FGH-val | 第 0 层对象与其值的 FGH 逐输入相等 | YiVWFGH | 编译定理 |

逐字陈述（模块限定名由上表给出，保留原文局部名字）：

```agda
EBOᶻ : Tr zero

twᶻ : ℕ → Tr zero

brwView : BrwView SigY Tr (λ {i} x → val i x) (λ _ → ⊤)

fghᶻ : ℕ → ℕ

wf : (ℓ : L) (x : Tr ℓ) → Acc ℓ x

vrec : (ℓ : L) (P : Tr ℓ → Set)
     → ((x : Tr ℓ) → ((t : Tr ℓ) → Part (view ℓ x) t → P t) → P x)
     → (x : Tr ℓ) → P x

objStep : (ℓ : L) (x : Tr ℓ) → ObjStep (view ℓ x)

val-leg : (ℓ : L) (x : Tr ℓ) → LegV ℓ (val ℓ x)

FGH-val : (x : Tr zero) (n : ℕ) → FGHᵥ (val zero x) n ≡ FGH x n
```

`fghᶻ = FGH EBOᶻ`。本轮未做新有限求值；没有把有限测试计作一般定理。以上是既有定义的入口提取，无需新条件接口的可满足性试验。

#### 4. 记号无关性审计

`importclosure.py` 未传任何 `--only` 参数；不是窄前缀审计。

| 入口 | 脚本本地模块数 | Agda 图本地模块数 | 集合差 | 禁用表命中 | Agda 图含库模块总数 |
|---|---:|---:|---|---:|---:|
| `OCF.Lean.YiPXEntry` | 11 | 11 | 两向均空 | 0 | 146 |
| `OCF.Lean.YiPXFull` | 14 | 14 | 两向均空 | 0 | 149 |

脚本把外部库模块当叶子；Agda 图继续展开标准库，所以这里比较的是任务涉及的本地模块闭包集合。不是声称脚本的外部库叶子集合等于标准库全部传递依赖。所有本地模块均在下表，既无记号模块也无标签验收模块。

生成 HTML / 图的编译均退出 0。指定三个根的定义切片：

| 根 | 到达块 | 记号模块块 | 其他模块记号词命中 |
|---|---:|---:|---:|
| YiMTTab:EBOᶻ | 123 | 0 | 0 |
| YiVWView:brwView | 86 | 0 | 0 |
| YiVWFGH:fghᶻ | 126 | 0 | 0 |
| 正对照 Correspond:FGH-Labω | 72 | 47 | 0 |

正对照逐字陈述：

```agda
FGH-Labω : ∀ {X t} → Lab X t → cof t ≡ cω →
           Σ (ℕ → Ordᶜ zero) λ F → (∀ n → Lab (F n) (fsn t n)) × (∀ n → FGH X n ≡ FGH (F n) n)
```

此定理实际解构 `Lab`，读取记号的共尾性与基本列；只用于检查切片工具，不进入候选闭包。它本身是带标签/共尾性前提的旧定理，这些前提不是交付 EBOᶻ / FGH 的前提。

补交五个根 `wf`、`vrec`、`objStep`、`val-leg`、`FGH-val` 分别到达 44、99、94、49、39 块，记号块和记号词均为 0。

切片代码复用已完整阅读的 `locslice.py` 中 `B4=` 之前的函数；同样阅读过 `depslice.py`、`locslice_ord.py` 与 `importclosure.py`。本地源检查未发现模块别名应用；参数化的 RWOps 与 BrwViewDef 模块头及 `open Sig S` 已出现在切片块中。没有手工排除任何到达的本地模块。切片仍是语法近似，不称作形式证明。

#### 5. 四层行数与增长来源

口径：只计 Agda 代码块的非空非注释行；按定义级依赖切片去重，不计标准库，不把未被根到达的导入、文件头、测试与旧折叠实例计入。模块参数头、必要的参数化 open、mutual 行到达时计入。两新入口共 12 行包装单列。

层次采用既有 89 / 473 的交付根口径：层 1 是主树类型与层号读回/塔定义；层 2 以合法闭项和 FGH 为根；层 3 加满足第一档验收所需的 View、良基、对象步进及其值证明。类型内携带的证据和互递归单调证明会随层 2 的依赖提前计入，不能把这部分代码删掉后称为可编译折叠。值结构作为 View/一致性证明的支撑计入层 3，不给主树层 1 重复计数。

| 层 | 本层新增 | 累计 | 距 1513 余量 |
|---|---:|---:|---:|
| 1 类型、层号读回、塔与 Λ | 89 | 89 | 1424 |
| 2 加折叠、表、合法闭项与 FGH 定义 | 392 | 481 | 1032 |
| 3 加 View、良基、对象步进、值合法与 FGH 一致性 | 364 | 845 | 668 |
| 4 加强度证明 | 不适用 | 不适用 | 不适用 |

若把本轮两份纯重导出包装的全文 12 行也计入交付包，为 857 行、余 656 行；与旧报告比较仍使用同口径的定义切片 845 行。整个本地模块文件全文代码共 1294 行、余 219 行，含未被候选根使用的旧实例/测试/定理；这与切片口径分开。上述余量都不表示第 4 层或 EBO 强度已经完成。

相同脚本、同一 HTML 语料重算旧主线：层 1 为 89，闭项/证书层为 473，逐模块完全重现旧报告的 YiRWPath 135、YiRWOps 97、YiTBRow 95、YiRWBlock 91、YiRWFold 33、YiMTTab 22。旧报告把折叠后合法性视作类型内已有，故层 2 与层 3 同为 473。

| 在旧 473 基础上按下列次序加入 | 新增行 | 加入后累计 | 距 1513 余量 |
|---|---:|---:|---:|
| 内部 View 及值/通用签名支撑 | 224 | 697 | 816 |
| View 部分良基、递归、对象步进及支撑 | 100 | 797 | 716 |
| 闭的 FGH 定义 | 8 | 805 | 708 |
| 值合法性 val-leg 的补充闭包 | 26 | 831 | 682 |
| FGH-val 的补充闭包（含 FGHᵥ） | 14 | 845 | 668 |

因此 View 增 224、良基/对象步进增 100、FGH 定义增 8；值合法性和 FGH 一致性再增 40。它们是按此顺序去重的边际成本，不是各模块全文长度之和。若只要闭项 + View 可递归/对象步进 + FGH 定义，核心切片是 805 行；完整入口额外交两条已有值证明，采用 845 行作为本轮完整交付数。

计数根：

```text
L1 = closure(YiRWBlock:tw, YiRWBlock:Λ)
L2 = L1 ∪ closure(YiMTTab:twᶻ, YiMTTab:EBOᶻ, YiVWFGH:fghᶻ)
L3 = L2 ∪ closure(YiVWView:brwView,
                  YiVWWf:wf, YiVWWf:vrec, YiVWWf:objStep,
                  YiVWVal:val-leg, YiVWFGH:FGH-val)
```

逐层完整定义块与行数同时保存在 `definitions.tsv` 和 `audit.json`，下方另列首次计入的定义块清单；`<mutual>`、`<open>` 是解析器的块名，不是新数学声明。

#### 6. 成品候选模块清单（全部本地源码）

| 模块 / 相对源码 | 作用 | 全文代码行 | L1 | L2 | L3 | 闭包干净 |
|---|---|---:|---:|---:|---:|---|
| `probes/OCF/Align/BrwViewDef.lagda.md` | 通用布劳威尔 View 签名与记录 | 33 | 0 | 0 | 29 | 是 |
| `probes/OCF/Lean/YiMTTab.lagda.md` | 最小比较表 rbᶻ 与合法闭项 | 41 | 0 | 22 | 22 | 是 |
| `probes/OCF/Lean/YiPXEntry.lagda.md` | 本轮新增：三项最小入口 | 5 | 0 | 0 | 0 | 是 |
| `probes/OCF/Lean/YiPXFull.lagda.md` | 本轮新增：第一档完整接口 | 7 | 0 | 0 | 0 | 是 |
| `probes/OCF/Lean/YiRWBlock.lagda.md` | 层号、树、第一位置序、读回、塔与 Λ | 101 | 89 | 91 | 91 | 是 |
| `probes/OCF/Lean/YiRWCheck.lagda.md` | 复用零无前驱定理 ¬◃z | 140 | 0 | 0 | 2 | 是 |
| `probes/OCF/Lean/YiRWFold.lagda.md` | 复用基础参数、槽位保留与结点构造 | 109 | 0 | 33 | 33 | 是 |
| `probes/OCF/Lean/YiRWOps.lagda.md` | 带非零证据的运算、迭代与嵌入 | 107 | 0 | 97 | 97 | 是 |
| `probes/OCF/Lean/YiRWPath.lagda.md` | 字面路径、Ok 与塔层号证书 | 147 | 0 | 135 | 135 | 是 |
| `probes/OCF/Lean/YiTBRow.lagda.md` | 带比较表的折叠 ψ 及其单调证明 | 167 | 0 | 95 | 95 | 是 |
| `probes/OCF/Lean/YiVWFGH.lagda.md` | 树上 FGH、闭函数与值一致性 | 38 | 0 | 8 | 22 | 是 |
| `probes/OCF/Lean/YiVWVal.lagda.md` | 值、值前序、步进与合法性 | 215 | 0 | 0 | 159 | 是 |
| `probes/OCF/Lean/YiVWView.lagda.md` | 新块的内部 View | 81 | 0 | 0 | 71 | 是 |
| `probes/OCF/Lean/YiVWWf.lagda.md` | View 部分良基、递归与对象步进 | 103 | 0 | 0 | 89 | 是 |

除了两个 YiPX 入口，本表均为复用的既有文件：没有移动、删减或改写。全表每项的传递导入闭包都没有禁用模块；完整入口的编译器图同时覆盖本表全部 14 个本地模块。`YiRWCheck` 全文 140 行，实际只取 ¬◃z 的 2 行；没有把它整篇算作必须数学代码。

#### 7. 第一个障碍、偏离与事故

没有遇到 Agda 类型错误、5G 堆耗尽或停止条件；没有需要修改树、折叠或合法性的步骤。第一个需要澄清的交付问题精确到 `YiVWWf.vrec` 与 `YiVWWf.objStep`：它们不在三项最小入口的导入闭包内。通过新增纯导入的 YiPXFull 显式交付，未重证。不是数学路线否定。

相对示例入口多建 YiPXFull 一件，用于完整交付已存在的良基/步进和两条值定理；不新增数学内容。环境检索曾查询不存在的 BrwViewLab 文件，rg 返回 2；随即读取已有 Correspond 的 FGH-Labω，未触发数学改题。没有 Agda 编译事故。补列塔项时，私有回报生成脚本曾因字符串换行退出 1，修复后重跑；该故障不涉及 Agda 源码或数学陈述。

没有另开子路，没有提交或推送；未修改 src、archive、README、LOG、台账及其他前缀源码。未新增候选数学路线或纸面否定。自己两份新文件的禁用构造和本机路径扫描均为 0；完整候选闭包的 14 份源码代码段的公设、洞、停机/正性豁免、trustMe、Funext、K、irrelevant projections 与 --cubical 扫描也为 0。

未读、只据转述引用：YiLLLeafNeg.noLeaf 的最新主审事实；简报里的 YiGIEnd、YiLKSlot 前情。它们不参与本轮编译、依赖根或行数。YiMT 的旧 89 / 473 报告相关段落已读，并由本路重算；YiVW 的既有回报用于核对第一档范围，未把其旧内存数字冒充本轮数据。

#### 8. 全部实验目录、源码、脚本与日志

仓库根：`<仓库>`。唯一实验目录：`<实验目录>`。没有临时 Agda 数学试验源码。完整回报：`<临时目录>`。环境帮助日志另在 `<临时目录>`。

本轮仓库新增源码只有：

- `probes/OCF/Lean/YiPXEntry.lagda.md`
- `probes/OCF/Lean/YiPXFull.lagda.md`

复用源码全部列在 §6；正对照另读/编 HTML 的源码为 `probes/OCF/Align/Correspond.lagda.md`，不进入候选清单。完整文件审计表 audit.json 含 §6 所有源码的 SHA-256。

私有脚本：

- `slice-initial.py`：试算与旧口径复现
- `audit.py`：正式四层计数、逐块与逐模块表、图集合核对
- `report.py`：生成本回报

所有脚本均在唯一实验目录；未改仓库审计脚本。

日志（全部路径以唯一实验目录为前缀）：
- `Correspond-positive-html.log`
- `YiPXEntry-cold.log`
- `YiPXEntry-html.log`
- `YiPXEntry-initial.log`
- `YiPXFull-cold.log`
- `YiPXFull-initial-html.log`
- `YiVWWf-html.log`
- `audit.log`
- `depslice-candidates.log`
- `depslice-full-extra.log`
- `depslice-positive.log`
- `final-check.log`
- `importclosure-entry.log`
- `importclosure-full.log`
- `report-generation.log`
- `slice-initial.log`
- `<临时目录>`（Agda 5G 的 --help，退出 0）

其余审计产物：

- `libraries`：两行标准库路径
- `html/`：成功编译生成的 HTML 语料
- `YiPXEntry.dot`、`YiPXFull.dot`：Agda 编译器依赖图
- `closure-compare.json`：最小入口图核对
- `audit.json`：全部 roots、闭包、逐块原文/行数、源码哈希及模块清单
- `definitions.tsv`：逐层首次计入的所有定义块
- `forbidden-scan.json`：新源码禁用与本机路径检查
- `closure-forbidden-scan.json`：14 份候选闭包源码禁用检查
- `YiPXEntry-cold.exit`、`YiPXFull-cold.exit`：冷编退出码 0 的记录
- `artifact-manifest.txt`：实验目录全部文件名清单

冻结的新源码 SHA-256：

| 源码 | SHA-256 |
|---|---|
| `probes/OCF/Lean/YiPXEntry.lagda.md` | `8aac9b365f83d53c796b2448561cfd7484d2033abe05ab1113e30c4ae66a0fa4` |
| `probes/OCF/Lean/YiPXFull.lagda.md` | `787348e2c5d0a5666693bb235ad4177d3a076297642d77c380613b1c09110939` |

#### 附：逐层首次计入的全部定义块

##### L1
- `OCF.Lean.YiRWBlock`：Sg (10)；<mutual> (1)；T (6)；Lt (8)；<mutual> (1)；L (4)；Sh (4)；Ch (4)；Sig (2)；Tr (2)；PK (3)；Pos (3)；Pos⁼ (2)；Br (3)；Br⁼ (3)；sl (3)；sl⁼ (3)；CH (3)；ChT (2)；chZ (2)；RCh (2)；at (2)；fromBr (2)；_⊕_ (3)；↑ (6)；tw (3)；Λ (2)。

##### L2
- `OCF.Lean.YiMTTab`：lo (3)；hi (3)；tbᶻ (5)；rbᶻ (5)；ψ₀ᶻ (2)；twᶻ (2)；EBOᶻ (2)。
- `OCF.Lean.YiRWBlock`：_⊢_◃_ (2)。
- `OCF.Lean.YiRWFold`：Base (2)；B₀ (2)；Keep (2)；mapK (3)；<mutual> (1)；kp (14)；kp⁼ (3)；node⁺ (3)；nodeLe (3)。
- `OCF.Lean.YiRWOps`：iter (3)；module _ (1)；T⁺ (2)；<mutual> (1)；_+_ (6)；+-mono (7)；lim⁺ (2)；nextA (3)；next⁺ (2)；cum (3)；limc⁺ (2)；Ω⁺ (2)；<mutual> (1)；zl (6)；z◃ (4)；Tr⁺ (2)；c₀ (4)；upz (2)；Ωt (5)；<mutual> (1)；ι (4)；ι-mono (4)；_⊞_ (2)；Dn (3)；mv (3)；mvBr (3)；mvFirst (3)；<mutual> (1)；Up (6)；Upm (9)。
- `OCF.Lean.YiRWPath`：Pth (5)；_≤_ (3)；_∙_ (5)；wk (5)；lift (3)；⊕⊑ (4)；z≤ (3)；bz⁼ (2)；<mutual> (1)；posW (3)；posW⁼ (3)；psh (5)；pshBr (5)；pshFirst (5)；<mutual> (1)；Ok (3)；OkS (4)；<mutual> (1)；Ok-at (3)；Ok-at⁼ (3)；OkOS (4)；OkO (3)；OkS⊕ (4)；Ok⊕ (3)；OkO⊕ (5)；◃→⊑ (7)；OkO↑ (7)；Ok-tw (4)；Ok-Λ (2)；from0 (3)；way (4)；cW (3)；cW-ind (4)；cW-ind₂ (4)；emb (5)；emb-mono (6)。
- `OCF.Lean.YiTBRow`：RbS (4)；Rb (3)；dW (4)；dW-ind (5)；dW-ind₂ (5)；<mutual> (1)；ψ (25)；mono (48)。
- `OCF.Lean.YiVWFGH`：FGH (6)；fghᶻ (2)。

##### L3
- `OCF.Align.BrwViewDef`：Sig (17)；module _ (1)；<open> (1)；View (7)；BrwView (3)。
- `OCF.Lean.YiRWCheck`：¬◃z (2)。
- `OCF.Lean.YiVWFGH`：FGHᵥ (5)；iter-cong (3)；FGH-val (6)。
- `OCF.Lean.YiVWVal`：chL (2)；chP (2)；chBr (2)；br0 (2)；V (5)；_⊹_ (5)；emb (5)；chT (3)；<mutual> (1)；val (6)；valCh (3)；_≼_ (7)；_≈_ (2)；≼-refl (5)；lim⁻ (4)；Ω⁻ (4)；<mutual> (1)；≼-trans (7)；sucT (4)；≈-refl (2)；≈-trans (2)；≼-suc (7)；≼⊹ (5)；⊹-mono (7)；emb-mono (8)；F≈ (2)；_◁_ (5)；⊹-mono◁ (5)；emb-mono◁ (6)；<mutual> (1)；val-mono (7)；valCh-mono₀ (3)；valCh-mono (3)；LegV (5)；⊹-leg (5)；emb-leg (6)；<mutual> (1)；val-leg (6)；valCh-leg (3)。
- `OCF.Lean.YiVWView`：<open> (1)；SigY (5)；VW (2)；chT⁻ (3)；conv (3)；conv₀ (3)；chT-β (3)；upz′ (3)；upz (2)；valCh-β (3)；val-upz′ (4)；val-upz (3)；reidx (5)；lim≡ (3)；Ω≡ (3)；mapUp (16)；view (7)；brwView (2)。
- `OCF.Lean.YiVWWf`：Part (5)；Pt (6)；part-reidx (5)；part-mapUp (7)；parts⊆ (9)；Acc (2)；<mutual> (1)；accUp (5)；accUpz (5)；wf (7)；vrec (7)；ObjStep (5)；upz-step (7)；os-reidx (5)；os-mapUp (6)；objStep (7)。

