# YiSX 树侧站间一步阶段回报：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiSXStart |
| 文件前缀 | `YiSX` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiSX 统一树运算与局部行界阶段复核” 一节 |
| 主审复核后的一句结论 | 1件独立冷编0；Φ合法及具体零步成立，一般RowBridge与Nstep未证，路线未否定。 |

## 简报原文

### 任务简报：摆脱侧：树侧的站间一步（前缀 YiSX）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十一批四路之一（选项原文 "摆脱侧：树侧的站间一步 (Recommended)"），与本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **旧的组装**（主审复核过；它的全域 Leaf 前提已被 `YiLLLeafNeg.noLeaf` 否定，所以它本身什么也没说）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- **当前的组装**（主审复核过）：`YiCNAccept.ebo-rest : LeafRest → LiftRest → LowRest → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，三族前提是沿龙骨的具体陈述（`YiCNKeel` 的 `LeafAt`、`LiftAt`、`LowAt`，分别从第 3、2、1 站起未证）。
- **共同的目标陈述**（主审 2026-11-15 在临时文件里编译通过，源码留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC3Ends.agda.txt`；正式文件里请自己重写一遍并编译）：
  ```agda
  open ExSuff gradedᵍ domsᵍ using (Keel⁻)        -- YiExSuff, YiGIInst
  Kᴱ : ℕ → Set
  Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)
  ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
  ebo-from-stations k = ≼-trans reference (l≼ (λ n → ≼-trans (k n (hs n)) (upperᴱ n)))   -- reference, hs, upperᴱ 取自 YiGIEnd
  ```
  即终点等于 "对一切 n，第 n 站（`Keel⁻.row keelᴱ n` 即 `EBOψ n`，`Keel⁻.twc keelᴱ n` 是 `EBOᶻ` 的第 n 支）的值下界"。Leaf、Lift、保持这几族律只是证它的一种办法。已知的值：`YiMTValue.k1ᶻ : Kᶻ 1`（对 `twᶻ 1`），`YiMTValue.Kᶻ n = (h : HC (E.ψ [] (E.Ωt (ΩTower n)) ∷ [])) → Rt h ≼ readRW (twᶻ n)`；`YiVTTw2Hi.tω≼twᶻ`（塔第 2 项起 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))）。`Keel⁻.twc keelᴱ n` 与 `twᶻ n` 的关系请自己核对（`keelᴱ` 的底取 `EBOᶻ` 各支实际继承的折叠）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- AGENTS 目标 "让树自足"、"树的语言"（规则的形状取自 FGH 的推广）、"攀爬与摆脱翻译要平衡"（1:1）。本路是本批的摆脱侧。
- **塔的定义**（`YiRWBlock` 第 144–146 行）：`tw (suc n) = nd (sΩ (tw n)) λ c → tw n ⊕ ↑ (tw n) c`；第 n 站的闭项是 `Ωt (tw n)` 折到第 0 层（`YiMTTab.twᶻ`，终点各支 `Keel⁻.twc keelᴱ n`）。
- **树侧现成的事实**：`YiTSStep.tree-step`（后继层号上 Ω 树的折叠按定义等于下层链的部分和极限，`refl`，不读记号）；折叠与单调互递归（`YiTBRow` 第 106 行 `mono`）；`YiTBFam.ψ-⊵`（输出不低于底）；新块上的值 `YiVWVal.val` 与 View（`YiVWView.brwView`）。
- 现在证每一站都要用记号一侧的关系族；连续几批的全域补法被否定（`noLeaf`、`no-step`、`no-frame₂`）。本路要的是：**站与站之间的那一步完全在树侧给出，记号只在末端用一次**。

#### 要做的（按序）
0. **最小检查**，在临时目录：写出一条不读记号的站间一步陈述，形如 "第 n+1 站的闭项（或它的读回）不低于对第 n 站闭项施加某个树侧运算 Φ 的结果"，Φ 由折叠与塔的构造给出（你定，说明理由）；在 n = 0 上编译它。不成立就停下回报。
1. **对一切 n**：用树侧的事实（`tree-step` 一类的定义性等式、折叠的单调）证这一步对一切 n 成立，不读记号。
2. **末端的一条记号引理**：精确写出还需要的那一条记号一侧的陈述 `Nstep`（例如 "参照值 ≥ 第 n 站的参照，推出 Φ 作用后 ≥ 第 n+1 站的参照"），编译条件链 "`Nstep` 加 `Kᴱ 0` 加站间一步 ⇒ 对一切 n 的 `Kᴱ n` ⇒ 终点"（经 `ebo-from-stations`）。
3. 在 n = 0、1 上检查 `Nstep`（用现有的记号结果）；交翻译账：Φ 用到树的哪些构造与字段，`Nstep` 读了记号的哪些东西。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiSX`（模块名 `OCF.Lean.YiSX…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiFR`、`YiS1`、`YiNL`）。树侧一步的文件若不读记号，文首标明 "不读记号"，用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包；读记号的文件标明 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库的 .agda-lib 路径>
  <cubical 的 .agda-lib 路径>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 8G**：同时最多五路在编译，机器共 64G。若某个文件确实要超过 8G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽（先在回报里说明）；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

### YiSX 完整回报（待主审独立复核）

#### 1. 判决与范围

对纲领与目标：交出一条不读记号、合法且可执行的树侧运算 Φ，以及它在第 0 站的具体值下界。没有改树、折叠、合法性或比较表。一般站间一步未走通，尚未把逐站的记号关系集中到末端一条引理；不声称树已自足或终点已达 EBO。

第 0 步通过：Φ(x) = `ψ₀ᶻ (zero ⊕ ↑ zero x) (ok↑ x) (proj₁ (Ωt (zero ⊕ ↑ zero x)))` 的树分量。先把零层输出读成层号，取该层 Ω 树再折回零层。理由是第 1 站根链的第 1 行在 n = 0 时恰给出这次运算。不是恒等运算，也没有把下一站的整棵树放进 Φ。

进度：
- 步 0：临时 `YiSX0.agda` 编译 0；首次调用发生在收到简报后约 6 分钟内，首版 42 是 `Ok (zero ⊕ ↑ zero x)` 与 `Ok (↑ zero x)` 类型不相同；按证据实际生成的层号保留 `zero ⊕` 后通过。
- 步 1：一般根第 1 行的精确形状与值上界编译通过；需要的桥精确陈述为 `RowBridge n`，只实填 0。n = 1 未证，未否定。
- 步 2：未进入。没有写出并编译 `Nstep`，没有重写 `Kᴱ` 与 `ebo-from-stations` 的正式验收文件；不以条件链冒充一般步已完成。
- 步 3：未进入 `Nstep` 的 0、1 检查。下面仍交已定义 Φ 的翻译账。

停止说明：第 0 步失败、8G 耗尽均未触发。已检查的字面展开方法与旧同层关系方法没有给出一般桥，转用值关系后也未得到 `RowBridge 1`。这是 AGENTS“连续受阻时停下来报告”口径的未走通回报；不把一次等式编译失败加旧关系的前提否定冒称为两次完整的实质重设计均类型错误，不宣称路线已否定。没有自行换 Φ 或把闭项改成未折叠的 Ω 树。

| 问题 | 精确位置 | 档 |
|---|---|---|
| Φ 是合法闭构造 | YiSXStart `ok↑`、`Φ⁺` | 编译定理 |
| 第 0 站所需不等式 | YiSXStart `step0` | 有限测试；该具体不等式有完整编译证明 |
| 一般根第 1 行 | YiSXStart `row1-shape`、`row1-bound` | 编译定理，不新增记号强度 |
| 0 站的源层号等式不能逐字推广到 1 站 | YiSXStart `source1-different` | 编译否定；仅否定所写的字面等式 |
| Φ 的结果能否由该行覆盖 | YiSXStart `RowBridge 1` | 未走通；没有否定定理 |
| 能否改由更后面的行或整条根链覆盖 | 未实现 | 判断：本回报没有穷尽证明方法 |
| `Keel⁻.twc keelᴱ n` 与 `twᶻ n` 的值桥 | YiGIInst `baseᴱ`、`betaᴱ`、`keelᴱ` | 只读定义；未证明、不把两种底混用 |

#### 2. 文件与自身冷编

唯一仓库新文件：`probes/OCF/Lean/YiSXStart.lagda.md`。

| 文件 | 非空 Agda 代码行 | 含空白 Agda 块行 | 全文件行 | 自身冷编退出码 | 最大 residency | 总内存 |
|---|---:|---:|---:|---:|---:|---:|
| YiSXStart.lagda.md | 53 | 69 | 76 | 0 | 172,410,768 bytes | 284 MiB |

统计口径包括选项、模块头、导入、签名、定义，不包括 Agda 代码块之外的文字及代码围栏。`+RTS -M8G -s -RTS`，冷编时间约 1.577 秒（并行环境中的量级）。只删除自己的 `probes/_build/2.8.0.2/agda/OCF/Lean/YiSXStart.agdai` 后冷编，依赖沿用已有接口。日志唯一 `Checking` 行是 YiSXStart 自身。

冷编命令：
```
agda +RTS -M8G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiSXStart.lagda.md > <实验目录>/YiSXStart-cold.log 2>&1
```
退出码由原 Agda 命令直接取得，没有管道。未用 `--ignore-interfaces`，没有删除共享依赖接口。

临时文件（不进仓库）：
| 文件 | 结果 | 用途 |
|---|---|---|
| YiSX0.agda | 0 | 第 0 步，最先编译的试验 |
| YiSXRowGeneral.agda | 42 | 尝试把第 0 站的根第 1 行字面等式推广到一般 n |
| YiSXBranch.agda | 0 | 一般实际行、RowBridge 0、源层号不相等的前置试验 |
| YiSXLePrecheck.agda | 0 | 引用既有 β-not，检查旧同层关系的规范前提不能全塔实填 |

#### 3. 定理与构造表（陈述逐字）

以下 `V` 是 `OCF.Lean.YiVWVal`：它给树跨层的序数值前序，不读取记号。

`ok↑`：
```agda
ok↑ : (x : Tr zero) → Ok (zero ⊕ ↑ zero x)
```
白话：任意零层树读成的层号带着块自己的合法性证据。编译定理，YiSXStart。

`Φ⁺`：
```agda
Φ⁺ : Tr zero → Tr⁺ zero
```
白话：Φ 的结果是带非零证据的零层树，定义没有额外假设。编译构造，YiSXStart。

`row1-shape`：
```agda
row1-shape : (n : ℕ) → head (twᶻ (suc n)) 1 ≡ twᶻ n + rowValue n
```
白话：下一站根的第 1 个部分和由前站和实际的第 1 行组成。编译定理，YiSXStart；依据 YiMTKeel 的 `rowσᶻ` 重写为精确树等式。

`row1-bound`：
```agda
row1-bound : (n : ℕ) → V.val zero (rowValue n) V.≼ V.val zero (twᶻ (suc n))
```
白话：实际第 1 行的值不高于下一站。编译定理，YiSXStart；这是现成第 1 行下界的干净值载体版本，不声称新增强度。

`bridge0`：
```agda
bridge0 : RowBridge 0
```
其中定义逐字是：
```agda
RowBridge : ℕ → Set
RowBridge n = V.val zero (Φ (twᶻ n)) V.≼ V.val zero (rowValue n)
```
白话：在第 0 站，Φ 的结果正好是实际第 1 行。有限测试，具体证明编译通过，YiSXStart。

`step-from-row`：
```agda
step-from-row : ∀ n → RowBridge n
  → V.val zero (Φ (twᶻ n)) V.≼ V.val zero (twᶻ (suc n))
```
白话：若 Φ 的结果由实际第 1 行覆盖，则所需站间一步成立。编译条件定理；条件在 0 有 `bridge0` 实例，在 1 未填，不能读作全塔一步。

`step0`：
```agda
step0 : V.val zero (Φ (twᶻ 0)) V.≼ V.val zero (twᶻ 1)
```
白话：第 0 步通过。有限测试，具体值不等式有完整编译证明，YiSXStart。

`source0`：
```agda
source0 : zero ⊕ ↑ zero (twᶻ 0) ≡ rowLevel 0
```
白话：第 0 站的 Φ 源层号与实际第 1 行源层号字面相等。有限测试，编译证明，YiSXStart。

`source1-different`：
```agda
source1-different : zero ⊕ ↑ zero (twᶻ 1) ≡ rowLevel 1 → ⊥
```
白话：同一源层号等式在第 1 站不成立：左边根形状是 ℕ 极限，右边根形状是 Ω 形状。编译否定，YiSXStart。它没有折叠值比较，不否定 `RowBridge 1`、目标站间一步或 YiSX 路线。

临时 `no-canonical-Le`：
```agda
CanonicalLe : Set
CanonicalLe = ∀ n → Can (tw n) (proj₁ (Ωt (tw n)))
no-canonical-Le : CanonicalLe → ⊥
```
白话：用旧 `YiVRRel` 的同层自相关要求覆盖原 Ω 树的全塔规范实例不可满足；直接调用 `β-not (h 1)`。编译定理，临时 YiSXLePrecheck，不进仓库，不是新数学结果。未把这条否定归到壁垒或值墙。

#### 4. 第一个障碍与已检查的方法

首个未证引理是 `RowBridge 1`，不是 `row1-bound`，也不是终点的上确界组装。

实际第 1 行由：
```agda
selfPoint n = proj₁ (ψ (tw n) (Ok-tw n) (rbᶻ (tw n)) (B₀ (tw n)) (tw n) self
                      (Ωt (tw n)) (proj₁ (Ωt (tw n))))
rowLevel n = tw n ⊕ ↑ (tw n) (selfPoint n)
```
给出。Φ 的层号则是 `zero ⊕ ↑ zero (twᶻ n)`。n = 0 时自折叠和零层折叠相同；n = 1 时上述字面源层号等式已经被 `source1-different` 否定。因此不能把第 0 步的 `refl` 当作一般证明。

检查过的另一方法是旧同层模拟 `YiVRRel.Le` 与 `YiVRFold.fl`。逐条读了定义与陈述：`fl` 是 `YiRWFold` 的保持定理，不是当前 `YiTBRow`；它固定来源层号与目标，不能直接给跨目标的读回比较。原 Ω 树还需自身规范性，而 `β-not` 已在 `tw 1` 否定这点。临时文件把该前提不可全塔实填重新实例化编译。这里只排除直接套用这份旧接口，不说明不存在另一种关系。

改用 `YiVWVal` 后，源层号不同本身不妨碍在同一零层值类型比较；但还需构造 `RowBridge 1` 的值推导。现有 `YiTBRow.mono` 固定来源层、底、路径及目标，其陈述没有跨目标的字段。没有把“找不到现成引理”当成否定；也没有以相似形状归到 W、V、C 或 `obs→dec`。

#### 5. 翻译账、审计、偏离与事故

Φ 用到的树构造与字段：零层树的 `↑` 读回；字面的左加零；`OkO↑` 与 `Ok⊕` 给层号合法性；`Ωt` 的逐构造子定义；`ψ₀ᶻ` 的零目标路径、默认底 `B₀`、起点 `Ωt zero`、最小比较表 `rbᶻ`；最后取非零树的第一投影。没有新节点或新字段，没有按记号基本列细规则派发，没有第 4 层逼出对前 3 层的修改。

实际行额外使用第 n 层自身目标的折叠 `selfPoint`；它并非前站的零层输出。这正是本回报保留的缺口，不把二者重新命名成同一个对象。

`Nstep` 尚未定义，所以不能列它读取了哪些记号；不能把“尚未读记号”记成已完成末端出口。Φ 的引用闭包干净并不说明树已自足，也不抹掉上游定义的研究来源。

审计：
- `python3 probes/Survey/scripts/importclosure.py OCF.Lean.YiSXStart` 退出 0；未加 `--only`。闭包 16 个模块，本地 8、库 8；禁用表命中 0。8 个本地模块为 YiRWBlock、YiRWOps、YiRWPath、YiRWFold、YiTBRow、YiMTTab、YiVWVal、YiSXStart。
- 新仓库文件源码检索公设、洞、停机/正性绕过、trustMe、额外 cubical、irrelevant-projections、本机路径，全部为 0。没有 Funext 前提。
- 没有 HTML、定义切片或依赖图结果可交；没有以失败编译生成的结果作审计依据。
- 只新增 YiSXStart；未改任何既有定义、其他前缀、src、archive、README、LOG、台账、留档。没有提交、推送、装包、pkill。

偏离与事故：
1. `ok↑` 首版写成 `Ok (↑ zero x)`，实际证据类型是 `Ok (zero ⊕ ↑ zero x)`；一次 42 后保留字面前缀修正。不是否定结果，不是库配置问题。
2. 泛化第 0 站等式的试验 42，首错误 `tw n != zero of type L`；之后用新文件的否定 `source1-different` 精确说明该字面等式在 1 失败，不把编译失败本身当否定。
3. 手册 §4 首次读取覆盖 §4.1–§4.5，§4.6 在结束前补读；这未完全遵守“先读第 4 节”的顺序要求，特此记录。全部编译均按 8G、单进程、私有日志执行。
4. 未触发堆耗尽、超时或 Agda 内部错误。

没有读、只凭简报转述的内容：YiCNAccept、YiCNKeel、YiLLLeafNeg.noLeaf、YiAbsObs 的整族否定、Barrier 的完整证明、SelfCheck-SC3Ends 附件、源 BTBO 全文。它们未被新文件导入，未用作新结论的证明。YiGIEnd、YiGIInst 与 YiExSuff 的相关定义已读，但没有重编这些旧模块，不宣称独立复核它们。YiVTTw2Hi 只检索了签名，没有沿其完整证明复核，不用它证明本回报的结论。

待主审独立复核后，本文件中的仓库编译事实才计入项目交付；路线总体仍为一般步未走通。
