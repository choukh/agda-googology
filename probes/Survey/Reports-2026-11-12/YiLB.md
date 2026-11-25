# YiLB 文献驱动的实际链验收不变量：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiLBStart、Inv、Actual |
| 文件前缀 | `YiLB` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiLB 实际链NF/G与值不变量初项复核” 一节 |
| 主审复核后的一句结论 | 3件独立冷编0；精确NF/G、初项及旧区间、非零层辅助不变量；增长新区间和FirstMissing未证。 |

## 简报原文

### 任务简报：文献驱动的验收不变量：按标准形与 G 集攻第 3 站的缺口（数学，记号一侧）（前缀 YiLB）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十三批（选项原文 "现在派，与 YiMS 并行 (Recommended)"）。作者的问题："我们现在遇到的困难，是不是几乎都是序数分析的困难？但是序数分析在 EBO这个高度下早就完成了呀，能否参考那边的成果来给我们这边加速呢？" 本路用文献里现成的记号一侧的不变量（标准形与 G 集，Buchholz 1986 的封闭引理）组织验收，与在跑的 YiMS（同样攻这一条，方法不同）并行作对照，在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **终点归结为各站的值下界**（编译定理）：`YiS1Accept.Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)`，`YiS1Accept.ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`。各行的参照：第 1 站 ψ₀(Ω₁)，第 2 站 ψ₀(Ω_Ω)，第 3 站 ψ₀(Ω_{Ω_Ω})。第 0、1、2 站在实际底上已成立（`YiFRStations.k0`、`k1`、`k2`；第 1、2 站由已有的 BTBO 下界得到）。已知的无条件终点值是 ψ₀(Ω_Ω+ψ₁(Ω_ω))，低于第 3 站的参照。
- **站间归约**（`YiFRStep`，先读定义的独立审查交的，编译过）：`module Step (n : ℕ)` 里 `ℓ = tw (suc n)`，`k = tw n`，`child c = k ⊕ ↑ k c`，`g c` 是孩子 c 处的 Ω 树，`feed c` 是 `g c` 经路径 `ink self` 折到槽位层 k 的输出，`chain = iter feed zero`（实际回灌链，住在槽位层 `tw n` 上），`out c` 是 `g c` 折到第 0 层的输出（`baseᴱ (suc n)`、`betaᴱ (suc n)` 是终点第 n+1 支实际继承的底与起点）；`branch-upper`：每个链点的输出不高于第 n+1 支；`step : Kᴱ n → Tail → Kᴱ (suc n)`，`Tail = (m : ℕ) → Σ ℕ λ q → (h : HC (E.fsn (row (suc n)) (suc m))) → tree h ≼ readRW (proj₁ (out (chain q)))`。
- **第一个缺口**（`YiFRStep` 末尾，逐字）：
  ```agda
  FirstMissing = Σ ℕ λ q → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
    → SI.E.tree h ≼ K.readRW (proj₁ (Step.out 2 (Step.chain 2 q)))
  ```
  主审用一个故意失败的等式让检查器展开了左边那一项（留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC4Row.agda.txt`）：`E.fsn (row 3) 1` 是 `E.ψ [] (E.fsT Ω_{Ω_Ω} (E.γT Ω_{Ω_Ω} [] 1)) ∷ []`，其中 Ω_{Ω_Ω} 写作 `E.ψ (E.ψ (E.ψ (E.ψ [] [] ∷ []) [] ∷ []) [] ∷ []) [] ∷ []`。这正是很早就卡住的 "K(2) 第 1 行"（`YiMTValue.K2-redᶻ`、`YiKQSuff.K2` 都停在这里）。
- **先验教训**（这几批编译的否定）：凡写成 "对一类对象全称成立" 的保持律都被否定了（`YiLLLeafNeg.noLeaf`、`YiSUNeg.no-step`、`YiGTIndexNeg.no-frame₂`、`YiMXNeg.¬Exit′` 等）；正面结果都是对实际对象的直接构造（`YiS1Low.folded¹`、`YiCNTw1.leaf-tw1`、`YiPJQ.qω+1`）。本路只对实际的链点与实际的那一项陈述，不写全域律。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（另见上面的共同陈述）
- **文献的状态**（`probes/Survey/OrdinalNotationsGuide.md` §1、§5.2、§5.3，先读这三节）：koteitan/googology-lean 的 `ExBuchholz`（Lean，`6da2de5`，MIT，经典逻辑，依赖 mathlib）机检了 EBO 记号的标准形封闭（`OTFS_thm`）、基本列递减与单调、共尾、秩等于值、到 C₀(Λ) 的同构、良基；核心是 Buchholz 1986 的引理 3.3 至 3.6 与 G 集的界（论文链接在手册 §9）。手册的判断：它的项、序、基本列与我们的 `EBO` 逐项相同（读码与转写测试，未形式证明），§5.3 有字典（例如 `γT` 对 `tower`，`fsn` 对 `fs t (numeral n)`，`fsT` 对 `fs a η`）。
- **仓库里已经移植的**（先用这些，再看 Lean）：
  - `OCF/Align/EboLeanBase`：序的句法事实，标准形 `NF`，G 集的成员关系 `InG`，可数项 `Ctbl`；
  - `OCF/Align/EboLeanClosure`：Buchholz 3.3、3.6 的 ω 部分（`hZ0`、`tow` γ 链不变量、`Tω`、`NFω`、`cl-fsn-NF`、`trian-fsn`）；
  - `OCF/Align/WfFsnClosure`：含 Ω 基本列部分（`cl-fsT`、`trian-fsT`），文首写明蓝本是 Lean 的 `towerOT_of_Bachmann`、`Trian_fs_aux`、`OTFS_aux`、`OTFS_thm`；
  - `OCF/Align/Bachmann`：Bachmann 性质；当年的标签路线（要求基本列逐项一致）在 γ₂ 处撞过墙，原因写在文首。本路只要下界，请判断那堵墙对下界是否有影响。
  - 出口与单调：`YiCFMono.mono≤ⁿ`（要标准形与可数）、`YiNFOCond.mono≤ᶜ`、`YiCFCofin.cofin`；`YiMXNote.¬Mono` 说明不要求标准形时项序推不出值序，与文献一致。
- 主审的判断（未编译）：文献里所有比较与基本列的引理都只对标准形成立，标准形的条件是 G 集低于参数；我们前几批自造的关系族失败的样子正是这类条件被丢掉时会出的问题。`FirstMissing` 的实质很可能是 "目标项是标准形，它的 G 分量受控，所以落在实际回灌链已经生成的部分里"。

#### 要做的（按序）
0. **最小检查**，在临时目录：证明目标项 `E.fsn (row 3) 1` 是标准形（用 `cl-fsn-NF` 或 `cl-fsT` 一类），并写出它的 G 分量（`InG`）与 γ 链的结构（`tow`）；同时展开 `Step.chain 2 0`、`Step.chain 2 1`。确认要比较的东西都有定义、证书都存在。不成立就停下回报。
1. **写出文献式的不变量**，只对实际的链点陈述：例如 "第 q 个链点的输出支配一切满足某个 G 集条件（相对第 q 个链点的某个读法）且低于某个界的标准形项"。条件取自 Buchholz 的封闭引理，你定具体形状，说明对应文献的哪一条。
2. **不变量的一步**：证明从第 q 个链点到第 q+1 个链点不变量保持，用文献引理（已移植的优先；缺的照 `ExBuchholz` 的证明移植，文首写明来源与行号）加上我们折叠的定义性展开。
3. **推出缺口**：由不变量得到 `FirstMissing`；再尝试 `Tail 2`（一切 m），从而得到第 3 站的值下界。做不到就交第一个挡住的引理，并说明它在文献里对应哪一条、文献的证明为什么不能直接搬。
4. **翻译账**：本路的不变量全部来自文献的哪几条；它只用在验收一侧，不改树、折叠、合法性。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiLB`（模块名 `OCF.Lean.YiLB…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiNL`、`YiXV`、`YiMS`、`YiFN`、`YiSL`）。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库目录>/standard-library.agda-lib
  <Cubical库目录>/cubical.agda-lib
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 8G**：同时最多六路在编译，机器共 64G。若某个文件确实要超过 8G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
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

### YiLB 完整回报（第五十三批，冻结待根审）

#### 1. 判决与原顺序

对纲领与目标：本轮只在验收侧使用记号。树、折叠、合法性、闭项及其证书均没有改动；没有新增序数值下界，不能称为树自足。第3站 ψ₀(Ω_{Ω_Ω})、FirstMissing、Tail 2 均未证。本轮不是路线否定。

第0步成立：指定目标 `target = E.fsn (Keel⁻.row keelᴱ 3) 1` 的标准形、参照证书、G₀ 精确成员及文献 γ 链结构均有编译定理；原 Step.chain 2 的前两点和非零证书也通过。`target` 的 G₀ 恰为 `{arg, ΩTower 2, []}`（含三个实际成员见证），其中 `arg = Ωt (Ωt (EBOψ 2))`、`ΩTower 2` 是 Ω_Ω。它们不是对若干随机项的测试。

第1步分两部分：值不变量 `YiLBInv.Inv` 只量化实际第 q 个输出下的标准主项，其条件是 NF a、G₀(a)<a、a≤param q；`param q = Ω²γ_q`。初项 `inv0` 已实填，`sample-band` 证明第1步目标的全部前提可满足且在旧参数界以上。辅助不变量 `YiLBActual.ActualInv` 把文献 NF/G 与实际链点、原 g 的非零层 R（验收关系）合在一起，全部 q 已实填。

第2步：`ActualInv` 的一步 `actual-step` 已编译；证明是从同一个实际槽位底重新构造下一点，甚至有 `chain-gamma q r` 与 `g-gamma q r` 的两个独立自然数参数。它不使用前一点作为归纳假设，也不证明实际值递增。值不变量的增长一步 `InvStep` 未实填；它是本轮未走通的部分。

第3步：没有 FirstMissing，故按原顺序未进一步尝试 Tail 2。`step→first` 仅是前提未填的条件出口，不算新增强度。根据原简报“做不到就交第一个挡住的引理”交付 §4 的具体义务；不把未走通写成否定。

| 问题 | 位置 | 档与结论 |
|---|---|---|
| 目标 NF/G、参照证书是否存在 | YiLBStart.nf-target/target-G/hc-target | 编译定理，存在 |
| 是否用原实际链、原底、原起点 | YiLBStart.chain1-self；YiLBActual.out-child | 编译定理，逐字展开原定义 |
| 实际链上的 NF/G/非零层关系是否能实填一步 | YiLBActual.actual/actual-step | 编译定理，能；无零层值结论 |
| 值不变量初项、旧区间是否成立 | YiLBInv.inv0/old-part | 编译定理，成立 |
| 目标是否处在旧区间以上、前提是否非空 | YiLBInv.sample-band | 编译定理，严格在其上且有实例 |
| 实际 out 对新区间的值支配 | §4 missing-child-low₁ | 未证义务；判断：已有 NF/G 引理尚未给出该接线 |
| FirstMissing / Tail 2 | 原 YiFRStep | 未走通；不是否定 |

#### 2. 文件、冷编与审计

仅新增下表三个文件，均在 `probes/OCF/Lean/`，均为验收文件。代码行按唯一 agda 代码块计，含空行；总代码 251 行。冷编逐件删除字面路径 `probes/_build/2.8.0.2/agda/OCF/Lean/YiLB*.agdai` 中对应自身的那一个接口，再从仓库根编译；没有删共享依赖或使用 ignore-interfaces。这里的星号是回报中的概括，实际命令均写各自字面路径。

命令均为 `timeout 600 agda +RTS -M8G -s -RTS --library-file=<实验目录>/libraries -i src -i probes <文件>`，退出码直接记录，未经管道。三个最终日志各只有自身模块的一条 Checking，无 warning、error 或 Heap exhausted。数字为 RTS maximum residency 与 total memory in use，不是进程 RSS；并行环境下用时只作工程记录。

| 文件 | 代码 / 总行 | 冷编退出码 | RTS 最大驻留 | RTS 总内存使用 | 用时 | 私有日志 |
|---|---:|---:|---:|---:|---:|---|
| `YiLBStart` | 92 / 98 | 0 | 1,651,274,832 bytes | 2904 MiB | 15.828 s | `cold-start.log` |
| `YiLBInv` | 91 / 97 | 0 | 1,676,969,104 bytes | 2959 MiB | 15.808 s | `cold-invariant.log` |
| `YiLBActual` | 68 / 74 | 0 | 1,481,135,320 bytes | 2548 MiB | 16.348 s | `cold-actual.log` |

完整机器记录在 `cold-metrics.json`。源码禁用构造、洞、K 选项、irrelevant-projections、完整 cubical 选项与本机路径检索均为0；没有函数外延前提。未提交、未推送。没有改 src/archive、已有数学文件、其它路线前缀、README、LOG、台账或留档。

首次临时文件 `YiLBCheck.agda` 在 2026-11-15 11:33:13 +0800 写出并启动编译，初次作用域错误42；11:34 的 check2 退出0。私有目录创建于11:31:55，满足30分钟内首次写出并编译的要求。

#### 3. 定理表（逐字签名）

签名中的短名与源码一致。`FR = YiFRStep`、`GI = YiGIInst`、`GR = YiGIRel`、`SI = YiAbsSimInst`、`K = YiKVRel`、`V = EboLeanView`。`w` 是 ΩTower 3 的 cΩ [] 视图。`Inv` 与 `ActualInv` 的定义见源码，前者含值比较，后者不含。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `nf-row3` | `nf-row3 : NF row3` | 第3站参照项是标准形。 | `YiLBStart` | 编译定理 |
| `nf-target` | `nf-target : NF target` | 指定的第1行目标是标准形。 | `YiLBStart` | 编译定理 |
| `target-form` | `target-form : target ≡ E.ψ [] arg ∷ []` | 目标恰为 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})。 | `YiLBStart` | 编译定理 |
| `gamma0` | `gamma0 : V.γ w 0 ≡ E.ΩTower 0` | 文献 γ 链的初项是1。 | `YiLBStart` | 编译定理 |
| `gamma1` | `gamma1 : V.γ w 1 ≡ r2` | 文献 γ 链的第1项是第2站参照。 | `YiLBStart` | 编译定理 |
| `gamma-NF-G` | `gamma-NF-G : ∀ q → NF (V.γ w q) × GB [] (V.γ w q) (V.fΩ w (V.γ w q))` | 每个文献 γ 项均标准，且其 G₀ 分量低于对应参数。 | `YiLBStart` | 编译定理 |
| `gamma-G` | `gamma-G : ∀ {z} → InG [] z r2 → (z ≡ E.ΩTower 2) ⊎ (z ≡ [])` | γ₁ 的 G₀ 分量只可能是 Ω_Ω 或零。 | `YiLBStart` | 编译定理 |
| `arg-G` | `arg-G : ∀ {z} → InG [] z arg → (z ≡ E.ΩTower 2) ⊎ (z ≡ [])` | 目标参数的 G₀ 分量只可能是 Ω_Ω 或零。 | `YiLBStart` | 编译定理 |
| `target-G` | `target-G : ∀ {z} → InG [] z target → (z ≡ arg) ⊎ (z ≡ E.ΩTower 2) ⊎ (z ≡ [])` | 目标的 G₀ 分量只可能是参数、Ω_Ω、零。 | `YiLBStart` | 编译定理 |
| `hc-target` | `hc-target : SI.E.HC target` | 目标有遗传可数参照证书。 | `YiLBStart` | 编译定理 |
| `chain0` | `chain0 : Step.chain 2 0 ≡ B.zero` | 原实际链第0点为零。 | `YiLBStart` | 编译定理 |
| `g0` | `g0 : Step.g 2 B.zero ≡ proj₁ (O.upz {s = B.sΩ (B.tw 2)} {h = Step.child 2} B.zero (O.Ωt (B.tw 2)))` | 原 g 在零处确为孩子0的 Ω 树嵌入。 | `YiLBStart` | 编译定理 |
| `chain1` | `chain1 : Step.chain 2 1 ≡ proj₁ (TB.ψ (B.tw 3) (P.Ok-tw 3) (MT.rbᶻ (B.tw 3)) (GI.baseᴱ 3) (B.tw 2) (P.ink P.self) (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)) (proj₁ (O.upz {s = B.sΩ (B.tw 2)} {h = Step.child 2} B.zero (O.Ωt (B.tw 2)))))` | 原实际链第1点展开为原 feed 在零处的折叠。 | `YiLBStart` | 编译定理 |
| `chain1-nz` | `chain1-nz : B.tw 2 B.⊢ B.zero ◃ Step.chain 2 1` | 第1链点有非零证书。 | `YiLBStart` | 编译定理 |
| `out-nz` | `out-nz : ∀ q → B.zero B.⊢ B.zero ◃ proj₁ (Step.out 2 (Step.chain 2 q))` | 每个实际输出有非零证书。 | `YiLBStart` | 编译定理 |
| `arg∈G` | `arg∈G : InG [] arg target` | 参数确实是目标的 G₀ 成员。 | `YiLBStart` | 编译定理 |
| `tower∈G` | `tower∈G : InG [] (E.ΩTower 2) target` | Ω_Ω 确实是目标的 G₀ 成员。 | `YiLBStart` | 编译定理 |
| `zero∈G` | `zero∈G : InG [] [] target` | 零确实是目标的 G₀ 成员。 | `YiLBStart` | 编译定理 |
| `chain1-self` | `chain1-self : Step.chain 2 1 ≡ proj₁ (TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (λ i u → GI.baseᴱ 3 i (P.inc B.zero u)) (B.tw 2) P.self (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)) (proj₁ (O.Ωt (B.tw 2))))` | 第1链点展开到 tw2 上的自身折叠，底仍为继承底。 | `YiLBStart` | 编译定理 |
| `ref-eq` | `ref-eq : ∀ q → E.fsn (E.EBOψ 3) q ≡ ref q` | 文献参数给出的参照逐项等于原第3站基本列。 | `YiLBInv` | 编译定理 |
| `ref-NF` | `ref-NF : ∀ q → NF (ref q)` | 每个该参照是标准形。 | `YiLBInv` | 编译定理 |
| `ref-param-NF` | `ref-param-NF : ∀ q → NF (param q)` | 每个参照参数是标准形。 | `YiLBInv` | 编译定理 |
| `ref-param-G` | `ref-param-G : ∀ q → GB [] (param q) (param q)` | 每个参照参数满足 G₀(a)<a。 | `YiLBInv` | 编译定理 |
| `ref-HC` | `ref-HC : ∀ q → SI.E.HC (ref q)` | 每个参照具有证书，封入 opaque 避免求值。 | `YiLBInv` | 编译定理 |
| `beta3` | `beta3 : proj₁ (GI.betaᴱ 3) ≡ Keel⁻.twc GI.keelᴱ 2` | 第3支继承起点字面上是第2支闭项。 | `YiLBInv` | 编译定理 |
| `from⊴` | `from⊴ : ∀ {x y : B.Tr B.zero} → x K.⊴ y → K.readRW x ≼ K.readRW y` | 零层第一位置的非严格关系给值序。 | `YiLBInv` | 编译定理 |
| `floor` | `floor : ∀ q → (h : SI.E.HC (ref 0)) → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 q)))` | 每个实际输出都保住原第2站的值下界。 | `YiLBInv` | 编译定理 |
| `old-part` | `old-part : ∀ q → (a : E.T) → NF a → GB [] a a → a ≤ᵀ param 0 → (h : SI.E.HC (E.ψ [] a ∷ [])) → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 q)))` | 旧参数区间内的全部标准主项在每个实际输出下方。 | `YiLBInv` | 编译定理 |
| `initial` | `initial : SI.E.HC (ref 0) → Inv 0` | 给定非空的初项参照证书，初项值不变量成立。 | `YiLBInv` | 编译定理 |
| `inv0` | `inv0 : Inv 0` | 初项值不变量无条件实填。 | `YiLBInv` | 编译定理 |
| `sample` | `sample : NF (param 1) × GB [] (param 1) (param 1) × (param 1 ≤ᵀ param 1) × SI.E.HC (ref 1)` | 新区间顶端的 NF/G/界/证书前提均有实例。 | `YiLBInv` | 编译定理 |
| `pointwise` | `pointwise : ∀ q → Inv q → (h : SI.E.HC (ref q)) → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 q)))` | 值不变量可取其闭区间顶点。 | `YiLBInv` | 编译定理 |
| `sample-band` | `sample-band : NF (param 1) × GB [] (param 1) (param 1) × (param 0 E.<ᵀ param 1) × (param 1 ≤ᵀ param 1) × SI.E.HC (ref 1)` | 目标参数严格越过旧参数界；新区间域确实非空。 | `YiLBInv` | 编译定理 |
| `step→first` | `step→first : InvStep → FR.FirstMissing` | 若值不变量的增长一步实填，便有 FirstMissing；此前提未填。 | `YiLBInv` | 编译定理 |
| `rd-gamma` | `rd-gamma : ∀ q → GR.Rd (B.tw 2) (V.γ w q)` | 文献 γ 项可在实际 tw2 层号中读出。 | `YiLBActual` | 编译定理 |
| `leaf-gamma` | `leaf-gamma : ∀ q → GR.R (B.tw 2) (E.Ωt (V.γ w q)) (proj₁ (O.Ωt (B.tw 2)))` | 实际 tw2 的 Ω 树具有 Ωγ 关系。 | `YiLBActual` | 编译定理 |
| `slot-gamma` | `slot-gamma : ∀ q → GR.R (B.tw 2) (E.Ωt (V.γ w q)) (proj₁ (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)))` | 继承槽位底具有同一 Ωγ 关系。 | `YiLBActual` | 编译定理 |
| `chain-gamma` | `chain-gamma : ∀ q r → GR.R (B.tw 2) (E.Ωt (V.γ w r)) (FR.Step.chain 2 (suc q))` | 每个正链点对每个文献 γ 项均具有 Ωγ 关系。 | `YiLBActual` | 编译定理 |
| `child-gamma` | `child-gamma : ∀ q r → GR.R (FR.Step.child 2 (FR.Step.chain 2 (suc q))) (V.fΩ w (V.γ w r)) (proj₁ (O.Ωt (FR.Step.child 2 (FR.Step.chain 2 (suc q)))))` | 原实际孩子的 Ω 树具有 Ω²γ 关系。 | `YiLBActual` | 编译定理 |
| `g-gamma` | `g-gamma : ∀ q r → GR.R (B.tw 3) (V.fΩ w (V.γ w r)) (FR.Step.g 2 (FR.Step.chain 2 (suc q)))` | 原 g 具有对应 Ω²γ 关系。 | `YiLBActual` | 编译定理 |
| `out-child` | `out-child : ∀ q → FR.Step.out 2 (FR.Step.chain 2 q) ≡ TB.ψ (FR.Step.child 2 (FR.Step.chain 2 q)) (proj₂ (P.Ok-tw 3) (FR.Step.chain 2 q)) (MT.rbᶻ (FR.Step.child 2 (FR.Step.chain 2 q))) (λ i u → GI.baseᴱ 3 i (P.inc (FR.Step.chain 2 q) u)) B.zero (P.z≤ (FR.Step.child 2 (FR.Step.chain 2 q))) (GI.betaᴱ 3) (proj₁ (O.Ωt (FR.Step.child 2 (FR.Step.chain 2 q))))` | 原 out 展开成同一实际孩子上的零层折叠，底和起点逐字保留。 | `YiLBActual` | 编译定理 |
| `actual` | `actual : ∀ q → ActualInv q` | NF/G 和上述非零层关系合成实际辅助不变量。 | `YiLBActual` | 编译定理 |
| `actual-step` | `actual-step : ∀ q → ActualInv q → ActualInv (suc q)` | 辅助不变量下一步可直接重新实填；不含输出值保持。 | `YiLBActual` | 编译定理 |

`InvStep = ∀ q → Inv q → Inv (suc q)` 仅为编译过的命题定义，没有构造。`step→first` 的前提是否成立正是未完成的目标，不能把这个条件定理当可应用的接口。`initial` 的 HC 前提由 ref-HC 0 实填；inv0 已调用。NF/G/参数界及 HC 的条件并不矛盾，sample 与 sample-band 给了目标项本身的实例。

#### 4. 第一个障碍：实际孩子 Ω 树的零层值接线

令 `c₁ = FR.Step.chain 2 1`、`h₁ = FR.Step.child 2 c₁`。第一个尚未写出的引理是下面的具体闭对象命题（这里只报告待证陈述，不把它当公设或定理写进源码）：

```agda
missing-child-low₁ :
  (h : SI.E.HC (E.fsn (Keel⁻.row GI.keelᴱ 3) 1)) →
  SI.E.tree h ≼ K.readRW (proj₁
    (TB.ψ h₁ (proj₂ (P.Ok-tw 3) c₁) (MT.rbᶻ h₁)
      (λ i u → GI.baseᴱ 3 i (P.inc c₁ u))
      B.zero (P.z≤ h₁) (GI.betaᴱ 3)
      (proj₁ (O.Ωt h₁))))
```

`YiLBActual.out-child 1` 把这个右端与原 `Step.out 2 (Step.chain 2 1)` 逐字接上。若有此引理，FirstMissing 见证就是1。这里未声称其不成立，也未把固定见证1的义务当成整个存在性命题的必要条件。

这一步的可用输入已经具体实填：`child-gamma 0 1` 给同一 h₁ 上的 Ω 树对目标参数 arg 的非零层 R；`g-gamma 0 1` 给原 g 的 R；`sample-band` 给 arg 的 NF、G₀(arg)<arg、旧界<arg 与目标 HC。缺的结论是该具体下折的值下界。没有用一般合法树上的保持律替换这条实际义务。

文献对应：直接读过的 [Buchholz 1986，pp.205–206，3.3–3.6](https://epub.ub.uni-muenchen.de/3841/1/3841.pdf) 证明记号基本列封闭及相对 G 界。直接核过的 [ExBuchholz@6da2de5 Closure.lean:1554–1633](https://github.com/koteitan/googology-lean/blob/6da2de5/Googology/Notation/ExBuchholz/Closure.lean#L1554) 的 towerOT_of_Bachmann，后继步使用 h33B/h36B 产出 NF/G；3.4 对应同文件359–400的 G_lt_of_Trian/Trian.G_lt。本轮用的 tow 与 cl-fsn-NF 已包含这些记号侧内容。原论文的下标范围与 EBO 不同，未照抄其绝对界；复用的是仓库已移植、含相对 SubBound 的版本。

判断：missing-child-low₁ 不是尚缺一条可照搬的上述文献引理，而是文献记号推导到原树折叠的模拟接线。文献没有 YiTBRow.ψ、实际 baseᴱ/betaᴱ 或 readRW，因此其 NF/G 输出本身没有实际 out 的值结论。本轮未完成这条接线。主审补充的 sem→M⁰/of⁰/ex-of⁰ 已检索；有有效值比较后可复用，不是本轮另开出口理论的理由。

对旧 Bachmann 文首 γ₂ 墙的判断：本轮没有要求 Lab 逐项一致；采用的一般 NF 上，所有 γ_q 与指定目标的标准形都已编译。旧窄域标签路线的失败不是本轮第0步失败的依据；这里也没有证明一条关于所有下界路线的“不受影响”定理。

#### 5. 翻译账、候选与未走通的办法

- 文献输入：NF 的 G 条件；3.3/3.6 的基本列封闭；第二塔不变量 tow；γ< 的下标界。它们全部留在验收文件，不进入树、折叠、合法性或闭项证书定义。
- 值候选 Inv：只量化实际输出下的标准主项，前提 NF a、GB [] a a、a≤Ω²γ_q。初项与旧参数区间完成；增长新区间未走通。不能把 InvStep 条件出口写成新强度。
- 辅助候选 ActualInv：NF/G 加实际 chain(suc q) 的 Ωγ 关系及 g 的 Ω²γ 关系。该候选对全部 q 有构造，一步也有构造，但没有输出值字段。因此不取代 Inv、不代替 FirstMissing。
- 未用新链、标准 B₀ 链或其它起点冒充实际链。证明里 F.B₀ Λ 只出现在原 baseᴱ 3 的定义性展开内部；实际折叠参数仍为继承 baseᴱ 3/betaᴱ 3。没有把已有下界用作上界。
- 未写全域 LowKeep、SlotIndex、所有孩子的同步定理，也未把已有各类否定归到本路。没有编译的路线否定，结论只写未走通。
- 需由根审记录的想法：上述两个候选、实际每个正链点对全部 γ_r 的 Ωγ 关系、固定孩子1的零层下折义务；本路不改 IdeaLedger。

#### 6. 偏离与工程事故

根审三件冷编后要求去除 initial 与 old-part 的重复核心。本次仅重排 YiLBInv 中 floor/old-part 的位置，保留 initial 原签名，改为 `initial _ = old-part 0`；inv0 仍为其闭实例。所有外部陈述及值/非零层边界不变；Start/Actual 的源码哈希保持。只重冷编 Inv，退出0、仅自身 Checking、无警告。总代码由255行减为251行。

没有数学改题或改定义。Inv0 的第一次写法省略了 γT/γ 的运输，42 后改用已有 fω-eq；早期有作用域导入及私有脚本替换签名的普通42错误，都未当成数学否定。

工程中两处大归约：第一次直接比较具体 HC，输入中断后旧会话最终确认退出130，改为 opaque 参照与对证书变量证明后通过。中断返回仍携 session_id 时曾启动替代检查，启动前没有先收到退出确认，不能据此声称严格验证了该瞬间的一进程纪律；随后进程快照未见同时存活的两个 YiLB Agda。第二次在具体 ψ-⊵ 上 with，RSS 约8.3GiB、尚无251或 Heap exhausted；输入中断未及时结束后，精确 TERM 自身 PID 42432，后改为对变量的 from⊴ 辅助函数，16秒通过。只终止自身进程，没有 pkill 或操作其它路线进程。其后每次编译都先确认前一进程退出，最终冷编单路逐件执行。未加堆，也未出现8G堆耗尽。

临时检查用90秒诊断上限，最终冷编与闭项 refl 使用600秒上限；没有124、154或251。scope失败42、初项运输失败42和中断都保存在私有日志。没有重跑相同大堆失败来冒充通过。

没有读、只凭转述引用的内容：未重新构建 Lean；Lean 公理和跨系统逐项相同的状态沿 Guide 的已标档说明，不作为本轮新定理。未完整读 Closure.lean 其它段落；本轮仅直接读359–400、1545–1634。原论文只核第3节相关页与引理，并非全篇新综述。WfFsnClosure 的蓝本与 cl-fsT/trian-fsT 已读，未新移植它们，因为本轮所需 NF/G 已由 EboLean 系列提供。

#### 7. 冻结清单

以下三个源码在最终冷编后不再修改，供根审主动冷编与读陈述。报告和编译指标在私有目录；不把本回报写入仓库。

```text
3f98dae59ede4c9270ad923d28b90f072c0bf6d5e20655cbd96a063b68cf8163  probes/OCF/Lean/YiLBStart.lagda.md
8fedac4ef8969577133e70b8546392f471abbeb914d9fd25ac35a9104fbdfe89  probes/OCF/Lean/YiLBInv.lagda.md
71e185643405687c69a01cef71acc0cc117571241a1feeb3ff5a707537fd2641  probes/OCF/Lean/YiLBActual.lagda.md

```
