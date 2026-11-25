# LowKeep 一次对一切层号归约（数学，整体引理） (YiLK)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十七批；外部模型，作者转发 |
| 前缀 | `YiLK` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：LowKeep 一次对一切层号归约（数学，整体引理）（前缀 YiLK）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十七批五路之一（选项原文 "LowKeep 一次对一切层号归约 (Recommended)"），与在跑的 YiPJ、YiNX、YiXV 以及本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **要证的律**（`YiAbsGIface` 第 142–143 行，逐字）：
  ```agda
  LowKeep  = ∀ {ℓ j} (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (K : Cx ℓ j) → Gb ℓ b → Wl w → Bd b w β K
           → ∀ {a x} → Gx ℓ x → R ℓ a x → R j (app K a) (ψ ℓ b j w β x)
  ```
  实例在 `YiGIInst`（`gradedᵍ`、`domsᵍ`），关系族 `YiGIRel.R`；零层的情形已证：`YiGICheck.low-zero`。
- **逐站做过的同类工作**（各站的结点、嵌入、ℕ 极限、松弛、遗传封闭、回灌链各行都证完了，留下的是孩子接口）：
  - 塔第 1 项那一层：`YiKPRel`（`record Kid`、`Top.Fold.LF¹`、`chain`、`leaf¹`），主线折叠上的版本 `YiLTKid`；
  - 塔第 2 项那一层：`YiKQRel`（`record Kid₂`）、`YiKQFold`（`Fold.LF²`、`chain`、`feedΩ`，底的条件 `GB²`）、`YiKQSuff`。
- AGENTS 的目标："闭包定理与阶段无关 (不按阶段定制支配论证)"。本路就是把上面两站的论证写成对一切层号的一条。
- `YiGIRel` 的族按层号 `L` 索引，不按 ℕ 经 `fn n` 索引。以前把任意路径交给保持接口时卡在 `fn n` 端点的合一（`SplitError.UnificationStuck`，回报 `probes/Survey/Reports-2026-11-12/YiSS.md`）；在 `L` 上索引可能没有这个问题，第 0 步先确认。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：写出一条统一的陈述 "对一切 ℓ：孩子接口 `KidU ℓ` ⇒ 源层为 ℓ 的 `LowKeep`"（`KidU ℓ` 是每层一条的孩子接口，你定）。确认类型正确；在 ℓ = `zero` 上由 `low-zero` 得到实例；路径的 `self`、`inc`、`inu` 三个子句各写一个，确认过检查器。不成立就停下回报，附首个错误。
1. **对一切层号的各行**：结点、嵌入（`up`）、ℕ 极限、Ω 分支、松弛与遗传封闭、回灌链，对一切 ℓ 一次证完（照 `YiKQFold.Fold.LF²` 与 `YiKPRel.Top.Fold.LF¹`，不按塔的项定制）。
2. **归约成一条**：编译 `(∀ ℓ → KidU ℓ) → LowKeep`。再分析 `KidU` 在 Ω 形状层号 `nd (sΩ k) h` 上要什么：能否归约到更低层号（或读回层号）上同形的陈述，从而对层号作良基递归；做到就交 "LowKeep 归约到某一族基础陈述" 的定理，做不到就交挡住递归的第一条引理。
3. 说明 `YiKPRel.Kid`、`YiKQRel.Kid₂` 是不是 `KidU` 在塔第 1、2 项那一层上的实例（编译或指出差别）。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiLK`（模块名 `OCF.Lean.YiLK…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiNX`、`YiXV`、`YiFM`、`YiLL`、`YiPC`、`YiVW`）。验收文件，文首标明。
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

3 件、241 同口径代码行；主审逐件删自身接口、5G 独立冷编全 0，各仅自身 Checking、源码哈希不变；禁用构造、洞、本机路径、Funext 0。已读全部源码与范围/旧两站比较。uniform 对任意 L 与输入树，fromSlots 按 L 递归消去孩子，Leaf 给起点；最终 Leaf→(∀ℓ StepUℓ)→LowKeep。KidU 另含槽位起点与步进，不是纯孩子单字段接口；完整 Leaf/StepU 联合可满足性未证。OmegaStep 源仍为原 Ω 层、目标 k，未从低源的零目标保持递归填入，签名分析不是否定定理。

## 回报原文（本会话执行）

### YiLK 完整回报（定稿）

源码冻结：三个 `probes/OCF/Lean/YiLK*.lagda.md`，冻结后的 SHA-256 见下表与 `audit.json`。回报定稿：本文件。请主审独立删三个自身接口，逐件冷编复核；本回报中的冷编是执行方自检。

#### 1. 判决、步骤与问题表

对纲领与目标的意义：本路给出一条对源层号结构递归的保持归约，没有按塔的第几项定制，没有改树、折叠、合法性或现有接口。孩子保持可由同一递归填入；`Leaf`（规范 Ω 树实现读回层号的叶律）可消去槽位链的起点。最终编译条件定理是：

```agda
steps→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → Laws.LowKeep gradedᵍ domsᵍ
```

`StepU ℓ` 是槽位回灌一步：已知当前坐标实现参照 γ 链的第 n 项，且该坐标处的源树实现对应的 Ω 基本列项，则折叠到槽位所在层后实现第 n+1 项。它包含原源层上的、目标是槽位层的折叠。尚未实填全层 `StepU`，也未实填全域 `Leaf`。本路不提高无条件主线强度，不新增关于 EBOᶻ 的无条件序数值下界；FGH 比较未作结论。

必须区分：`KidU` **含孩子保持以及槽位起点、步进条件**，并不是把旧的孩子接口逐字改为全层后就填完了。已编译 `(∀ ℓ → KidU ℓ) → LowKeep`，进一步消去孩子与起点后，剩下的全层步进前提仍有待证明。没有把这个前提叫作已经完成的保持律。

- 第 0 步通过：临时纯 Agda 文件 `YiLKCheck.agda` 在进入一般证明前编译退出 0。`Reduction = ∀ ℓ → KidU ℓ → LowAt ℓ` 类型正确；`kid-zero : KidU zero` 是闭实例；`low-zero-instance` 由既有 `low-zero` 给出。`self-zero` 检查 self；`up-inc` 检查后继形状的一条 inc 孩子行；`up-inu` 检查任意形状的标准 inu 孩子行。inc 检查不是任意 Ω 指定孩子派发的完整保持定理。
- 第 1 步完成条件归纳：`Fold.LF` 对所有 `s h` 一次处理 mz、m1、mL、mΩ、mU、mw、mc。`updated-ok` 说明传给孩子的更新底仍满足已有 `OKB`；`Fold.chain` 对 n 递归，实际证明完整回灌链。Ω 行的条件正是明列的 `SlotU.start/step`，未隐藏全链结论为前提。
- 第 2 步完成归约：`uniform`、`reduce`、`lowKeep`；`fromSlots` 对 `L` 结构递归消去孩子接口；`start-from-leaf` 消去槽位起点；最后得到 `steps→lowKeep`。Ω 形状的根槽位步进逐字展开为 `OmegaStep`，`omega-step` 编译证明它是 `StepU (nd (sΩ k) h)` 的必要投影。进一步由较低源层或读回层号的同形命题填它，尚未走通；本路只交未完成引理，不给否定结论。
- 第 3 步完成签名与量化域比较，差别见第 4 节。没有声称旧两个接口已转换成 `KidU`。

| 问题 | 位置 | 档 |
|---|---|---|
| 任意 L 索引的统一接口与三种指定路径子句可否通过检查器 | YiLKIface 的 Reduction、self-zero、up-inc、up-inu；临时 check-2.log | 编译定理 |
| 能否不按塔项分别写源层各行 | YiLKFold.Fold.LF 与 Fold.chain | 编译条件定理 |
| 孩子前提能否由源层结构递归消去 | YiLKFold.fromSlots | 编译条件定理 |
| 槽位起点能否由 Leaf 取得 | YiLKSlot.start-from-leaf | 编译条件定理 |
| 最终 LowKeep 的归约 | YiLKSlot.steps→lowKeep | 编译条件定理 |
| Ω 根槽位步进的精确残留义务 | YiLKSlot.OmegaStep、omega-step | 类型与投影为编译定理；该义务未填 |
| 仅用较低源层的 PresU 继续递归是否足够 | 源层仍是 nd (sΩ k) h，目标改成 k | 未走通；签名分析是判断，不是不可推出定理 |
| 是否已有全域前提的闭实例 | 只有 KidU zero、StepU zero 已交；全域 Leaf 与 StepU 未交 | 范围说明，不能据本回报声称全域前提已可满足 |

#### 2. 文件、冷编与审计

私有实验目录：`<实验目录>/`。完整回报：`<回报原文>`。没有别的私有实验目录。

内存直接抄自每次 `+RTS -s`：maximum residency 单位为 bytes；total memory in use 单位为 MiB。它们不是进程 RSS，不跨口径比较。代码行列为 Agda 代码块全部行 / 非空行；物理行包括 literate 文字及围栏。

| 模块 | 物理行 | 代码块行 / 非空行 | 删自身接口冷编退出码 | maximum residency bytes | total memory MiB | elapsed s |
|---|---:|---:|---:|---:|---:|---:|
| `YiLKIface` | 117 | 110 / 93 | 0 | 1,337,414,128 | 2479 | 16.791 |
| `YiLKFold` | 102 | 95 / 85 | 0 | 1,347,867,664 | 2393 | 17.552 |
| `YiLKSlot` | 84 | 74 / 63 | 0 | 1,475,692,592 | 2573 | 16.201 |

三件共 303 物理行，279 代码块行，其中 241 非空。每件冷编仅删其自身 `.agdai`，不忽略或删除依赖接口；每份冷编日志仅有对应自身模块的一条 `Checking`，没有依赖重编、错误或警告。每次只跑一个 Agda，堆上限始终 5G。

源码文件：

1. `probes/OCF/Lean/YiLKIface.lagda.md`
2. `probes/OCF/Lean/YiLKFold.lagda.md`
3. `probes/OCF/Lean/YiLKSlot.lagda.md`

临时文件、日志与生成接口完整清单：

- `libraries`：本路私有库清单。
- `YiLKCheck.agda`、`YiLKCheck.agdai`：第 0 步原型与其接口，保留原始版本；定稿版本复用既有 `OKB`，并把起点、步进类型拆出命名。
- `check-1.log`：退出 42，缺少 `YiMTTab` 显式导入；首错为 `NotInScope`，不是 LibraryError。
- `check-2.log`：第 0 步通过，退出 0。
- `fold-1.log`：初版统一 LF、reduce、lowKeep 通过，退出 0。
- `fold-2.log`：加入 `fromSlots` 与 `slots→lowKeep` 后通过，退出 0。
- `slot-1.log`：退出 42，缺少 `proj₂` 显式导入；首错为 `NotInScope`。
- `slot-2.log`：补导入后通过，退出 0。
- `final-warm.log`：复用已有 `OKB` 后三个冻结源码的入口暖编，退出 0。
- `YiLKIface-cold.log`、`YiLKFold-cold.log`、`YiLKSlot-cold.log`：各件冷编和 `+RTS -s` 原始输出。
- `YiLKIface-cold.exit`、`YiLKFold-cold.exit`、`YiLKSlot-cold.exit`：上述退出码，均 0。
- `audit.json`：三个源文件代码行、禁用构造检查与冻结 SHA-256。
- `cold-verification.json`：逐件核对退出码、Checking、内存与 SHA-256。
- `signatures.md`：定稿源码逐字抽出的签名附录；本回报后附同一内容。

仓库生成接口是 `probes/_build/2.8.0.2/agda/OCF/Lean/YiLKIface.agdai`、`YiLKFold.agdai`、`YiLKSlot.agdai`，均只删除过自身同名接口后重新生成。

自查范围是上述三个新增源码全文：`postulate`、洞、`TERMINATING` / `NON_TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、允许未解元、`--irrelevant-projections`、独立 `--cubical`、本机路径命中均为 0；没有 Funext 前提。`--safe --without-K --lossy-unification` 保持；库默认选项保持。没有作记号无关性声明：三件都是标明读记号的验收文件，因此没有对它们作成品候选依赖切片或导入闭包清洁声明。

冷编重现命令（分别替换模块名，每次只删对应自身接口）：

```sh
rm probes/_build/2.8.0.2/agda/OCF/Lean/YiLKIface.agdai
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiLKIface.lagda.md > <实验目录>/YiLKIface-cold.log 2>&1
result_code=$?
print "exit=$result_code"
```

冻结源码 SHA-256：

- `probes/OCF/Lean/YiLKIface.lagda.md`：`09ab5693081ae7b4921b9a3d6cae721291c41c58381d25b33f52a38181853990`
- `probes/OCF/Lean/YiLKFold.lagda.md`：`6067d0f96ad977b2685b179549e5095e999791fc3f6854509643c89c908ddc9e`
- `probes/OCF/Lean/YiLKSlot.lagda.md`：`13d06a1f1e7cb8c8385c209782b08a1ebb42056b107febc538618f2bb597341c`

#### 3. 定理表

以下均为编译条件定理或无条件的接口构造，不是有限测试。具体条件逐字写在类型中。

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| kid-zero | `kid-zero : KidU zero` | 零层统一接口有闭实例 | YiLKIface |
| self-zero | `self-zero : PresU zero` | 复用 low-zero，零层对任意输入树保持 | YiLKIface |
| low-zero-instance | `low-zero-instance : LowAt zero` | 零层当前 LowKeep 片段 | YiLKIface |
| uniform | `uniform : ∀ ℓ → KidU ℓ → PresU ℓ` | 对任意源层、任意输入树的零目标保持 | YiLKFold |
| reduce | `reduce : Reduction` | `Reduction = ∀ ℓ → KidU ℓ → LowAt ℓ` | YiLKFold |
| lowKeep | `lowKeep : (∀ ℓ → KidU ℓ) → Laws.LowKeep gradedᵍ domsᵍ` | 实际分级实例的原 LowKeep 归约 | YiLKFold |
| fromSlots | `fromSlots : (∀ ℓ → SlotU ℓ) → ∀ ℓ → PresU ℓ` | 同一层号结构递归消去所有孩子前提 | YiLKFold |
| slots→lowKeep | `slots→lowKeep : (∀ ℓ → SlotU ℓ) → Laws.LowKeep gradedᵍ domsᵍ` | 槽位起点、步进足够 | YiLKFold |
| start-from-leaf | `start-from-leaf : Laws.Leaf gradedᵍ domsᵍ → ∀ ℓ → StartU ℓ` | 叶律和底的 Ω 下界给回灌链起点 | YiLKSlot |
| step-zero | `step-zero : StepU zero` | 零层步进义务空匹配可填 | YiLKSlot |
| steps→pres | `steps→pres : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → ∀ ℓ → PresU ℓ` | 对任意输入树得到零目标保持 | YiLKSlot |
| steps→lowKeep | `steps→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → Laws.LowKeep gradedᵍ domsᵍ` | 叶律加全层一步回灌推出原 LowKeep | YiLKSlot |
| omega-step | `omega-step : ∀ k h → StepU (nd (sΩ k) h) → OmegaStep k h` | Ω 根槽位所需步进的逐字投影 | YiLKSlot |

`PresU`、`StartU`、`StepU`、`LowAt`、`OmegaStep` 的完整定义见源码；其余辅助引理与局部 `Fold` 参数下的 `Fz`、`chain`、`LF` 的逐字签名在附录。`Fold` 的上下文为：

```agda
module Fold (s : Sh) (h : Ch s → L) (K : KidU (nd s h))
            (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (gb : OK B) (t : E.T) where
```

前提可满足性核对的精确边界：第 0 步要求的零层 `KidU` 已给闭实例，孩子保持及槽位步进零层实例已编译。底的条件就是已有 `YiRBFam.OKB`，规范底 `B₀` 满足它由逐点 `⊴r` 可填写。统一定理没有要求层号比较或全分支派发。但全层 `StepU` 尚未给实例，不能借本路的条件定理断言该全层接口已可满足，也不能断言不可满足。

#### 4. 第一个未完成引理及旧两站的差别

第一个未完成引理是 `OmegaStep k h` 的实填，逐字陈述为：

```agda
OmegaStep : (k : L) → (Tr k → L) → Set
OmegaStep k h = (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) → OK B
  → (t a ν : E.T) → GR.Rd k ν → E.cof a ≡ E.cΩ ν
  → (g : Tr k → Tr (nd (sΩ k) h)) (n : ℕ) (c : Tr k)
  → GR.R k (E.γT (t ++ a) ν n) c
  → GR.R (nd (sΩ k) h) (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.R k (E.γT (t ++ a) ν (suc n))
      (proj₁ (ψ (nd (sΩ k) h) o r B k (ink self) (B k (ink self)) (g c)))
```

签名分析（判断档）：源仍是 `nd (sΩ k) h`，目标是 k；调用 `PresU k` 会把源换成 k，调用 `PresU (h c)` 会把源换成孩子层，都不是这里所需的折叠。且 γ 的后继项用参照下标 ν 的 ψ，而当前 `PresU` 的目标参照固定为 ψ₀。故本路的这条源层结构递归不能直接把此字段交给它的低层递归结果。没有证明任何更广的递归方案不可行，也没有把它归为壁垒实例。

量化域警示（判断档）：本路的 `StepU` 对任意前缀 t、底满足 OKB、任意 g 及一个分支的关系证据要求一步结论；它未额外要求 g 在所有参照坐标上满足整个 Ω 分支律。因此它是明确的充分条件，其全域可满足性需单独检查。不能把本路归约读成“原低层保持问题的等价改写”，更不能把该条件未填解释为原 LowKeep 已否定。

`YiKPRel.Kid`、`YiKQRel.Kid₂` 不是本路 `KidU` 在 tw 1、tw 2 上的逐字实例。下列是已读源码的签名差别，不是“不可能构造接口映射”的定理：

| 项目 | YiKPRel.Kid / 第一站 | YiKQRel.Kid₂ / 第二站 | 本路 KidU |
|---|---|---|---|
| 孩子关系 | 自选 Kd | 自选 Kd | 固定 GR.R (h c) |
| 底条件 | 自选 GBc，带逐点放大封闭 | OKB；顶层 GB² 另要求 `A.M¹ One.ΩΩ` 的底 | 孩子 PresU 统一 OKB；槽位条件另外明列 |
| 前缀 | 固定 t₀ 的接口 | 固定空前缀 | 对所有前缀 t |
| 孩子路径 | 自选 Pc，包含标准 z≤ 与经过下标层路径 | Pc 为标准路径或经过下标层路径 | ChildU 只用标准 z≤；回灌到槽位使用 posW |
| Ω 根 Low | 第一站 M⁰ η c | `A.M¹ (E.Ωt η) c` | `GR.R k η c` |
| 根 Nu | ν ≡ []；其他槽位排除 | ν ≡ []；其他槽位排除 | `Rd k ν`，其他槽位按 Low/Nu 递归 |
| 输入推导 | 其顶层 LF¹ 要 Sp，mU 左推导是 mz | LF² 要 Sp，mU 左推导是 mz | PresU 对所有 GR.R 推导，不要求 Sp |
| 折叠 | YiRWFold.ψ；主线变体是 YiLTKid | YiTBRow.ψ | YiTBRow.ψ |

因此旧两站证明的 Ω 行不能逐字填满这里的所有槽位字段。没有编译旧接口到新接口的转换。`YiLKFold` 的 mz、m1、mL、mU、mw、mc 证明形状取自已有推导归纳，新的工作是统一源层、显式槽位链条件，以及消去孩子与起点的归约。

#### 5. 偏离、事故与引用边界

- 范围选择：原“孩子接口”落实为 `KidU = ChildU + SlotU`；这多出了槽位条件，已在判决中明列。没有声称孩子单一字段足够。
- 研究判断：曾考虑把完整链直接放进接口，最终保留起点与一步字段，完整链由归纳证明；未保存另一个完整链接口。
- 研究判断：本路只要求当前 LowKeep 的标准零路径；没有扩大为所有目标层与所有路径的完整派发保持。inc 检查是后继形状的一条实例。所有泛化到任意目标层的方案均未在本路实现。
- 研究判断：更低源层的零目标保持没有直接提供 OmegaStep 所需的同源分级目标折叠。后续候选是发展按目标读回下标 ν 参数化的模拟律，或先检查当前 StepU 的全域可满足性；这是建议，没有改题执行，也没有改现有树侧定义。
- 两次退出 42 都是显式导入遗漏：YiMTTab 与 proj₂。没有一次在同一数学接口处重新设计失败，没有触发两次重设计停止条件；没有堆耗尽、超时或 Agda 内部错误。
- 先读完任务简报、AGENTS.md、EBOHandbook §4；先完成第 0 步原型的编译，再写统一 Fold。没有派子路，没有改共享接口、旧文件、README、LOG、台账或归档，没有提交或推送。仅写自身前缀源码、上述私有实验目录及指定回报路径。
- 直接读过的相关定义或签名：YiRWBlock、YiRWOps（所需 Ω/读回定义）、YiRWPath、YiRWFold、YiTBRow、YiTBFam、YiRBFam、YiGIBlock、YiGIInst、YiGIRel、YiGICheck、YiAbsGIface、YiHCRel、YiKPRel、YiKQRel、YiKQFold、YiLTKid、YiSPRel、YiLTFold、YiLTLim、YiMENote、YiANFam、YiTSNote、YiExSuff，以及 YiPJAll 的路径保持声明。按签名和所需代码段读取，没有整篇读取所有导入闭包。
- 仅由简报转述、未作独立冷编复核的背景：上一批 YiGIEnd.eboᵍ 已被主审复核、YiSS 的 SplitError 事故、YiPJ/YiNX 已冻结等历史结论。新结果不依赖对这些历史结论的重新证明。YiGIEnd 的完整证明未读；不把本路结果表述为已完成它的所有前提。
- 既有证明按导入接口复用，未删除其接口进行单独冷编。主审对本路三个新增源码的独立复核仍待进行。

#### 附录：定稿源码逐字签名

##### YiLKIface.lagda.md

```agda
PresU : L → Set

ChildU : L → Set

feed : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (p : Pos ℓ)
  → (Br ℓ p → Tr ℓ) → Br ℓ p → Br ℓ p

StartU : L → Set

StepU : L → Set

    start : StartU ℓ

    step : StepU ℓ

    child : ChildU ℓ

    slot : SlotU ℓ

LowAt : L → Set

Reduction : Set

kid-zero : KidU zero

self-zero : PresU zero

low-zero-instance : LowAt zero

updated-ok : ∀ s h (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → OK B
  → (x : Tr (nd s h)) (c : Ch s)
  → OK (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x)

up-inu : ∀ s h → ChildU (nd s h)
  → (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → OK B
  → (t a b : E.T) (β : Tr⁺ zero) (x : Tr (nd s h)) (c : Ch s)
  → (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ (nd s h) o r B zero (inu (λ c → z≤ (h c))) β x))
  → GR.R (h c) b y
  → M⁰ (E.ψ [] ((t ++ a) ++ b) ∷ [])
      (proj₁ (ψ (nd s h) o r B zero (inu (λ c → z≤ (h c))) β (up x c y e)))

up-inc : ∀ h → ChildU (nd sS h)
  → (o : Ok (nd sS h)) (r : Rb (nd sS h)) (B : Base (nd sS h)) → OK B
  → (t a b : E.T) (β : Tr⁺ zero) (x : Tr (nd sS h))
  → (y : Tr (h tt)) (e : h tt ⊢ zero ◃ y)
  → M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ (nd sS h) o r B zero (inc tt (z≤ (h tt))) β x))
  → GR.R (h tt) b y
  → M⁰ (E.ψ [] ((t ++ a) ++ b) ∷ [])
      (proj₁ (ψ (nd sS h) o r B zero (inc tt (z≤ (h tt))) β (up x tt y e)))
```

##### YiLKFold.lagda.md

```agda
  F : Tr⁺ zero → Tr (nd s h) → Tr⁺ zero

  Fz : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ x → M⁰ (ψᴺ 0 t) (proj₁ (F β x))

  chain : ∀ a (p : Pos (nd s h)) ν → GR.Nu (nd s h) p ν → E.cof a ≡ E.cΩ ν
    → (g : Br (nd s h) p → Tr (nd s h))
    → (∀ η c → GR.Low (nd s h) p η c → GR.R (nd s h) (E.fsT a η) (g c))
    → ∀ n → GR.Low (nd s h) p (E.γT (t ++ a) ν n)
      (iter (feed (nd s h) o r B p g) (fromBr (nd s h) p zero) (suc n))

  LF : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ {a x} → GR.R (nd s h) a x → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (F β x))

uniform : ∀ ℓ → KidU ℓ → PresU ℓ

reduce : Reduction

lowKeep : (∀ ℓ → KidU ℓ) → Laws.LowKeep gradedᵍ domsᵍ

fromSlots : (∀ ℓ → SlotU ℓ) → ∀ ℓ → PresU ℓ

slots→lowKeep : (∀ ℓ → SlotU ℓ) → Laws.LowKeep gradedᵍ domsᵍ
```

##### YiLKSlot.lagda.md

```agda
  nu-to : ∀ ℓ (p : Pos ℓ) {ν} → GR.Nu ℓ p ν → GR.Rd (at ℓ p) ν

  nu-to⁼ : ∀ a (q : Pos⁼ a) {ν} → GR.Nu⁼ a q ν → GR.Rd (proj₁ (sl⁼ a q)) ν

  low-from : ∀ ℓ (p : Pos ℓ) {η} {x : Tr (at ℓ p)}
    → GR.R (at ℓ p) η x → GR.Low ℓ p η (fromBr ℓ p x)

  low-from⁼ : ∀ a (q : Pos⁼ a) {η} {x : Tr (proj₁ (sl⁼ a q))}
    → GR.R (proj₁ (sl⁼ a q)) η x → GR.Low⁼ a q η (proj₂ (sl⁼ a q) x)

r⊴ : ∀ ℓ {η x y} → GR.R ℓ η x → x ⊴ y → GR.R ℓ η y

start-from-leaf : Laws.Leaf gradedᵍ domsᵍ → ∀ ℓ → StartU ℓ

step-zero : StepU zero

steps→pres : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → ∀ ℓ → PresU ℓ

steps→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → Laws.LowKeep gradedᵍ domsᵍ

OmegaStep : (k : L) → (Tr k → L) → Set

omega-step : ∀ k h → StepU (nd (sΩ k) h) → OmegaStep k h
```
