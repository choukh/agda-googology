# 在规范域上重写律并重做组装（数学，接口） (YiCN)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 "派"（第五十批）；外部模型，作者转发 |
| 前缀 | `YiCN` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：在规范域上重写律并重做组装（数学，接口）（前缀 YiCN）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十批（作者原话 "派"，回应主审的建议 "在规范塔域上重写接口的律，让 Leaf 只对塔实际用到的层号陈述，出口随推导产生，然后重新编译组装"），与在跑的 YiXV、YiGT、YiSU 在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **组装现在什么也没说**：`YiGIEnd.eboᵍ` 的前提是 `Leaf`、`Lift`、`LowKeep` 三条全域律加全塔出口条件，而全域 `Leaf` 已被编译否定：`YiLLLeafNeg.noLeaf : Leaf → ⊥`，限到合法层号上也一样（`noLeafOk`）。反例是孩子层号参差的 Ω 形状层号：k = `zero`，h 在树 0、1、2 上分别取层号 0、1、0，读法从孩子 1 继承，孩子 2 装不下（回报 `probes/Survey/Reports-2026-11-12/YiLL.md`）。AGENTS："前提要可满足. 否定定理与条件定理的每个前提, 给一个实例或说明为何可满足; 前提矛盾的定理什么也没说"。
- **出口**：非标准形项上项序推出值序不成立（`YiMXNote.¬Mono`），带 `mc` 的关系上的无条件出口不成立（`YiMXNeg.¬Exit′`）；改写 `YiMXEnd.LowKeepᴱ`（保持连同出口证据 `Exᴴ` 一起产生），`forgetᴱ`、`eboᴱ : Leaf → Lift → LowKeepᴱ → …` 已编译（回报 `YiMX.md`）。
- **组装证明实际用到律的地方**（`YiExSuff` 第 57–68 行）：
  ```agda
  keel (suc n) = tw-step n (li (gl n) (lf (keel n)))
  keelᴿ n = lf (keel n)
  folded L n = L (b₀ n) (w₀ n) (β₀ n) (K₀ n) (gb n) (wl n) (bd n) (gx n) (keelᴿ n)
  ```
  即 `Leaf` 只在塔的层号 `tw n`、对着龙骨的读法 `keel n` 上用，`Lift` 只在 `gl n` 上用，`LowKeep` 只在龙骨的各行上用。接口的律在 `YiAbsGIface` 第 138–155 行（`Leaf = ∀ {ℓ ν} → Rd ℓ ν → R ℓ (Ωr ν) (Ωt ℓ)` 不受 `Doms` 约束）。
- **已有的局部事实**：`YiLLCheck.read0 : ∀ {ν c} → GR.R zero ν c → GR.Rd (↑ zero c) ν`（第 0 层上的读法律对一切关系推导），`YiLLCheck.leafC`（无 Ω 结点的层号上 Leaf）；`YiGICheck.leaf-fin`、`rd-fin`、`lift-start`、`low-zero`；不依赖 Leaf 的归约 `YiPFReachFold.slots→lowKeepᵂ`。
- 在跑的 YiSU 发现原 `StepU` 的全域量化不成立、补上底与前缀的联系后在 `fn 1` 上有实例；它还没结束，本路不导入 `YiSU*`、`YiGT*` 的文件。
- AGENTS "量化域先取带证据的读回域"；"连续两条同形的退化反例就停下来查量化域, 不逐个加字段"；"闭包定理与阶段无关"。

#### 要做的（按序）
0. **最小检查**，在临时目录：
   - (a) 写出只沿龙骨的律：`Leafᵏ : ∀ n → R (tw n) (Ωr (kt n)) (Ωt (tw n))`（或以 `keel n` 为参数的形式）、`Liftᵏ`（只在 `gl n`）、`LowKeepᴱᵏ`（只在龙骨各行，结论带 `Exᴴ`），照 `YiExSuff.TowerE` 与 `YiMXEnd` 编译出 "这三条 ⇒ `toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`"。
   - (b) 在 n = 0 上把这三条实填（`rd-tw0`、`read0`、`low-zero` 一类）。
   - (c) 确认 `noLeaf` 的反例层号不是任何 `tw n`。
   - 不成立就停下回报。
1. **阶段无关的规范域**：只沿龙骨的律是逐站的；再给一个不读记号、与阶段无关的层号域 `Cn : L → Set`（主审的候选，判断：Ω 形状层号 `nd (sΩ k) h` 的孩子层号 h 沿孩子的第一位置序单调，且递归地对 k 与各 `h c` 成立；你可以选别的，说明理由），证明：一切 `tw n` 在 `Cn` 里；`noLeaf` 的反例层号不在里面；`Cn` 上的 Leaf 推出 `Leafᵏ`。
2. **`Cn` 上的 Leaf**：对 `Cn` 里的层号与其读法证 Leaf，或交第一个反例（若反例在 `Cn` 里，就是 "规范域上的 Leaf 也被否定"，写成编译定理并停下）。至少做到 `tw 1`。
3. **新的组装**：编译 `eboᶜ`，前提是 `Cn` 上的 Leaf（或 `Leafᵏ`）、`Liftᵏ`、`LowKeepᴱᵏ`；每条前提给出实例或说明为何可满足，n = 0、1 的实例尽量编译出来。精确列出剩下未实填的前提。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiCN`（模块名 `OCF.Lean.YiCN…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiGT`、`YiSU`）。定义规范域的文件若只用树与层号，文首标明 "不读记号" 并用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包；其余文件标明 "验收文件"。
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
  - **堆上限 5G**：同时有四路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
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

五件283行逐件删自身接口5G冷编0、仅自身Checking、哈希不变，扫描0。Domain导入闭包与编译器图本地4件相同且干净；两次构造失败在主审私有副本均复现42。达到至少tw1：完整Leaf在tw0/tw1，龙骨Leaf到第2站、Lift到第1站，Low及出口仅第0站。余项与全族可满足性未知，不报无条件EBO；NoNu仅否定提取字段，不否定Cn上的Leaf。详见LOG和V190。

## 回报原文（主审已独立复核）

### YiCN 完整回报（冻结交主审复核）

#### 1. 判决与完成范围

**对纲领与目标：本路把三条律改写到了实际龙骨调用域，给出了不读记号、与阶段无关的层号域，并编译了新的条件组装。没有改树、折叠、合法性，没有新增无条件强度，也没有从已否定的 Leaf 消去得到 EBO。** 本路已达到简报“至少做到 tw 1”的交付要求；这不表示全域实填已经完成。自检均完成；以下“编译定理”仍待主审逐件独立复核。

- 第 0 步全部通过。临时 `YiCNMin.agda` 编译退出 0：局部 Leaf/Lift/连出口的 LowKeep ⇒ 主线终点 ≥ EBO；第 0 站三条实填；旧反例不等于任何 `tw n`。首个临时文件及首个编译日志的时间为 2026-11-14 23:02:57 +0800，满足首个临时检查在 30 分钟内编译的限制。
- 第 1 步完成。`Cn` 由零、后继、有相邻路径的 ℕ 极限、统一的 `Ωc k = nd (sΩ k) (λ c → k ⊕ ↑ k c)` 生成。`cn-tw`、`cn-ok`、`cn-mono`、`no-cn`、`not-tw` 均编译通过。
- 第 2 步做到 **tw 1 的完整 Leaf（任意 Rd 读法）**。另有 tw 0 的完整 Leaf、第 0、1 站的龙骨 Lift、第 2 站指定读法的龙骨 Leaf。**没有证明整个 Cn 上的 Leaf，也没有否定它。**
- 第 3 步完成条件组装 `eboᵏ`、`eboᶜ`、`ebo-rest`。未完成的是全塔前提的实填与其整体可满足性证明。精确余项：Leaf 从 n ≥ 3 起；Lift 从 n ≥ 2 起；连同 Exᴴ 的 LowKeep 从 n ≥ 1 起。条件组装不据此计为新的无条件 EBO 强度结果。

选择生成式 Cn 的理由（判断）：它把同一个树侧 Ω 步骤作为统一生成规则，且不需要逐阶段写专属前提；域内其 Ω 根的单调性另有 `cn-mono` 检验。它不是简报候选“对 k 及每个孩子递归检查任意单调 Ω 根”的实现：Cn 不要求 Ωc 的每个孩子也有 Cn 证据。该候选的完整遗传条件本路未实现、未否定。未证明也不主张两域之间的包含关系，更不主张严格包含。`cn-ok` 给出原 Ok 及孩子的 Ok，不给出每个孩子的 Cn。导入闭包干净只说明定义不引用记号，不宣称定义没有受到已有树侧塔形状的启发。

| 问题 | 位置 | 档与当前结论 |
|---|---|---|
| 全域 Leaf 已否定是否污染组装 | `YiCNKeel.Assembly` | 编译定理：只调用新三条局部律；只引用旧 GE 的 reference/upperᴱ，不调用旧 eboᵍ |
| 原 noLeaf 反例是否还在规范域或塔中 | `YiCNAccept.no-cn/not-tw` | 编译定理：均不在 |
| tw 1 完整 Leaf | `YiCNTw1.leaf-tw1` | 编译定理：成立，∀ Rd 读法 |
| 整个 Cn 的 Leaf | Ω 根的任意孩子继承分支 | 未知；两种证明设计在该处未走通，不是编译否定 |
| 任意孩子读法能否直接给下标层前驱读法 | `YiCNDirectNeg.NuFromChild` | 编译否定：即使规范 tw 1、孩子 2、读法 2 也不成立 |
| 该字段的否定是否否定规范 Leaf | `YiCNDirectNeg.leaf-source` | 编译定理：同一输入上的 Leaf 成立，故不能这样归类 |
| 所有局部律的整体可满足性 | `LeafRest/LiftRest/LowRest` | 未知；局部实例不替代全塔族的实填 |
| 新的无条件序数值强度 | 本路 | 没有；EBO 是带下述前提的序数值下界，不是 FGH 比较 |

##### 前提的可满足性检查与精确余项

`LeafAt n` 只对塔使用的 ν = kt n 陈述；`LiftAt n` 只在 Ω 树及该固定输入上陈述；`LowAt n` 固定龙骨的源层、底、目标 0、路径、起点及空上下文，返回推导与 Exᴴ 的 Σ。这里 tw、kt、row、twc 是 `Keel⁻ keelᴱ` 的字段/派生量。

```agda
LeafAt n = GR.Rd (tw n) (kt n) → GR.R (tw n) (E.Ωt (kt n)) (proj₁ (O.Ωt (tw n)))
LiftAt n = GR.R (tw n) (E.Ωt (kt n)) (proj₁ (O.Ωt (tw n))) → GR.Rd (B.↑ (tw n) (proj₁ (O.Ωt (tw n)))) (E.Ωt (kt n))
LowAt n = GR.R (tw n) (E.Ωt (kt n)) (proj₁ (O.Ωt (tw n))) → Σ (GR.R B.zero (row n) (twc n)) H.Exᴴ
Leafᵏ = ∀ n → LeafAt n
Liftᵏ = ∀ n → LiftAt n
LowKeepᴱᵏ = ∀ n → LowAt n
```

具体输入并非空域：`GR.rd-tw0`、`rd1`、`rd2` 实填相应读法；`leaf0 GR.rd-tw0`、`leaf1 rd1` 实填 Lift 的源关系；`low0` 的结果直接给出关系和出口证据。规范域完整 Leaf 在 `tw 0`、`tw 1` 上有实例。这些都是编译定理，而不是有限样本测试。

但尚无 `Leafᶜ`、`Leafᵏ`、`Liftᵏ`、`LowKeepᴱᵏ` 的整个全称族实例；不能把上述局部实例说成已证明其整体可满足。下列余项也仍未知：

```agda
LeafRest = ∀ n → C.LeafAt (suc (suc (suc n)))
LiftRest = ∀ n → C.LiftAt (suc (suc n))
LowRest = ∀ n → C.LowAt (suc n)
```

##### n = 1 的 LowKeepᴱ：实际缺口与尝试范围

`LowAt 1` 的源关系由 `leaf1 rd1` 实填，目标仍缺整个 Σ：既没有构造出 `GR.R zero (row 1) (twc 1)` 的推导，也没有它的 `H.Exᴴ` 证据。这里 `row 1` 是 `E.EBOψ 1`；`twc 1` 是 `keelᴱ` 的实际第 1 行，底为 `baseᴱ 1`、起点为 `betaᴱ 1`，不能把只涉及标准底 B₀ 与 Ωt zero 的另一个闭项的结论直接当作它的实例。

本路对这一行的实际工作是检索和纸面匹配，**没有写出 LowAt 1 的候选证明项，也没有 LowAt 1 的编译失败日志**。已查 `YiTBFam.Qu`/`YiLTFold.Qu`（源层为 zero），以及 `YiTBFam.LF`、`sΩ-LF` 等（源层为有限后继层号 fn n）；这些签名未直接覆盖 Ω 形状源层 `tw 1`。也查了 `YiMTValue` 的塔第 1 项值关系与下界；它们给值比较，未给出本接口要求的 H 关系推导和出口证据。本路没有证明从那些结果反推该 Σ 的引理。

判断：由于源关系已有闭项，n = 1 这一行可以先以“为指定输出构造一对关系推导与 Exᴴ”为目标，不必先证明对所有源推导的保持。但这只是任务归约的纸面说明，本路未将此归约另写成编译定理，也未取得该输出对。`YiCNInherited` 与 `YiCNDirect` 的两份未通过实验都针对 Leaf 的 Ω 继承分支，不能计作 LowAt 1 的构造尝试或否定。LowAt 1 的当前状态是未实填、未知；不归因于 no-NuFromChild、¬Mono 或 ¬Exit′。

#### 2. 文件、冷编、内存与审计

所有编译单 Agda，堆上限 5G。最终逐件删除其字面路径下自己的 `.agdai` 后重编；旧依赖使用已有接口，未使用 `--ignore-interfaces`。每份最终日志恰有一条 Checking，且是该文件自己的模块。没有 251、124 或 154。

代码行口径：`总文本行 / Agda fenced code 中非空、非纯注释行`，含选项、模块头、导入；不与别的口径并列比较。内存是 `+RTS -s` 的 maximum residency（字节），另列 total memory in use；它们不是进程 RSS。总计 364 文本行、283 非空代码行。

| 新文件（均在 probes/OCF/Lean/） | 总行 / 代码行 | 冷编退出码 | maximum residency bytes | total memory MiB | elapsed s |
|---|---:|---:|---:|---:|---:|
| `YiCNDomain.lagda.md` | 37 / 25 | 0 | 136,225,248 | 232 | 1.596 |
| `YiCNKeel.lagda.md` | 70 / 57 | 0 | 1,495,991,136 | 2438 | 16.003 |
| `YiCNTw1.lagda.md` | 122 / 102 | 0 | 1,393,179,424 | 2449 | 16.89 |
| `YiCNAccept.lagda.md` | 93 / 70 | 0 | 1,525,027,376 | 2498 | 17.983 |
| `YiCNDirectNeg.lagda.md` | 42 / 29 | 0 | 1,500,335,592 | 2447 | 16.75 |

仓库源码只有以上五个新文件。未改已有文件或文档，未改 src/archive，未提交、未推送，未派子路。五个文件文首均为 4 行非空文字。

- `importclosure.py OCF.Lean.YiCNDomain`：退出 0，本地闭包 4 个模块：YiCNDomain、YiRWBlock、YiRWOps、YiRWPath；禁用表命中 0。未使用 --only 缩窄审计。
- `agda --dependency-graph` 核对：图有 136 个标签，OCF 本地标签恰是上述 4 个；没有 Align/Notation/EBO 记号模块。
- 五个仓库源文件扫描：禁用构造/未解洞选项 0，本机路径 0，YiSU/YiGT 导入 0，N.noLeaf/N.noLeafOk/N.not-leaf-instance 调用 0。`--cubical-compatible` 与禁用的 `--cubical` 分开检查。
- 最终冷编后所有源文件 SHA256 与扫描时一致；详细数据在 `source-audit.json`、`verification.json`。这里没有做 depslice/HTML，也没有声称完成定义级切片。

最终冷编命令形式：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiCN<模块>.lagda.md > <实验目录>/cold-<模块>.log 2>&1
```

Domain 一次冷编另带 `--dependency-graph=<实验目录>/domain.dot`。退出码由 wrapper 直接取得，没有经过管道。

#### 3. 定理表与逐字陈述

所有下列条目是“编译定理”档；含未实填前提者标“条件”。内部坏输入消去辅助引理的前提与正规输入构造分别在源文件中给出。`NuFromChild` 的否定使用 cn-source/rd-source 实填全部输入，且另有 leaf-source，不能把它误读成 Leaf 的否定。

在 `YiCNKeel` 的 Assembly 内，签名上下文逐字为：

```agda
module Assembly (lf : Leafᵏ) (li : Liftᵏ) (lk : LowKeepᴱᵏ) where
```

##### YiCNDomain

| 名字 | 一句白话 | 档 |
|---|---|---|
| `cn-tw` | 全部规范塔层号都有域证据。 | 编译定理 |
| `cn-ok` | 域证据给出既有 Ok 合法性。 | 编译定理 |
| `cn-mono` | Ω 形状的孩子沿原树第一位置序有向前路径。 | 编译定理 |

逐字签名（沿源文件写法；名字按本节模块限定）：

```agda
cn-tw : ∀ n → Cn (tw n)

cn-ok : ∀ {ℓ} → Cn ℓ → P.Ok ℓ

cn-mono : ∀ {k h} → Cn (nd (sΩ k) h) → ∀ {x y} → k ⊢ x ◃ y → h x P.⊑ h y
```

##### YiCNKeel

| 名字 | 一句白话 | 档 |
|---|---|---|
| `Assembly.keel` | 三条局部律中的 Leaf/Lift 生成塔的读法；所在模块的 lf、li、lk 见下方上下文。 | 编译定理（条件） |
| `Assembly.folded` | 只折龙骨实际用到的行，并同时保留出口证据。 | 编译定理（条件） |
| `Assembly.Kᴱ` | 第 0 层关系经其自己的 Exᴴ 证据给出值下界。 | 编译定理（条件） |
| `Assembly.eboᶜ` | Assembly 内的带条件终点下界。 | 编译定理（条件） |
| `leaf0` | 第 0 站 Leaf 的实填。 | 编译定理 |
| `lift0` | 第 0 站 Lift 的实填。 | 编译定理 |
| `low0` | 第 0 站低层保持及出口的实填。 | 编译定理 |
| `eboᵏ` | 仅以三条局部全塔律为前提组装 EBO 下界。 | 编译定理（条件） |

逐字签名（沿源文件写法；名字按本节模块限定）：

```agda
  keel : ∀ n → GR.Rd (tw n) (kt n)

  folded : ∀ n → Σ (GR.R B.zero (row n) (twc n)) H.Exᴴ

  Kᴱ : ∀ n (h : SI.E.HC (row n)) → SI.E.tree h ≼ K.readRW (twc n)

  eboᶜ : toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ

leaf0 : LeafAt 0

lift0 : LiftAt 0

low0 : LowAt 0

eboᵏ : Leafᵏ → Liftᵏ → LowKeepᴱᵏ → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
```

##### YiCNTw1

| 名字 | 一句白话 | 档 |
|---|---|---|
| `no-emptyω` | ω 共尾视图的第 2 项不能是零。 | 编译定理 |
| `Ω-inv` | Ω 记号上的项序可反映到下标。 | 编译定理 |
| `small-head` | 低于 Ω₁ 的非零项的头层号低于 1。 | 编译定理 |
| `nonempty` | 非空项不等于零项。 | 编译定理 |
| `fω-below` | ω 基本列第 2 项不高于 Ω₁ 时，原项严格低于 Ω₁。 | 编译定理 |
| `suc-below` | 后继保持低于 Ω₁。 | 编译定理 |
| `rdC-bound` | 无 Ω 形状层号的全部读法低于 Ω₁。 | 编译定理 |
| `rd-zero` | 零层号只有零读法。 | 编译定理 |
| `regular-zero` | Ω 共尾且零参数基本列为零时，原项是 Ω₁。 | 编译定理 |
| `rd1-bound` | tw 1 的全部读法不高于 Ω₁。 | 编译定理 |
| `leaf-tw1` | tw 1 对任意 Rd 读法满足完整 Leaf。 | 编译定理 |

逐字签名（沿源文件写法；名字按本节模块限定）：

```agda
no-emptyω : ∀ {t} (v : Vω t) → fω v 2 ≡ [] → ⊥

Ω-inv : ∀ {u v} → E.Ωt u ≤ᵀ E.Ωt v → u ≤ᵀ v

small-head : ∀ {u b xs} → (E.ψ u b ∷ xs) E.<ᵀ Ω₁ → u E.<ᵀ E.natT 1

nonempty : ∀ {x : E.PT} {xs : E.T} → (x ∷ xs) ≡ [] → ⊥

fω-below : ∀ {t} (v : Vω t) → fω v 2 ≤ᵀ Ω₁ → t E.<ᵀ Ω₁

suc-below : ∀ {t} → t E.<ᵀ Ω₁ → E.sucT t E.<ᵀ Ω₁

rdC-bound : (ℓ : L) → NoΩ ℓ → ∀ {ν} → GR.Rd ℓ ν → ν E.<ᵀ Ω₁

rd-zero : ∀ {ν} → GR.Rd zero ν → ν ≡ []

regular-zero : ∀ {ν κ} (v : VΩ ν κ) → κ ≡ [] → fΩ v [] ≡ [] → ν ≡ Ω₁

rd1-bound : ∀ {ν} → GR.Rd (tw 1) ν → ν ≤ᵀ Ω₁

leaf-tw1 : ∀ {ν} → GR.Rd (tw 1) ν → GR.R (tw 1) (E.Ωt ν) (proj₁ (O.Ωt (tw 1)))
```

##### YiCNAccept

| 名字 | 一句白话 | 档 |
|---|---|---|
| `no-cn` | 旧 noLeaf 的反例层号不在新域。 | 编译定理 |
| `not-tw` | 该反例不等于任何 tw n。 | 编译定理 |
| `cn→keel` | 规范域上的完整 Leaf 足以提供塔所需的 Leaf。 | 编译定理（条件） |
| `leaf-tw0` | tw 0 对任意读法的完整 Leaf。 | 编译定理 |
| `leaf1` | 第 1 站龙骨 Leaf。 | 编译定理 |
| `lift1` | 第 1 站龙骨 Lift，忽略输入推导而直接构造读法。 | 编译定理 |
| `leaf2` | 第 2 站指定龙骨读法上的 Leaf；不是 tw 2 的完整 Leaf。 | 编译定理 |
| `rd1` | 第 1 站读法是闭项。 | 编译定理 |
| `rd2` | 第 2 站读法是闭项。 | 编译定理 |
| `eboᶜ` | 规范域 Leaf 加局部 Lift、连出口的局部低层保持，推出 EBO 下界。 | 编译定理（条件） |
| `fill-leaf` | 将已填的 0、1、2 站与未知余下族拼成 Leafᵏ。 | 编译定理（条件） |
| `fill-lift` | 将已填的 0、1 站与未知余下族拼成 Liftᵏ。 | 编译定理（条件） |
| `fill-low` | 将已填的第 0 行与未知余下族拼成 LowKeepᴱᵏ。 | 编译定理（条件） |
| `ebo-rest` | 将全塔尚未实填的前提精确写成三个余下族。 | 编译定理（条件） |

逐字签名（沿源文件写法；名字按本节模块限定）：

```agda
no-cn : Cn N.ℓ → ⊥

not-tw : ∀ n → N.ℓ ≡ tw n → ⊥

cn→keel : Leafᶜ → C.Leafᵏ

leaf-tw0 : ∀ {ν} → GR.Rd (tw 0) ν → GR.R (tw 0) (E.Ωt ν) (proj₁ (O.Ωt (tw 0)))

leaf1 : C.LeafAt 1

lift1 : C.LiftAt 1

leaf2 : C.LeafAt 2

rd1 : GR.Rd (tw 1) (E.natT 1)

rd2 : GR.Rd (tw 2) (E.Ωt (E.natT 1))

eboᶜ : Leafᶜ → C.Liftᵏ → C.LowKeepᴱᵏ → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ

fill-leaf : LeafRest → C.Leafᵏ

fill-lift : LiftRest → C.Liftᵏ

fill-low : LowRest → C.LowKeepᴱᵏ

ebo-rest : LeafRest → LiftRest → LowRest → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
```

##### YiCNDirectNeg

| 名字 | 一句白话 | 档 |
|---|---|---|
| `cn-source` | 否定字段反例的 Ω 根在规范域内。 | 编译定理 |
| `rd-source` | 其孩子 2 的读法 2 是闭项。 | 编译定理 |
| `no-NuFromChild` | 禁止从任意孩子后继读法直接提取下标层的前驱读法这一字段。 | 编译定理 |
| `leaf-source` | 同一规范反例输入的 Leaf 结论成立；故上一否定不是规范域 Leaf 的否定。 | 编译定理 |

逐字签名（沿源文件写法；名字按本节模块限定）：

```agda
cn-source : Cn (Ωc zero)

rd-source : GR.Rd (zero ⊕ ↑ zero two) (E.natT 2)

no-NuFromChild : NuFromChild → ⊥

leaf-source : GR.R (tw 1) (E.Ωt (E.natT 2)) (proj₁ (O.Ωt (tw 1)))
```

`NuFromChild` 的逐字定义：

```agda
NuFromChild = ∀ {k} → Cn k → (c : Tr k) {ν : E.T} → E.cof ν ≡ E.c1
  → GR.Rd (k ⊕ ↑ k c) ν → GR.Rd k (E.pred ν)
```

#### 4. 第一个障碍与停止范围

一般 Cn Leaf 的第一个未填引理是 Ωc k 在 `GR.ca (inj₁ (c , q))` 的任意孩子继承情形：给定 `q : Rd (k ⊕ ↑ k c) ν`，要得到顶层 Ω 树对 Ων 的关系。`cn-mono` 只有 x ◃ y 时孩子向前的路径；没有任意孩子 c 到第一孩子 0 的反向路径。

尝试一保留在 `YiCNInherited.agda:19`：即使暂把每个孩子的完整 Leaf 作为参数，写出的 `H.mw (H.mU ... (lc c q)) ◃w` 仍被检查器拒绝，日志是 `zero != c`。这是所写项不能使用第一分支边的类型错误，不是“这个目标没有证明”的定理。

尝试二改为保持目标、从孩子读法提取顶层直接 Ω 行所需的前驱共尾参数，所需字段命名为 `NuFromChild`。构造尝试保留在 `YiCNDirect.agda:8`，退出 42：孩子层号不是下标层 k。另有诊断留成 `no-NuFromChild` 编译否定：k = 0、c = 2、ν = 2，输入读法成立，所求输出 Rd 0 1 不成立。`leaf-source` 同时编译给出该输入的 Leaf，具体说明保持目标的直接 Ω 行不是必需的证明形状。

两种设计都未构造出一般 Ω 继承分支，依简报停止继续重写；只进行交付所需自查。停止不关闭规范域 Leaf，也不把它归到已有 W/V/C 或 LPO 壁垒：这里诊断的字段没有折叠、没有值比较，失败的是从孩子读法反提下标层读法的字段。没有提出修改树、折叠或合法性的方案。

**未知清单：** 整个 Cn 上的 Leaf；tw 2 的任意读法完整 Leaf；LeafRest（n ≥ 3）；LiftRest（n ≥ 2）；LowRest（n ≥ 1，包含出口）。本路没有证明这些字段矛盾。没有因读法高低关闭任何路线。

#### 5. 偏离、事故、未读来源与完整工件清单

- 选了生成式 Cn，而不是简报建议的任意单调 Ω 根遗传谓词；这在允许的“可以选别的”范围内，选择理由及域的差别已写在 §1。主审可分别审阅域选择与已编译结论，不把它当作作者已采纳。
- 额外交付 `leaf2`（仅第 2 站龙骨读法）与直接 Ω 字段的配对否定；没有借此扩大为 tw 2 完整 Leaf。
- `YiCNSmall` 初稿有一处多余右括号，改后通过。`YiCNBound` 初稿两轮在 w4 的 indexed match 上合一受阻，改为抽出通用头层号引理；随后补齐 nonempty 的显式类型以消除 metas，最终通过。这些是同一数学证明的语法/合一修复，没有拿失败日志当作否定定理。
- `YiCNDirectNeg` 初编 [] 的导入在局部签名后面，作用域失败；移到顶层并显式传 leaf-source 的 ν 后通过。
- 早期修复版本未逐版保留源码快照；当前 Min/Small/Bound 源码与各自最后一份通过日志配套。早期错误日志保留，只作工程历史；两份实际数学构造未通过的 Inherited/Direct 源码分别原样保留。
- 搜索已有 EBOψ 1 引理时，搜索输出出现 YiSUActual 的两行签名；未打开该文件、未导入 YiSU/YiGT、未依据该签名构造证明。报告此有限暴露，不宣称完全没有看见其文件名/签名。
- `importclosure.py --help` 不是该脚本支持的调用，返回 2；随后读取其调用说明并使用正式模块参数，退出 0。没有安装包或改变环境。
- 已读简报、AGENTS、手册 §4、YiGIEnd/GIInst/GIRel、YiExSuff、YiMXEnd、YiLLCheck/LeafNeg、YiGICheck 及所检索的相关签名/视图片段。**没有直接阅读 YiMXNote.¬Mono 和 YiMXNeg.¬Exit′ 的证明**，只把主审已复核的背景当作背景；本路结论不调用这两条否定。未重冷编全部旧依赖，本路冷编范围严格为五个新模块。
- 旧 noLeaf 的否定定理本身只作为已读背景。新正向结论使用其反例对象，或调用该文件的 fsn-big/fω-big/conflict 等独立已证句法引理；没有调用 noLeaf/noLeafOk/not-leaf-instance 作假前提消去。新的 no-NuFromChild 也未用于 EBO 组装。

##### 全部仓库源码

- `<仓库>/probes/OCF/Lean/YiCNDomain.lagda.md`
  SHA256 `abe38090a4f26e9eb720e0ef7f4c2ec2f85c14579d11f5bf2d7f60086f4a1826`
- `<仓库>/probes/OCF/Lean/YiCNKeel.lagda.md`
  SHA256 `c4b2fbb194d99d2eee8043ce9d998af5b36b4abd559f3e41f362ddf118034289`
- `<仓库>/probes/OCF/Lean/YiCNTw1.lagda.md`
  SHA256 `ffc644ee9e78c5632e212a6562bb7a47a8e59ebb5f01d68c903f00413d229428`
- `<仓库>/probes/OCF/Lean/YiCNAccept.lagda.md`
  SHA256 `c3e970223be34026ae240af682c2139ca217e4a41c8ebb0b9ec80ad410fcdeba`
- `<仓库>/probes/OCF/Lean/YiCNDirectNeg.lagda.md`
  SHA256 `4ba0407c36bd25427173e31410010e2b5b9cd2fe287db29b8a07a20ff770f65f`

##### 全部实验源码与状态

| 源码（实验目录） | 对应日志 | 退出码与意义 |
|---|---|---|
| YiCNMin.agda | min-01.log | 0；第 0 步 (a)(b)(c) |
| YiCNSmall.agda | small-01.log / small-02.log | 42（括号）/ 0；生成域与 tw 1 固定读法 Leaf/Lift |
| YiCNBound.agda | bound-01.log 至 bound-04.log | 42 / 42 / 42 / 0；最终完整 tw 1 Leaf |
| YiCNInherited.agda | inherited-01.log | 42；数学构造尝试未通过，不是编译否定 |
| YiCNDirect.agda | direct-01.log | 42；数学构造尝试未通过；字段另有编译否定 |

实验目录是 `<实验目录>`。完整简报来源：`<临时目录>`。

##### 全部日志与退出码

| 日志 | 退出码 | 范围 |
|---|---:|---|
| `<实验目录>/min-01.log` | 0 | 第 0 步临时检查 |
| `<实验目录>/small-01.log` | 42 | 多余右括号；无数学结论 |
| `<实验目录>/small-02.log` | 0 | 规范域和指定 tw 1 实例 |
| `<实验目录>/bound-01.log` | 42 | w4 indexed match 合一受阻 |
| `<实验目录>/bound-02.log` | 42 | 同一合一问题；改写前日志 |
| `<实验目录>/bound-03.log` | 42 | nonempty 的未显式类型导致 metas |
| `<实验目录>/bound-04.log` | 0 | 完整 tw 1 Leaf |
| `<实验目录>/domain-01.log` | 0 | Domain 初编 |
| `<实验目录>/accept-01.log` | 0 | Accept 初编，连带两个尚无接口的新依赖 |
| `<实验目录>/direct-neg-01.log` | 42 | [] 局部导入作用域 |
| `<实验目录>/direct-neg-02.log` | 0 | 直接 Ω 字段否定和配对正向实例 |
| `<实验目录>/inherited-01.log` | 42 | 任意孩子不是第一孩子 |
| `<实验目录>/direct-01.log` | 42 | 孩子读法不是 k 上的前驱读法 |
| `<实验目录>/cold-domain.log` | 0 | Domain 自删接口冷编，含依赖图 |
| `<实验目录>/cold-keel.log` | 0 | Keel 自删接口冷编 |
| `<实验目录>/cold-tw1.log` | 0 | Tw1 自删接口冷编 |
| `<实验目录>/cold-accept.log` | 0 | Accept 自删接口冷编 |
| `<实验目录>/cold-direct-neg.log` | 0 | DirectNeg 自删接口冷编 |
| `<实验目录>/domain-importclosure.log` | 0 | importclosure 非 Agda 审计 |

##### 其他全部实验工件

- `<实验目录>/YiCNBound.agdai`
- `<实验目录>/YiCNMin.agdai`
- `<实验目录>/YiCNSmall.agdai`
- `<实验目录>/cold-accept.exit`
- `<实验目录>/cold-direct-neg.exit`
- `<实验目录>/cold-keel.exit`
- `<实验目录>/cold-tw1.exit`
- `<实验目录>/domain.dot`
- `<实验目录>/libraries`
- `<实验目录>/logs-status.json`
- `<实验目录>/make_report.py`
- `<实验目录>/source-audit.json`
- `<实验目录>/verification.json`

源码审计 JSON 与最终核验 JSON 的 cold_files/source_audit_hits/domain_graph_local_modules/all_source_hashes_unchanged 字段是复核入口；make_report.py 是报告生成脚本，未参与数学证明。实验生成的 .agdai 仅作为工件保留，不作为主审从头编译的替代。

冻结时间（UTC）：2026-11-14 15:32:01。冻结后不再修改这五个源文件；交主审复核，不提交、不推送。
