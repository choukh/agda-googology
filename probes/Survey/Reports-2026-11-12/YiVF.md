# View 与 FGH 搬到新主线（基础，第一档交付） (YiVF)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十六批（“外部模型额度很充足，我们可以多线并行”）；外部模型，作者转发 |
| 前缀 | `YiVF` |
| 回报 | 2026-11-14 已返回并由本会话主审复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：View 与 FGH 搬到新主线（基础，第一档交付）（前缀 YiVF）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十六批六路之一（选项原文 "View 与 FGH 搬到新主线"），与并行的其他各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。原主线 `YiRWFold` 的值定理保留作参照。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **纲领第 1 条**（`AGENTS.md`）：中间层若不直接用布劳威尔树，必须有布劳威尔树的 View（内部 View，值上一致）。总概率评估的第一档交付是 "合法的 ψ₀(Λ) 读法闭项，加内部 View 与 FGH"。
- **现有的 View 与 FGH 只在 F2 块上**：`YiLPIface`（接口字段）、`YiLPInst`（`legI : Iface`，F2 折叠 `YiLegFold` 填满各字段）、`YiLPView`（内部 View）、`YiLPFGH`（`fgh = FGH EBOᶜ`，F2 的闭项；第 0 层的树只有零、后继、ℕ 极限，FGH 逐行照 `src/OCF/BTBO.lagda.md` 的 `FGH`）、`YiLPWf`、`YiLPMono`、`YiLPKall`、`YiLPBMOne`、`YiLPNoBM`、`YiLPInto`、`YiLPRead`、`YiLPVal`。先读这些文件的文首。
- 新主线：`YiTBRow.ψ` 配 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（`YiMTTab`）；合法性是类型（`Ok`），折叠与单调互递归。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：把 `YiLPIface` 的接口实例化到新主线折叠的骨架，确认各字段的类型能对上（精简块的层号、路径、表与 F2 的不同）；对不上的字段列出来。不成立就停下回报。
1. **接口实例**：新主线折叠填满 `YiLPIface` 的各字段（照 `YiLPInst`），对一切层号、证据、表与底；能对任意表陈述就对任意表。
2. **内部 View**：照 `YiLPView`，在新主线的闭项上给出内部 View（每个对象可看成零、后继、ℕ 极限（相邻项按合法性步进）或 Ω 极限，值上与对应构造子互相 ≼）。
3. **FGH**：照 `YiLPFGH`，给出 `FGH EBOᶻ` 这个闭的 ℕ → ℕ 函数，并查导入闭包干净（成品候选）。
4. 交一张表：F2 上每个 `YiLP*` 结论在新主线上的对应（已搬、改写后搬、搬不了及原因）。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiVF`（模块名 `OCF.Lean.YiVF…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiCD`、`YiDD`、`YiKQ`、`YiSP`、`YiNX`、`YiXV`、`YiGI`）。成品候选文件（View、FGH）用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包干净，文首标明 "成品候选"；其余标明 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有九路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
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

主审读过原 Iface 的固定 F2 类型和两份临时源码；独立删临时接口后，投影骨架冷编为 0，原首字段赋值复现 42（UnequalTerms，YiLegBlock.L 与 YiRWBlock.L 不匹配）。按简报第 0 步停止；没有交付新 View/FGH，也没有数学否定。仓库 YiVF 模块为 0，原数学文件未动。

临时源码：[YiVFSkel.agda](attachments/YiVF-YiVFSkel.agda.txt)、[YiVFFieldCheck.agda](attachments/YiVF-YiVFFieldCheck.agda.txt)。原文只机械替换本机路径、降低标题层级；执行方的阶段统计保留，主审确认以本节为准。

## 回报原文（本会话执行）

### YiVF 完整回报

#### 1. 判决与范围

对纲领与目标的意义：本路没有交付新主线的内部 View 或闭的 FGH，因此没有补齐第一档交付。第 0 步按原接口逐字检查时失败，已触发简报的停止条件；后续第 1—3 步未执行。失败是固定 F2 类型的接口与新主线类型不对接的检查事实，不是新主线没有 View、没有 FGH 或不能发展接口的否定定理。

新主线折叠本身的临时骨架通过检查：对任意 `YiRWBlock.L`、`Ok`、`YiTBRow.Rb` 和 `YiRWFold.Base`，由 `YiTBRow.ψ` 投影出的 `ψ⊥ᵀ`、`ψsᵀ` 及其非零证明均可定义。随后把 `ψ⊥ᵀ` 交给 `YiLPIface.Iface.ψ⊥` 的精确字段类型，Agda 在第一参数的层号类型处拒绝，退出 42。

依据简报「第 0 步不成立」的停止条件停止，没有把任务改成重写接口，也没有改树、折叠或合法性。没有新增仓库源码；所有实验仅在临时目录。本回报第 3 节给出第 4 步所需的未搬状态表，不能把它读成已验证的搬运可行性表。

- 第 0 步：临时骨架编译退出 0；直接接口字段检查退出 42。
- 第 1 步：未执行，未定义新主线 `Iface` 实例。
- 第 2 步：未执行，未新增内部 View。
- 第 3 步：未执行，未新增 `FGH EBOᶻ`，未运行成品候选导入闭包审计。
- 第 4 步：仅整理逐模块的未搬状态及原接口字段差异，不声称改写后已经搬运。

##### 问题表

| 问题 | 位置 | 档与证据 |
|---|---|---|
| 原 `Iface` 的层号、树、路径、底固定为 F2，记录没有块参数 | `probes/OCF/Lean/YiLPIface.lagda.md:18–21,80–87` | 源码检查；临时字段赋值由检查器拒绝，有限编译检查 |
| 新主线投影骨架能对任意 `Ok`、`Rb`、`Base` 写出 | `YiVFSkel.agda:12–26` | 编译构造与编译定理，退出 0 |
| 该骨架能否满足逐条改写后的全部接口律 | 未开始 | 未验证；没有否定定理 |
| 新主线内部 View、部分良基、对象层步进与闭 FGH | 未开始 | 未验证；没有否定定理 |

首个临时文件与首轮编译日志创建于 2026-11-14 20:23:57 +0800，首轮编译约 1.875 秒；在任务开始后的 30 分钟期限内完成。

#### 2. 源码、编译与日志

临时目录：`<实验目录>`。
完整回报：`<回报原文>`。
仓库源码：无；`probes/OCF/Lean/YiVF*` 无新增文件。

全部实验源码：

1. `<实验目录>/YiVFSkel.agda`
2. `<实验目录>/YiVFFieldCheck.agda`

配置：`<实验目录>/libraries`，两行库路径与简报一致。
生成接口：`<实验目录>/YiVFSkel.agdai`。失败文件没有成功接口。

| 源码 | 代码行口径 | 首编退出码 | 删自己接口后的冷编退出码 | 冷编最大 residency（RTS 原数） | 冷编总内存 in use |
|---|---:|---:|---:|---:|---:|
| `YiVFSkel.agda` | 20 行代码；26 行物理源码 | 0 | 0 | 141,566,096 bytes | 237 MiB |
| `YiVFFieldCheck.agda` | 9 行代码；13 行物理源码 | 42 | 不适用：故意检查失败，未交成功文件 | 首轮 153,332,224 bytes | 首轮 263 MiB |

代码行计数排除空行与普通注释，保留选项行、模块头和导入。

`YiVFSkel` 首轮最大 residency 为 153,565,048 bytes，总内存 in use 257 MiB。所有 Agda 均带 `+RTS -M5G -s -RTS`，同时仅一个 Agda，未增加堆上限。

全部编译日志：

- `<实验目录>/YiVFSkel.log`：首轮退出 0。
- `<实验目录>/YiVFSkel-cold.log`：只删本实验 `YiVFSkel.agdai` 后冷编，退出 0；唯一 `Checking` 行是 `YiVFSkel`。
- `<实验目录>/YiVFFieldCheck.log`：退出 42，首错是 `UnequalTerms`，不是 `LibraryError`。

可复现命令（从仓库根运行）：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -l standard-library -i src -i probes -i <实验目录> <实验目录>/YiVFSkel.agda > <实验目录>/YiVFSkel-review.log 2>&1
YIVF_EXIT=$?
echo "exit $YIVF_EXIT"
```

将文件名换成 `YiVFFieldCheck` 即可复现原接口字段不对接；预期退出码是 42。上面的 `*-review.log` 是建议复核命令的输出名，目前没有生成，不计入已存在日志。

#### 3. 接口差异与 F2 对应表

##### 3.1 原接口为什么不能直接实填

原文件实际是：

```agda
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold using (Base; base; b⊥; n⊥; bs; ns; chB)
record Iface : Set₁ where
  field
    ψ⊥ : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → Tr ℓ → Tr zero
```

`L` 等在记录声明前已经固定。记录没有参数可把它们换成 `YiRWBlock.L`、`Tr`、`Ok`、`Rb` 与新 `Base`。这不是某条深层接口律的证明失败；还没有检查到那些律。

已核对的表示差异如下。这里的「需要改写」是源码层的判断，不是改写后的数学定理：

| 成分 | F2 | 新主线 |
|---|---|---|
| 层号 | `zero/suc/lim/Ωₗ`，类型 `YiLegBlock.L` | `zero/nd s h`，类型 `YiRWBlock.L` |
| 树与第一位置序 | `YiLegBlock.T/Lt` | `YiRWBlock.T/Lt`，不同的归纳类型 |
| 后继、ℕ 极限层的槽位 | 直接为孩子的 `Pos⁼` 或 `Σ ℕ Pos⁼` | 统一包在 `PK s ⊎ Σ (Ch s) Pos⁼` 中；非 Ω 形状的 `PK` 是 `⊥` |
| 路径 | `ins/inl/inlu/inb/inu/ink/self` | `inc/inu/ink/self`；不能直接传旧路径 |
| 证据 | 分开的 `Ev` 与 `Rt` | `Ok` 收拢合法性与相邻路径；另有 `Rb` 可缺比较表，不能把 `Rb` 当作旧 `Rt` |
| 底 | `Base` 记录，独立的 `b⊥/n⊥`，以及 `bs/ns` | `(j : L) → j ≤ ℓ → Tr⁺ j`；没有独立的 `b⊥` 字段 |
| 折叠 | 两个函数 `ψ⊥/ψs`，另给非零证明 | 一个 `ψ` 输出 `Tr⁺ j`；可投影函数与非零证明 |
| 保留 | CPS `kp⁼`，带 `Ev/Rt` | 返回 `Keep` 的 `kp⁼`，带 `Ok`；`Keep` 为可缺槽位、换型及首分支等式 |

临时 `ψ⊥ᵀ` 选择 `B zero (z≤ ℓ)` 为起点。这是检查新主线折叠类型的选择，没有证明它恢复 F2 独立 `b⊥` 的全部语义，也没有把此选择写入任何仓库定义。

##### 3.2 24 个字段的检查状态

所有字段的旧类型都引用固定的 F2 层号/树；所以直接实填首先都需要跨类型处理。实际编译只到首字段即停止，没有声称其余 23 个字段分别被检查器拒绝。

| 字段（列全） | 本轮结果 |
|---|---|
| `ψ⊥` | 原类型直接赋值失败：`YiLegBlock.L !=< YiRWBlock.L`。对应 RW 投影骨架编译通过，但不具有原字段类型。 |
| `ψs`、`nz⊥`、`nzs` | 对应 RW 投影骨架编译通过；未在原字段类型中实填。 |
| `kp⁼` | 未实填。原字段是 F2 的 CPS 类型，新主线返回 `Keep`；两者直接类型不同。 |
| `J2-suc`、`J2-lim`、`J2-limu`、`J2-Ωk`、`J2-Ωu` | 未检查律；层号构造子、证据、路径、底和折叠引用均需处理。 |
| `J2⊥-suc`、`J2⊥-lim`、`J2⊥-Ω` | 未检查律；还涉及 F2 独立底分量与新主线起点选择。 |
| `mono⊥`、`monos` | 未检查律；新主线已有 `YiTBRow.mono`，本轮未完成对应定理的接口实填。 |
| `self-up` | 未检查律；涉及新主线统一孩子类型与 `Up`。 |
| `node`、`node⊥` | 未检查律；涉及 CPS 保留与 `Keep/node⁺` 的对应。 |
| `kp-fwd`、`kp-bwd` | 未检查律；涉及新路径及 `way` 的表示。 |
| `J2-lim-bwd`、`J2-lim-fwd` | 未检查律；还涉及新孩子底和带表折叠。 |
| `kstep`、`kall` | 未检查律；`Nx`、证据、`InB/prE/Kept` 也固定为 F2，需要另述对应陈述。 |

`dS/dL/dW/step` 是记录里的派生定义，不是另外四个字段。它们同样使用旧 `chB`、底投影和旧路径；不能原样应用到 RW 类型。

##### 3.3 F2 的每个 YiLP 模块在新主线的对应状态

「未搬」表示停止后未执行；不能改写成「搬不了」。未完成任何 View/FGH 成品候选，因而没有「已搬」或「改写后搬」的定理。

| F2 模块与结论 | 新主线本轮对应 | 状态与原因 |
|---|---|---|
| `YiLPIface`：`Iface` 字段、`Nx/Ev-Nx/Rt-Nx`、`InB/prE/brE/Kept` | 临时 `YiVFSkel` 仅给四个投影骨架 | 未搬；原记录类型直接实填失败。 |
| `YiLPInst`：`legI`、塔与 `Nx` 的三个等式、`kall-legI-tw` | 无新接口实例 | 未搬；第 0 步停止。 |
| `YiLPVal`：值、前序自反传递、`emb-≈/valCh-≈`、加法与抬升单调、`val-mono/val-leg/val-+` | 无 | 未搬；第 0 步停止，未改写值类型。 |
| `YiLPView`：`view/brwView`、`upz/mapUp` 分解 | 无 | 未搬；第 0 步停止，未生成新主线内部 View。 |
| `YiLPWf`：`parts⊆/wf/vrec/objStep` | 无 | 未搬；第 0 步停止。 |
| `YiLPFGH`：`FGH/FGHᵥ`、`FGH-val/FGH-1/fgh-1`、闭 `fgh`，及 `test₀` 有限测试 | 无 | 未搬；未定义新 `FGH EBOᶻ`，也未运行数值测试。 |
| `YiLPKall`：`kall/kall-tw` | 无 | 未搬；第 0 步停止。 |
| `YiLPMono`：`ψs-start/Up-base/bm-zero⊥/bm-zeros`，`BM⊥/BMs/BaseMonoΩt/CoordMono` 陈述，条件定理 `bm-Nx` | 无 | 未搬；第 0 步停止，原条件未在新主线验证。 |
| `YiLPBMOne`：`am⊥/ams/bm-one` | 无 | 未搬；第 0 步停止。 |
| `YiLPNoBM`：`no-bm/no-bm-all` | 无 | 未搬；没有对新主线重证否定，也没有据此否定新主线。 |
| `YiLPRead`：`readᴸ`、`read≼V/V≼read/≼→ᴸ/≼→read/FGH-read` | 无 | 未搬；第 0 步停止，未引入参照框架。 |
| `YiLPInto`：`B₀⊴dL/into-0`，条件 `into-bm/into-all-bm/into-coord`，`chain-B₀/chain-B₁` 有限测试 | 无 | 未搬；第 0 步停止，未声称条件已满足。 |

#### 4. 本轮编译构造与定理

以下逐字陈述均在临时模块 `YiVFSkel` 中；`L/Tr/◃` 是 `YiRWBlock`，`Ok/≤/z≤` 是 `YiRWPath`，`Base` 是 `YiRWFold`，`Rb/ψ` 是 `YiTBRow`。所有表和底都量化，没有限定为 `rbᶻ` 或 `B₀`。

##### `ψ⊥ᵀ`

```agda
ψ⊥ᵀ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → Tr ℓ → Tr zero
```

白话：选择底在零目标路径上的分量为起点，投影新主线折到零层的输出树。
文件：`<实验目录>/YiVFSkel.agda:12`。
档：编译构造；不是旧接口实例。

##### `ψsᵀ`

```agda
ψsᵀ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ
    → (β : Tr j) → j ⊢ zero ◃ β → Tr ℓ → Tr j
```

白话：任意目标路径和非零起点的折叠输出树。
文件：`<实验目录>/YiVFSkel.agda:15`。
档：编译构造。

##### `nz⊥ᵀ`

```agda
nz⊥ᵀ : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (x : Tr ℓ)
     → zero ⊢ zero ◃ ψ⊥ᵀ ℓ o r B x
```

白话：上述零目标折叠的输出非零。
文件：`<实验目录>/YiVFSkel.agda:19`。
档：编译定理。

##### `nzsᵀ`

```agda
nzsᵀ : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ)
     → (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
     → j ⊢ zero ◃ ψsᵀ ℓ o r B j w β nβ x
```

白话：上述任意目标折叠的输出非零。
文件：`<实验目录>/YiVFSkel.agda:23`。
档：编译定理。

这两条非零定理都只是已有 `ψ` 返回的 `Tr⁺` 的第二投影，没有重证折叠单调或任何接口律。前提不是空域：已有 `Ok-tw`、`Ok-Λ`、`rbᶻ`、`B₀`、`z≤` 和 `Ωt` 提供规范的合法性、表、底、路径和非零起点；这些定义的源码已读，但本轮没有编译新的闭项实例，不能把它算为新的强度验收。

#### 5. 第一个障碍

首个失败的检查名：`YiVFFieldCheck.check-ψ⊥`。
原字段位置：`probes/OCF/Lean/YiLPIface.lagda.md:82`。
临时失败位置：`<实验目录>/YiVFFieldCheck.agda:13.14-17`。

失败文件用 `TypeOf` 直接取得投影的类型，没有手抄或削弱字段类型：

```agda
TypeOf : ∀ {a : Level} {A : Set a} → A → Set a
TypeOf {A = A} _ = A

check-ψ⊥ : (I : Iface) → TypeOf (Iface.ψ⊥ I)
check-ψ⊥ I = ψ⊥ᵀ
```

原日志首错：

```text
error: [UnequalTerms]
OCF.Lean.YiLegBlock.L !=< OCF.Lean.YiRWBlock.L
when checking that the expression ψ⊥ᵀ has type TypeOf (Iface.ψ⊥ I)
```

档：有限编译检查失败，非编译否定定理。没有证明「任意适配都不可能」，没有证明改写接口的律不成立，也没有把该错误归到 LPO、WLPO、W/V/C 等墙。

建议（仅建议，未执行）：若后续重新派发，应先明确要把 `YiLPIface` 作为陈述模板，另写带新主线类型的接口，而非构造原 `Iface` 的实例；同时明确 F2 独立 `b⊥` 与新主线底零分量的关系、`Ok/Rb` 的参数化位置，以及 CPS 保留字段怎样改述。不能把通过四个投影骨架当作全部接口律可满足的证明。

#### 6. 偏离、事故、自查与阅读边界

- 没有重新设计树、折叠或合法性；没有修改原 `YiLPIface`；没有新增另一版本的一般接口。
- 停止后仅冷编已成功的临时骨架并整理回报，没有继续第 1—3 步。
- 没有仓库源码或文档改动，没有修改其他路文件，没有提交或推送，没有派子路。
- 同时一个 Agda、5G；无堆耗尽、无超时、无内部错误。唯一退出 42 是上述预期类型不对接；不是缺库。
- 初次批量阅读输出过长，随后分别重读原接口、实例、View、FGH 与其余模块文首，并对类型定义和签名定点检索。未以被截断的内容作唯一依据。
- 新源码禁用构造检索为 0：`postulate`、停机/正性绕过、`trustMe`、K、`--irrelevant-projections`、`--cubical`（排除允许的 `--cubical-compatible`）、洞与问号均无。临时源码只有所需安全选项及正式定义。
- 仓库无 YiVF 文件，故仓库新文件本机路径检查、逐文件冷编与成品候选导入闭包检查均无对象；未把「未运行」写成「检查干净」。临时文件没有本机绝对路径常量。
- 首轮与冷编的 `YiVFSkel` 日志各只有自己模块的 `Checking` 行。失败日志只有 `YiVFFieldCheck` 的 `Checking` 行及错误；不算通过文件。
- 代码来源：骨架直接投影 `YiTBRow.ψ` 的 `Tr⁺` 结果；旧字段签名来源为完整读过的 `YiLPIface`。没有抄入未读证明。
- 已完整读：任务简报、`AGENTS.md`、`EBOHandbook.md` 第 4 节、`YiLPIface`、`YiLPInst`、`YiLPView`、`YiLPFGH`、`YiRWBlock`、`YiMTTab`；读过 `YiTBRow` 的折叠与单调代码以及相关签名。
- 已按要求读全部 `YiLP*` 文首。对应表中 `YiLPMono/BMOne/NoBM/Into/Read/Kall/Val/Wf` 的原有结果以其文首和定点签名为来源，没有在本轮重新编译这些旧结果，也没有完整审阅其每条证明。它们在表里只是旧结果索引，不算本轮独立复核过的事实。
- `src/OCF/BTBO.lagda.md` 的 FGH、本批其他路、`YiMTValue` 的全部强度证明没有完整读或独立复核；本回报没有据它们作新的数学结论。新主线的指定采用状态来自作者简报及当前 README，不从旧文件文首的历史「未经采纳」字样推导新裁决。

本路已定稿结束，保留上述全部源码和日志，供主审独立冷编复核。
