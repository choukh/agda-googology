# 用参数化版本取代旧副本（工程） (YiDD)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十五批；外部模型，作者转发 |
| 前缀 | `YiDD` |
| 回报 | 2026-11-14 已返回并由本会话主审复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：用参数化版本取代旧副本（工程，前缀 YiDD）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节。** 主审会从头冷编复核，只认编译过的结果。

#### 作者的决定（2026-11-14，选项原文）
- 本路（选项原文）："(3) 工程：用参数化版本取代旧副本"，说明是 "把已被参数化覆盖的旧副本（候选省 2558 行）改由实例代替；要删或移走已有文件，需你同意"。作者选了它，即同意改动这批已有文件。
- 主审定的做法（最不具破坏性）：**不删除文件**。先整份备份，再把副本改写成重导出参数化版本的薄壳，模块名与导出的定理名不变，依赖它们的文件照常编译。这批副本大多不在 git 里，删掉就无法恢复。
- 范围只限 2026-11-14 新生成的副本 `probes/OCF/Lean/YiVT*`（照搬自更早的原件）。**不动任何原件**（`YiLeg*`、`YiEV*`、`YiPH*`、`YiAN*`、`YiLS*`、`YiME*`、`YiT2*`、`YiMW*`、`YiEX*`、`YiEB*` 等），不动 `YiPM*` 本身。
- 本路是工程，不改任何数学结论，不改树、折叠、合法性的数学内容。

#### 现状（主审复核过的编译事实）
- 回报 `probes/Survey/Reports-2026-11-12/YiVT.md`：32 件 `YiVT*`，其中 24 件是副本（16 件只换导入，8 件有 "改:" 注释的手改）。
- 回报 `probes/Survey/Reports-2026-11-12/YiPM.md`：`YiPM*` 34 件把 F2 的折叠与下降引理一族按表参数化（`YiPMFold.F tb`、`YiPMLSFold.F tb`、`YiPMEVReach.F tb`、`YiPMPHEnd.F tb`、`YiPMANReach.F tb` 等），实例在 `YiPMInst`（`Empty`、`Minimum`）；`YiPMMin*` 重得新主线终点下界（`YiPMMinANLim.tω≼EBOᴿ`、`instω`）。回报里有 16 对证明的局部行数账（5404 → 2846，候选省 2558）与 8 件手改的逐项处理。

#### 要做的（按序）
0. **清单与依赖**（不改任何文件）：
   - 列出 `YiVT*` 里可以由 `YiPM*` 的 `Minimum` 实例代替的副本：逐件写出它导出的名字、在 `YiPM*` 里对应的名字、以及仓库里有哪些文件导入它。
   - 8 件手改的，按 `YiPM.md` 的逐项处理说明哪些能代替、哪些不能（不能的留原样）。
   - 用检索确认没有遗漏的导入者（`grep -rl "OCF.Lean.YiVTxxx" probes src`）。
   - 不成立（例如名字或陈述对不上）就停下回报。
1. **备份**：把清单里每个要改写的文件原样复制到 `probes/Survey/Reports-2026-11-12/attachments/superseded-YiVT-2026-11-14/<原文件名>.txt`。复制前后核对字节数一致。
2. **改写为薄壳**：清单里每个文件改写成：文首 5 行以内说明 "已由 `YiPM…` 的 `Minimum` 实例代替，原文见留档附件"，正文只保留模块声明与 `open import … public`（或按需 `using`/`renaming` 保持原导出名）。导出名与陈述必须与原件一致。
3. **全量验证**：删掉所有改写过的模块、所有 `YiVT*`、所有导入它们的模块的接口，冷编一遍，确认全部退出 0，且原来的结论名（例如 `YiVTANLim.tω≼EBOᴿ`、`YiVTTw2Hi.tω≼twᶻ`、`YiVTTw.twᶻ-R`）仍可用、陈述不变。
4. **账**：交实际省下的行数（代码行计，改写前后对比）与改写文件的清单。

**纪律**：已有引理先检索再写；只改清单里的 `YiVT*` 副本，不改别的任何已有文件；若某件要改陈述才能代替，就不改它，留原样并在回报里列出；停止条件触发时先停下回报。

#### 规则
- 新建文件（若需要）放 `probes/OCF/Lean/`，前缀 `YiDD`。不碰 `src/`、`archive/`，不碰并行的另两路前缀 `YiPJ`、`YiCD`。
- 中文 literate Agda（`.lagda.md`）；改写后的薄壳仍是 literate 格式，选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。
- 仓库文件里不写本机路径。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G（另两路也在编译）。不用 `--ignore-interfaces`，只删要验证的模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 是 Agda 内部错误。报退出码时不要经过管道。
- 不删除任何文件（包括 `YiVT*`）；不在你的临时目录与上面说的文件之外改动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档的正文（备份附件除外；这些由主审更新；回报交给作者转回）。
- 查签名用检索，不整篇读大文件；改写可以写脚本，脚本留在临时目录。
- **停下的条件**：某件代替后陈述对不上；全量验证有任何非 0 退出；8G 耗尽。
- **结束前自查**：全量冷编退出码全 0；检索禁用构造与本机路径为 0；备份附件与改写清单一一对应。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；清单（代替的、不能代替的及原因）；全量验证结果；实际省下的行数；问题表（问题、位置、档）。
2. 文件表：改写的文件、备份附件、冷编退出码。
3. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容。



## 本会话主审复核（2026-11-14）

主审独立复现旧陈述兼容检查为 42（UnequalTerms），并以旧证明填同一陈述的正对照编译 0。24 候选的 109 条直接导入边独立核对无差异，32 个 YiVT 原文均与本轮起点逐字节相同。正式白名单为空、实际节省 0；未进行备份改写或全量冷编。清单仅为语法候选，不是公开 API 认证。

临时源码：[YiDDCompat.agda](attachments/YiDD-YiDDCompat.agda.txt)。原文只机械替换本机路径、降低标题层级；执行方的阶段统计保留，主审确认以本节为准。

## 回报原文（本会话执行）

### YiDD 回报：第 0 步兼容检查未通过，未改写旧副本

#### 1. 判决

本路未改树、折叠、合法性或任何已有数学文件。没有新增值结论，也没有完成副本迁移。参数化版本本身的数学结论沿用上一批；本次检查的是能否保留旧导出陈述而直接重导出。

第 0 步首个兼容检查退出 42，首错为 `UnequalTerms`：保留旧 `YiVTFold.ψs` 的逐字 `ψs-⊵` 陈述，不能用 `YiPMLSFold.F tbᶠ` 的对应证明经定义性转换填入。两边递归头是 `YiPMFold.F.ψs tbᶠ` 与 `YiVTFold.ψs`。不是 LibraryError、未解洞、堆耗尽或超时。

按简报第 0 步不成立、某件代替后陈述对不上的停止条件，在正式改写前停止。正式白名单为空；没有备份、薄壳改写、删接口或全量冷编。24 候选的原文件 SHA-256 均未变，代码行 4075 → 4075，实际省 **0 行**。

这不是数学否定，也没有证明两种折叠不能由外部定理关联；仅报告本次保留旧陈述的直接填值检查失败。没有为使它通过而擅自改写 YiVTFold。

#### 2. 候选与消费者

16 件仅换导入副本、8 件手改副本，共 24 候选。逐件语法候选名、参数化对应名、直接导入者与 rg 对照在 `<实验目录>/inventory.md`、`inventory.json`。

该清单不是已核公开 API。脚本过滤可识别的 where/private 局部名后，记录 854 个语法声明/模块候选及公开重导出语句。初稿误把 YiVTLSTw1 的 where 局部 go 列成平坦导出，主审指出后已过滤；该数字不作成功公开符号计数。首个兼容检查即失败，未逐名作 Agda 导出与陈述认证。

对每件候选分别 rg 检索全限定名，再以精确 import/open import 语句解析对照，共 109 条直接导入边；命中但不是导入的文件另列，没有把模块自身声明当作消费者。

| 原副本 | 待核参数化对应 | 直接导入者数 | 本次兼容状态 |
|---|---|---:|---|
| `YiVTLSTw1` | `YiPMLSTw1.F tbᶠ` | 12 | 未完成编译兼容检查；未改 |
| `YiVTEBShape` | `YiPMEBShape.F tbᶠ` | 5 | 未完成编译兼容检查；未改 |
| `YiVTLSBtbo` | `YiPMLSBtbo.F tbᶠ` | 3 | 未完成编译兼容检查；未改 |
| `YiVTEBBtbo` | `YiPMEBBtbo.F tbᶠ` | 3 | 未完成编译兼容检查；未改 |
| `YiVTMEAnchor` | `YiPMMEAnchor.F tbᶠ` | 15 | 未完成编译兼容检查；未改 |
| `YiVTMEStep` | `YiPMMEStep.F tbᶠ` | 1 | 未完成编译兼容检查；未改 |
| `YiVTT2Desc` | `YiPMT2Desc.F tbᶠ` | 1 | 未完成编译兼容检查；未改 |
| `YiVTEXRow` | `YiPMEXRow.F tbᶠ` | 1 | 未完成编译兼容检查；未改 |
| `YiVTMWPre` | `YiPMMWPre.F tbᶠ` | 6 | 未完成编译兼容检查；未改 |
| `YiVTEVReach` | `YiPMEVReach.F tbᶠ` | 10 | 未完成编译兼容检查；未改 |
| `YiVTPHBase` | `YiPMPHBase.F tbᶠ` | 4 | 未完成编译兼容检查；未改 |
| `YiVTPHCtx` | `YiPMPHCtx.F tbᶠ` | 3 | 未完成编译兼容检查；未改 |
| `YiVTANFam` | `YiPMANFam.F tbᶠ` | 4 | 未完成编译兼容检查；未改 |
| `YiVTANKp` | `YiPMANKp.F tbᶠ` | 1 | 未完成编译兼容检查；未改 |
| `YiVTANLv` | `YiPMANLv.F tbᶠ` | 1 | 未完成编译兼容检查；未改 |
| `YiVTANReach` | `YiPMANReach.F tbᶠ` | 2 | 未完成编译兼容检查；未改 |
| `YiVTLSFold` | `YiPMLSFold.F tbᶠ` | 17 | 旧陈述兼容检查失败；未改 |
| `YiVTT2Frame` | `YiPMT2Frame.F tbᶠ` | 10 | 未完成编译兼容检查；未改 |
| `YiVTEVTw2` | `YiPMMinEVTw2` | 1 | 未完成编译兼容检查；未改 |
| `YiVTEVEnd` | `YiPMMinEVEnd` | 3 | 未完成编译兼容检查；未改 |
| `YiVTPHEnd` | `YiPMMinPHEnd` | 3 | 未完成编译兼容检查；未改 |
| `YiVTANEnd` | `YiPMMinANEnd` | 2 | 未完成编译兼容检查；未改 |
| `YiVTANLim` | `YiPMMinANLim` | 1 | 未完成编译兼容检查；未改 |
| `YiVTTWEnd` | `YiPMMinTWEnd` | 0 | 未完成编译兼容检查；未改 |

##### 8 件手改的准确范围

这是 YiPM 已交的数学范围，不是本次已迁移清单：

| 副本 | 参数化侧的范围 | 本次处置 |
|---|---|---|
| YiVTLSFold | 任意表保持、下降及 ψs-⊵ | 旧 ψs-⊵ 陈述直接填值失败，保留原样 |
| YiVTT2Frame | 通用下降；fallback 带表无条目条件；形状测试在 Inst | 未进入编译兼容检查，保留原样；Generic 中不存在的 flat-lim 不作同名导出 |
| YiVTEVTw2 | 通用下降，最小表 compβ/rowG | 未检查兼容，保留原样 |
| YiVTEVEnd | 最小表 hi1/c₁/path₂ 与出口 | 同上 |
| YiVTPHEnd | 通用下降前缀，具体 path₃/hi1/出口在 Min | 同上 |
| YiVTANEnd | 通用参照/AtN，具体 G/shape/gk/pathN/hi1/出口在 Min | 同上 |
| YiVTANLim | 依赖最小表有限站下界的极限出口 | 同上 |
| YiVTTWEnd | 通用下降，最小表 path₁/hi1/出口 | 同上 |

未把未检查写成不能替代。新写的 YiVTFold、YiVTRel、YiVTTw、YiVTNorel、YiVTEmb、YiVTHi、YiVTTw2Hi、YiVTTw2HiOld 不在本路 24 副本拟改范围内，均未动。

#### 3. 兼容检查

临时源码 `<实验目录>/YiDDCompat.agda`。关键陈述逐字保留旧折叠，只有证明右侧选参数化最小表：

```agda
module Minimum = Param.F tbᶠ
old-statement : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Old.Base ℓ) (j : LF) (w : j ≤ ℓ)
              (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
            → j ⊢ β ⊴ Old.ψs ℓ ε ρ B j w β nβ x
old-statement = Minimum.ψs-⊵
```

`Old` 是 YiVTFold；`Param` 是 YiPMLSFold；tbᶠ 来自 YiPMTable，与 YiPMInst.Minimum.LSFold 同一模块实例。

第 16 行首错，完整日志 `<实验目录>/YiDDCompat.log`：

```text
error: [UnequalTerms]
OCF.Lean.YiPMFold.F.ψs tbᶠ ℓ ε ρ B₁ j w β nβ x !=
Old.ψs ℓ ε ρ B₁ j w β nβ x of type T (Sig j)
when checking that the expression Minimum.ψs-⊵ has type
(ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B₁ : Old.Base ℓ) (j : LF)
(w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ) →
j ⊢ β ⊴ Old.ψs ℓ ε ρ B₁ j w β nβ x
```

使用 safe/without-K/lossy-unification，scratch 另带仓库传染选项，单 Agda、8G。退出码直接记录为42；日志仅自身 Checking。maximum residency 708,646,504 bytes，total memory 1343 MiB。文件没有编译成定理，失败记录不作数学否定。

#### 4. 文件与行数

| 项 | 结果 |
|---|---|
| 正式改写清单 | 空，0 件 |
| 备份附件 | 未进入第1步，0 件，未创建备份目录 |
| 新增仓库 YiDD 模块 | 0 件 |
| 临时 YiDDCompat.agda | 42，UnequalTerms |
| 24 候选旧文件 | inventory.json 所记哈希全部未变 |
| 全量冷编 | 未进入第3步，未执行，不报通过 |
| 实际节省 | 非空非整行注释的 Agda 代码行：4075 → 4075，省0 |

| 问题 | 位置 | 档 |
|---|---|---|
| 新证明返回新递归头，旧陈述保留旧递归头 | YiDDCompat第16行 | 编译失败记录，不是定理 |
| 候选导出没有编译核准 | inventory.md/json | 语法检索事实 |
| 备份/薄壳/全量验证未执行 | 简报第1–3步 | 遵守第0步停止条件 |

#### 5. 偏离与材料

- 已读完整简报、AGENTS、EBOHandbook §4、YiPM 回报的范围、16对候选账和8件手改说明；实际查阅 YiVTLSFold/YiPMLSFold、YiVTFold/YiPMFold、YiPMInst 等相关签名。没有引用未读的外部材料。
- 初版 inventory 的 where 局部名扁平提取有误；主审指出后修正过滤，并标明仅是语法候选，未作为成功 API 对照。生成脚本不进仓库。
- 没有改任何仓库文件、写备份附件、删除源码或接口；没有装包、提交、推送或另派子路。其它并行文件不在本路范围。
- 只做一次旧陈述兼容检查，触发停止后不继续改定义、加相等假设或扩大已有文件范围。没有把上一轮2558候选节省当作本轮节省。

确切临时路径（归档时脱敏）：

- `<实验目录>/report.md`：本回报。
- `<实验目录>/inventory.md`、`inventory.json`：24候选与逐件语法名/消费者清单。
- `<实验目录>/inventory.py`：只读清单脚本。
- `<实验目录>/YiDDCompat.agda`、`YiDDCompat.log`：失败源码与日志。
- `<实验目录>/libraries`：库配置。

建议把 inventory.md/json 作为语法检索附件保留；候选映射不是已认证的替代 API。
