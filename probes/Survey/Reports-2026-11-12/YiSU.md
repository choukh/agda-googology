# StepU 的可满足性与改写（数学，配对否定） (YiSU)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十九批；外部模型，作者转发 |
| 前缀 | `YiSU` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：StepU 的可满足性与改写（数学，配对否定）（前缀 YiSU）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十九批四路之一（选项原文 "StepU 的可满足性与改写 (Recommended)"），与在跑的 YiXV、YiFM、YiLL、YiMX 在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- **再上一批**（主审复核过）：`YiLKSlot.steps→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → Laws.LowKeep gradedᵍ domsᵍ`（`YiLKIface`、`YiLKFold`、`YiLKSlot`；回报 `probes/Survey/Reports-2026-11-12/YiLK.md`）：折向第 0 层的各行对一切层号证完，剩每层一条槽位回灌的步进 `StepU`。第一档交付（合法闭项、内部 View、FGH）已在新主线上编译（`YiVW*`）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **要检查的陈述**（`YiLKIface.StepU`，逐字）：
  ```agda
  StepU ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
    → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
    → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
    → GR.Low ℓ p (E.γT (t ++ a) ν n) c
    → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
    → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)
  ```
  其中 `feed ℓ o r B p g c = fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c)))`（`YiLKIface` 第 40–59 行）。
- `YiLKSlot.steps→lowKeep` 用它推出 `LowKeep`；没有任何层号上的全称实例。YiLK 回报的量化域警示（判断）："本路的 `StepU` 对任意前缀 t、底满足 OKB、任意 g 及一个分支的关系证据要求一步结论；它未额外要求 g 在所有参照坐标上满足整个 Ω 分支律。因此它是明确的充分条件，其全域可满足性需单独检查"。
- 观察（主审，未编译）：`feed` 只用到 `g c`；底 B 只受 `OK B` 约束，`StepU` 里没有把底与前缀 t 联系起来的条件（`LowKeep` 里对应的是 `Bd b w β K`）。
- AGENTS："律带公共上界, 构造与否定配对"；"量化域先取带证据的读回域"，反例对象不在读回域内的否定读作 "谓词太宽"。并行的 YiGT 在构造方向攻同一处。
- `eboᵍ` 的量化域 `domsᵍ`（`YiGIInst` 第 46–49 行）：`Gx = λ ℓ x → x ≡ proj₁ (O.Ωt ℓ)`，`Gb = λ ℓ b → proj₁ (proj₂ b) ≡ MT.rbᶻ ℓ`，`Gl` 同 `Gx`；即 `LowKeep` 本身只对每层的 Ω 树与主线比较表要求。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：取有 Ω 槽位的最小层号（例如 `fn 1` 或 `tw 1`），用规范底 `B₀` 与几种退化的选择（前缀 t 很大而底不随之变；g 在 c 以外任意；ν、a 取最小的合法值），把 `StepU` 的前提逐个实填，判定结论成立还是不成立（编译实例或编译反例）。前提不可满足就换一组，并在回报里说明。
1. **若有反例**：编译 `(∀ ℓ → StepU ℓ) → ⊥`（或在指定层号上的否定），说出缺的是哪一种联系（底与前缀、g 的整条分支律，或别的）；写出补上这一联系的 `StepU′`，并重编 `steps′→lowKeep : Leaf → (∀ ℓ → StepU′ ℓ) → LowKeep`（复用 `YiLKSlot` 的证明）；再在最小层号上给 `StepU′` 一个实例，说明它可满足。
2. **若小实例上都成立**：给出最小层号上 `StepU` 的编译实例，并精确写出一般情形还缺什么；不写 "可满足"，除非有全称实例。
3. 与 YiGT 共用 `YiLKIface`，不改它；新的陈述放你自己的文件。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiSU`（模块名 `OCF.Lean.YiSU…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiFM`、`YiLL`、`YiMX`、`YiGT`、`YiPF`、`YiPX`）。验收文件，文首标明。
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



## 首次回报原文（原任务仍继续）

主审复核与续作原因另见 LOG；首次报告的结束判断不自动成为主审结论。

### YiSU 完整回报（2026-11-14）

#### 1. 判决与任务完成范围

对纲领与目标的意义：本路否定了一个过宽的验收充分接口，未改树、折叠、合法性或证书，未增加大数或 EBO 强度成果。`StepU (fn 1)` 已有编译反例，而且反例满足 g 的整条分支律。因此，把单支前提补成整条分支律不能修复这个接口。底与前缀的联系在该反例中确实缺失；补上此联系后，最小层号上有全称步进实例及非空的前提实例。

原任务中的 `steps′→lowKeep : Leaf → (∀ ℓ → StepU′ ℓ) → LowKeep` **没有交付**。直接复用 `YiLKFold` 会要求它的 `OK B` 或现有 `Bdᵍ` 提供新增的底前缀关系；这两个供给命题都有编译反例。此事实不证明任何可能的 `steps′→lowKeep` 证明都不存在，也不否定 `LowKeep` 或规范塔域。本路停在此处，不改原接口的量化域，不以已被否定的全域 `Leaf` 消去矛盾来交付条件终点。

最新的 `YiLLLeafNeg.noLeaf` 已由主审冷编 0 是派发信息，本路没有独立重编它；最终五个文件不导入该文件，也不调用其结论。早期临时上界文件用过该文件的数个有限句法引理；正式 `YiSUBound` 改为任意 n 的独立下界，摆脱该并行文件的依赖。

##### 第 0 步

第一个临时文件：`<实验目录>/YiSUMin.agda`，日志 `YiSUMin-1.log`，退出码 0，约 15.514 秒，最大 residency 1,368,065,896 字节。在读取简报和手册后的首轮检查完成，未超过 30 分钟。

初始临时实例取 `ℓ = fn 1`、`o = tt , λ _ → tt`、`p = inj₂ (tt , inj₁ tt)`、`r = rb-no ℓ`、`B = B₀ ℓ`、`ν = []`、`a = Ω₁ = E.Ωt (E.natT 1)`、`n = 0`、`c = suc zero`，g 恒为源层的 `suc zero`。所有前提实填；空前缀有一步实例。前缀 1 时目标是 `E.ψ [] (E.natT 2) ∷ []`，输出是 `next⁺ 1`。没有把不可满足的前提当成反例。

正式文件把 g 加强为：零分支返回零，其余分支把第 0 层树原样嵌入 `fn 1`。`whole-branch` 证明它在所有参照坐标上满足整条 Ω 分支律；这时同一 c 的输出和失败结论保持。正式 g 与早期恒值 g 是两组检查，回报的主要否定用正式 g。

| 正式实例的前提 | 实填位置 | 档 |
|---|---|---|
| `Ok ℓ` | `YiSUNeg.o` | 编译闭项 |
| `OK (B₀ ℓ)` | `YiSUNeg.okB`，逐点反身 `⊴r` | 编译定理 |
| `GR.Nu ℓ p []` | `YiSUNeg.nu = GR.c0 refl` | 编译闭项 |
| `E.cof a ≡ E.cΩ []` | `YiSUNeg.cof-a = refl` | 编译定理 |
| 当前 γ 坐标的 `Low` | `YiSUNeg.low = H.m1 refl H.mz` | 编译闭项 |
| 当前分支的 `R` | `YiSUNeg.branch`，由整条分支律得到 | 编译闭项 |
| 整条分支律 | `YiSUNeg.whole-branch` | 编译定理 |
| γ 的下一项为 ψ₀(2) | `YiSUNeg.gamma1 = refl` | 编译的具体化简 |
| 实际回灌为 `next⁺ 1` | `YiSUNeg.out = refl` | 编译的具体化简 |
| 该输出不能承载 ψ₀(2) | `YiSUBound.no-ω²` | 编译否定定理 |

任务顺序：第 0 步完成；第 1 步的原接口否定、改写接口、最小层全称实例完成；第 1 步的原 `LowKeep` 归约未完成；第 2 步不适用；第 3 步遵守，未改共享 `YiLKIface`。

##### 问题表

| 问题 | 位置 | 判决与档 |
|---|---|---|
| 原全层 StepU 是否有实例 | `YiSUNeg.no-steps` | 否，编译否定 |
| 是否只是缺 g 的整条分支律 | `YiSUBridge.no-whole` | 该补法仍不成立，编译否定 |
| 是否存在可满足的底前缀联系 | `YiSUMin.prefix-zero`、`YiSUBridge.prefix-next` | 空前缀与前缀 1 均实填，编译定理 |
| 改写后最小层的全称步进 | `YiSUMin.step′-one` | `StepU′ (fn 1)`，编译定理 |
| 原 OK 能否给新增联系 | `YiSUBridge.no-OK-prefix` | 不能，编译否定 |
| 原 Bd 能否给新增联系 | `YiSUBridge.bd`、`no-Bd-prefix` | 前提有实例而结论假，编译否定 |
| 是否仍有别的办法证明原 LowKeep | 未证明亦未否定 | 判断：本路未走通；没有关闭路线 |
| 是否触及规范塔强度 | 无 EBO 值定理 | 未作判定 |

#### 2. 文件与冷编

代码行口径：Agda 代码块内非空、非单独注释行，包含模块头与导入。五个文件合计 354 行。它们全部是验收侧文件，不能计为前三层新增定义成本或强度提升。

每件均在定稿后删除**自身**接口，再单独运行 Agda，依赖接口保留；每个日志恰有该模块自己的一个 `Checking` 行，0 条 warning。没有使用 `--ignore-interfaces`，始终单 Agda、`+RTS -M5G -s -RTS`。

| 文件（均在 `probes/OCF/Lean/`） | 代码行 | 总行 | 冷编退出码 | `+RTS -s` 最大 residency（字节） | 冷编秒 |
|---|---:|---:|---:|---:|---:|
| `YiSUBound.lagda.md` | 148 | 186 | 0 | 1,005,436,616 | 11.782 |
| `YiSUIface.lagda.md` | 32 | 42 | 0 | 1,418,659,096 | 15.082 |
| `YiSUNeg.lagda.md` | 66 | 93 | 0 | 1,399,128,384 | 16.196 |
| `YiSUMin.lagda.md` | 60 | 71 | 0 | 1,429,496,712 | 15.685 |
| `YiSUBridge.lagda.md` | 48 | 64 | 0 | 1,428,250,776 | 15.841 |

冷编日志和执行记录均在 `<实验目录>/`：`YiSUBound-cold.log`、`YiSUIface-cold.log`、`YiSUNeg-cold.log`、`YiSUMin-cold.log`、`YiSUBridge-cold.log`、`cold-results.json`、`cold-summary.json`、执行脚本 `cold.py`。

编译配方（从仓库根目录，替换文件名）：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiSUNeg.lagda.md > <实验目录>/YiSUNeg-cold.log 2>&1
```

冷编脚本用 `subprocess.run` 直接取得 Agda 退出码，不经过管道。库文件含简报指定的 stdlib 与 cubical 两个路径。编译过程中没有超过 5G、没有堆耗尽、没有超时或内部错误。

#### 3. 定理表及接口原文

下表陈述按源码逐字抄出，多行签名的空白折叠为一行。`YiSUNeg` 中 `ℓ = fn 1`、`t = E.natT 1`、`ν = []`、`a = E.Ωt (E.natT 1)`；`YiSUBound.ωᶜ = proj₁ (next⁺ (Ωt zero))`，`ωᵀ = E.ψ [] (E.natT 1) ∷ []`。名字中的 ω² 是该具体参照 ψ₀(2) 的标记；`small-bound` 是 **句法项序** 的上界，没有借助无条件出口把它改说成新的序数值验收。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `fin-bound` | `∀ {t x n} → H.M⁰ t x → Fin x n → t ≤ᵀ E.natT n` | 高度 n 的有限树只能承载句法上不超过 n 的参照 | YiSUBound | 编译定理 |
| `small-bound` | `∀ {t x} → H.M⁰ t x → Small x → t ≤ᵀ ωᵀ` | 有限树与指定 ω 输出的参照项均不超过 ω | YiSUBound | 编译定理 |
| `no-ω²` | `H.M⁰ (E.ψ [] (E.natT 2) ∷ []) ωᶜ → ⊥` | 具体 ω 输出不承载 ψ₀(2) | YiSUBound | 编译否定 |
| `whole-branch` | `∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c)` | 反例的整条分支律实填 | YiSUNeg | 编译定理 |
| `gamma1` | `E.γT (t ++ a) ν 1 ≡ (E.ψ [] (E.natT 2) ∷ [])` | 非空前缀把下一项提高到 ψ₀(2) | YiSUNeg | 编译的具体化简 |
| `out` | `feed ℓ o (rb-no ℓ) (B₀ ℓ) p g c ≡ ωᶜ` | 回灌仍是指定 ω 输出 | YiSUNeg | 编译的具体化简 |
| `small-step` | `GR.Low ℓ p (E.γT a ν 1) (feed ℓ o (rb-no ℓ) (B₀ ℓ) p g c)` | 同一组参数在空前缀下一步成立 | YiSUNeg | 编译实例 |
| `no-step` | `StepU ℓ → ⊥` | 最小层的原 StepU 为假 | YiSUNeg | 编译否定 |
| `no-steps` | `(∀ ℓ → StepU ℓ) → ⊥` | 原全层 StepU 为假 | YiSUNeg | 编译否定 |
| `rd-zero` | `∀ {ν} → GR.Rd zero ν → ν ≡ []` | 第零层的层号读法只能是零 | YiSUMin | 编译定理 |
| `to-one` | `∀ {a x} → GR.R (fn 1) a x → F.M 1 a x` | 最小层的分级关系转入已有遗传有限族 | YiSUMin | 编译定理 |
| `step′-one` | `StepU′ (fn 1)` | 带底前缀证据的最小层步进有全称实例 | YiSUMin | 编译定理 |
| `prefix-zero` | `PrefixU (B₀ (fn 1)) []` | 规范底满足空前缀的新前提 | YiSUMin | 编译定理 |
| `no-whole` | `WholeU ℓ → ⊥` | 只补整条分支律仍为假 | YiSUBridge | 编译否定 |
| `no-prefix-one` | `PrefixU (B₀ ℓ) t → ⊥` | 规范底不承载本例的前缀 1 | YiSUBridge | 编译否定 |
| `no-OK-prefix` | `((B : Base ℓ) → OK B → PrefixU B t) → ⊥` | 原底下界不能供给前缀联系 | YiSUBridge | 编译否定 |
| `bd` | `Bdᵍ (o , MT.rbᶻ ℓ , B₀ ℓ) (z≤ ℓ) (next⁺ (Ωt zero)) t` | 供给否定中的原 Bd 前提有实际实例 | YiSUBridge | 编译闭项 |
| `no-Bd-prefix` | `(Bdᵍ (o , MT.rbᶻ ℓ , B₀ ℓ) (z≤ ℓ) (next⁺ (Ωt zero)) t → PrefixU (B₀ ℓ) t) → ⊥` | 本例原 Bd 不能供给新增前提 | YiSUBridge | 编译否定 |
| `ok-next` | `OK Bnext` | 逐点 next 的底仍满足原下界 | YiSUBridge | 编译定理 |
| `prefix-next` | `PrefixU Bnext t` | 该底承载前缀 1，新前提不空真 | YiSUBridge | 编译定理 |
| `linked-step` | `GR.Low ℓ p (E.γT (t ++ a) ν 1) (feed ℓ o (rb-no ℓ) Bnext p g c)` | 补上联系后，本反例的一步成立 | YiSUBridge | 编译实例 |

辅助的有限阶基本列下界、前驱、句法比较与 Small 保持引理均在 `YiSUBound` 源码；它们不是另一个强度口径。源码中 `nu`、`cof-a`、`low`、`branch`、`okB` 是上述反例前提的显式见证。

新接口的逐字定义：

```agda
PrefixU : ∀ {ℓ} → Base ℓ → E.T → Set
PrefixU {ℓ} B t = (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → GR.R (at ℓ p) (E.ψ ν t ∷ []) (proj₁ (B (at ℓ p) (posW ℓ p)))

StepU′ : L → Set
StepU′ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t
  → (a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)

WholeU : L → Set
WholeU ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ)
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
  → (n : ℕ) (c : Br ℓ p) → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)
```

`StepU′` 不额外要求整条分支律；最小层证明使用当前分支关系与底前缀关系，通过已有 `YiLTFold.LF` 一步得到结论。一般层是否够用未证明。`WholeU` 是另一种被否定的候选，不应与 `StepU′` 混读。

#### 4. 第一个障碍及停止位置

第一个数学障碍在 `YiLKIface.StepU` 的任意前缀 t：`feed` 看不到 t，而 `OK B` 不要求底承载 t。不是层号三歧、不是 `obs→dec`，本路没有把它归入既有 W/V/C 或 LPO 壁垒。

两种补法的检查：

1. 只加 g 的整条分支律：`YiSUBridge.no-whole` 直接否定同一处的步进；反例的 `whole-branch` 是全称证明，不是有限抽样。
2. 加底前缀证据：`step′-one` 在最小层全称实填，`prefix-zero` 与 `prefix-next` 证明前提可满足。但直接沿 `YiLKFold.Fold.chain` 复用证明时，模块参数只有 `gb : OK B`，没有 `PrefixU B t`；到 `reduce` / `slots→lowKeep`，`Bdᵍ` 的第一分量是 **β** 的前缀关系，第二分量仍只是 `OK B`。`no-OK-prefix` 与带明确 `bd` 的 `no-Bd-prefix` 否定了这两个直接供给办法。

因此没有把原 `steps′→lowKeep` 写成已编译定理，也没有借全域 Leaf 为假来获得空真的条件结论。此处的结论限于上述两个明确定义的供给命题；原 LowKeep 是否还能以别的外部论证证明，仍是未走通。

停止纪律的读法：同一槽位的两种修补已分别完成可编译检查，不能再把缺失条件当作工程洞反复补。本路不继续改第三种接口，不改目标、树、折叠、合法性或原 Bd；将下一步决定交回主审。没有声称整个研究路线已被否定。

建议（判断，未执行）：如继续沿底前缀联系推进，应先确定允许的带证据读回域，并先把根底与递归更新底的 PrefixU 供给条件单独定稿、实填；这会涉及验收接口的量化域，不能冒充已完成原归约。

#### 5. 偏离、事故、引用范围

- 未修改已有仓库文件；只新增五个 YiSU 前缀 literate 文件。未改 `src/`、`archive/`、README、LOG、台账、留档；未派子路、未装包、未提交、未推送；没有删除其他前缀接口。
- 任务未全部完成的部分是原 `steps′→lowKeep`，原因与限制见第 4 节。新的 `StepU′`、最小层实例和反例都属于原任务第 1 步，没有擅自实现量化域修订。
- 早期临时上界迭代的三次退出 42 分别是临时未完成表达式的语法错误、隐式参数位置错误、一个不可能模式子句；第四次退出 0。正式 `YiSUMin` 首次退出 42 是未显式导入 `YiTBRow.ψ`，补导入后通过。都是实现错误，没有经过两次数学重新设计去硬攻同一失败陈述；完整日志保留。
- 临时目录外的 scratch 选项有 `--safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns`。其中早期 Bound 会显示 `UnsupportedIndexedMatch` warning（普通归纳构造子的注入性）；正式仓库从库选项取得 `-W noUnsupportedIndexedMatch`，冷编无 warning。没有开启 `--cubical` 或 K。
- 直接读取了完整简报、AGENTS.md、手册 §4；`YiLKIface`、`YiLKSlot`、`YiLKFold`、`YiGIRel` 的相关陈述及证明；`YiGIInst.Bdᵍ`/`domsᵍ`；块与路径；EBO 共尾视图与基本列；有限层接口。`YiLTFold.LF` 和它调用的成熟依赖通过现有接口使用，未独立冷编整条依赖闭包。
- 关于原 `eboᵍ` 和既有 FGH/View 的已验收状态依简报，不是本路重新复核的成果；它们未被本路用于新的强度声称。关于主审已冷编 noLeaf 的状态依最新派发信息，本路不替主审作复核结论。
- 最终正式源码禁止构造、本机路径、Funext 扫描均为 0；记录在 `scan-results.json`。扫描覆盖全部五个文件全文。没有运行 HTML、依赖切片或把失败编译的结果作审计依据；本路五件都明确为读记号的验收文件。

#### 6. 全部文件、实验目录、日志及冻结

仓库源码：

1. `<仓库>/probes/OCF/Lean/YiSUBound.lagda.md`
2. `<仓库>/probes/OCF/Lean/YiSUIface.lagda.md`
3. `<仓库>/probes/OCF/Lean/YiSUNeg.lagda.md`
4. `<仓库>/probes/OCF/Lean/YiSUMin.lagda.md`
5. `<仓库>/probes/OCF/Lean/YiSUBridge.lagda.md`

私有实验目录仅一个：`<实验目录>/`。

实验源码：`YiSUMin.agda`（最初恒值 g 的第 0 步）与 `YiSUBound.agda`（最终正式独立化之前的上界原型），各有私有 `.agdai`。正式文件优先于原型。

所有编译日志（均在上述实验目录）：

- `YiSUMin-1.log`
- `YiSUBound-1.log`、`YiSUBound-2.log`、`YiSUBound-3.log`、`YiSUBound-4.log`
- `YiSUNeg-1.log`
- `YiSUMin-repo-1.log`
- `YiSUBridge-1.log`
- `YiSUBound-cold.log`、`YiSUIface-cold.log`、`YiSUNeg-cold.log`、`YiSUMin-cold.log`、`YiSUBridge-cold.log`

其他私有产物：`libraries`、`cold.py`、`cold-results.json`、`cold-summary.json`、`scan-results.json`，冻结清单 `freeze.json`。完整回报为本文件 `<临时目录>`。

五个正式源码均已冻结，交主审独立复核；本路不再修改。冻结清单保存源码 SHA-256、冷编与扫描摘要。

## 主审最终复核

首次五件及续做六件均已逐件删自身接口5G冷编0，仅自身Checking，哈希不变，扫描0。原停止解释撤回，续做后按AGENTS同形反例停查域；原StepU′到LowKeep无额外供给版未交且未否定。根/当前槽位供给和BetaStep有精确反例，补条件接线不报强度，最小实际折叠有非空实例。完整范围见LOG和V188。

## 续作回报原文（主审已独立复核）

### YiSU 续报（2026-11-14）

#### 1. 判决、对首次回报的更正与停止依据

对纲领与目标的意义：已把“根底缺前缀联系”落实为实际折叠证明里的两个具名供给点，并编译了显式补条件的整段归约与两个非空最小实例。未改树、折叠、合法性、原 `Bdᵍ` 或原 `LowKeep` 的定义与量化域；没有新增 EBO 强度结果。

原目标 `steps′→LowKeep : Leaf → (∀ ℓ → StepU′ ℓ) → LowKeep` **仍未交付，也未被否定**。补条件版 `steps′→lowKeep⁺` 多了显式 `RootSupply`；该供给在最小层已假，所以只能作为证明接线记录。β 替代版的 `beta→lowKeep` 不多加根供给，但其 `BetaStep` 在最小层已被否定，也只能作为接线记录。两者都不作强度成果，不从 `Leaf → ⊥` 消去。

首次回报 `<临时目录>` **原文保留**。其中把供给命题的编译否定解释成简报“两次重新设计仍过不了检查器”的停止理由不成立，此解释在这里撤回。第 0 步的反例是预期任务分支，也不是第 0 步前提不成立。

本次停止依据是 AGENTS 当前最佳实践“量化域先取带证据的读回域”的原文：**“连续两条同形的退化反例就停下来查量化域，不逐个加字段。”** 主审最新续派明确要求在这两个检查完成后据此收束，不增加第三种修补、不改量化域。两条检查是：

1. 把整张根前缀供给缩成规范 Ω 根上的**当前槽位**供给：`LocalStep (fn 1)` 和实际 `local-chain` 可编译，但 `no-local-root` 否定从原 `Bdᵍ` 总能供给它；反例同时满足主线比较表、规范 Ω 树的源关系与原底条件。
2. 用实际 β 的前缀证据替代槽位底证据：已重编到原 `LowKeep` 的 `beta→lowKeep`，但 `no-beta-step` 否定该步进接口，即使有 g 的整条分支律。本反例 g 不等于规范 Ω 树的 g，故**不否定链域或规范 Ω 上更弱的证明**。

这不是“两次检查器拒绝”。续做只有一个实现错误退出 42：β 版链步进少需一个实参而搬运时仍多传了旧实参，修正后通过；不把该错误充作数学重新设计失败。

#### 2. 实际证明需要的根底与递归更新底

`YiSUSupport` 的逐字定义：

```agda
RootPrefix : ∀ ℓ → Base ℓ → E.T → Set
RootPrefix ℓ B t = PrefixU B t

Updated : ∀ s h → Ok (nd s h) → Rb (nd s h) → Base (nd s h)
  → Tr (nd s h) → (c : Ch s) → Base (h c)
Updated s h o r B x c i u = ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x

Support : ∀ ℓ → Ok ℓ → Rb ℓ → Base ℓ → E.T → Set
Support zero o r B t = ⊤
Support (nd s h) o r B t = RootPrefix (nd s h) B t ×
  (∀ {a x} → GR.R (nd s h) a x → (c : Ch s)
    → Support (h c) (proj₂ o c) (proj₂ r c) (Updated s h o r B x c) (t ++ a))

UpdateSupply : ∀ s h (o : Ok (nd s h)) (r : Rb (nd s h)) → Base (nd s h) → E.T → Set
UpdateSupply s h o r B t = ∀ {a x} → GR.R (nd s h) a x → (c : Ch s)
  → Support (h c) (proj₂ o c) (proj₂ r c) (Updated s h o r B x c) (t ++ a)
```

根与更新的消费位置明确分开：

- `YiSUFold.Fold.chain` 调 `StepU′` 时显式传 `root s h o r B t sp`。它证明槽位回灌的当前层步进。
- `YiSUFold.Fold.LF` 的 `mU` 行显式传 `update s h o r B t sp m c` 给孩子保持；对应的实际更新底逐字是 `Updated ... x c`，前缀变为 `t ++ a`。`updated-ok` 仍复用旧引理，新增供给没有藏入 `OK`。
- 孩子的 `Support` 继续递归到它自己的每次更新底；没有只给第一层更新、却在后续递归中默认为有。
- 其他归纳行复用 `YiLKFold`，尤其 `mΩ` 使用实际 `YiTBRow.ψ`、实际 feed 链与累计极限；不是只证明一个无关联的接口蕴含。

`Rows` 逐层收集 `StartU` 与 `StepU′`；最小层的 `start-one` 直接由 `rd-zero`、原 `OK B` 和折叠下界证明，不使用全域 `Leaf`。`rows-one` 是 `Rows (fn 1)` 的实例。

`YiSUFold.fold` 的逐字类型：

```agda
SupportedPres : L → Set
SupportedPres ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → Support ℓ o r B t
  → (β : Tr⁺ zero) → M⁰ (E.ψ [] t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B zero (z≤ ℓ) β x))

fold : ∀ ℓ → Rows ℓ → SupportedPres ℓ
```

#### 3. 原目标与两个补条件版本

##### 根供给版

`YiSUReduce.RootSupply` 保留原 `LowAt` 全部参数：

```agda
RootSupply : L → Set
RootSupply ℓ = ∀ {j} (b : Bsᵍ ℓ) (w : j ≤ ℓ) (β : Tr⁺ j) (t : E.T)
  → proj₁ (proj₂ b) ≡ MT.rbᶻ ℓ → Wlᵍ w → Bdᵍ b w β t
  → ∀ {a x} → x ≡ proj₁ (Ωt ℓ) → GR.R ℓ a x
  → Support ℓ (proj₁ b) (proj₁ (proj₂ b)) (proj₂ (proj₂ b)) t

steps′→lowKeep⁺ : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU′ ℓ)
  → (∀ ℓ → RootSupply ℓ) → Laws.LowKeep gradedᵍ domsᵍ
```

该证明实际调用 `fold`，`Leaf` 只通过既有 `start-from-leaf` 提供各层起点；没有矛盾消去。新增的 `RootSupply` 在签名中显露，不是原任务已完成的 `steps′→LowKeep`。

`no-root-one` 的反例有原域全部见证：`ℓ = fn 1`、主线表 `MT.rbᶻ ℓ`、`B₀ ℓ`、`β = next⁺ (Ωt zero)`、`t = E.natT 1`、`w = z≤ ℓ` 与 `wz`、`bd`、`gx = refl`、`leaf-fin 1 : GR.R ℓ Ω₁ (proj₁ (Ωt ℓ))`。所得根前缀要求零层的 `1` 承载 ω，已由有限句法上界否定。这里不是缺源树关系或缺主线比较表造成的空前提。

##### 当前槽位重设计

`PrefixAt ℓ B t p ν` 只向当前 p、ν 要底前缀，`LocalStep` 用它代替整张 `PrefixU`。`local-one` 实填最小层，`Chain.local-chain` 按这个新接口重编实际 feed 迭代。`LocalRootSupply` 只对 `RootSlot` 指定的规范 Ω 根槽位给证据；后继形状根取孩子自身槽位，Ω 形状根取下标层自身槽位，ℕ 极限形状没有 Ω 根。

`no-local-root` 仍用上述规范源树、主线表、β、B、t 与 `bd`。因此，即使把请求缩到这个当前槽位，也不能从现有 `Bdᵍ` 直接取出证据。它否定的是此供给方案，没有证明原 `LowKeep` 为假。

##### β 替代重设计

`YiSULocal.BetaStep` 用 `β` 及 `H.M⁰ (E.ψ [] t ∷ []) (proj₁ β)` 代替槽位底前缀，同时保留 g 的整条分支律。`YiSUBetaFold` 把 β 和这个证据一路传到 `Fold.chain`，得到：

```agda
beta→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → BetaStep ℓ) → Laws.LowKeep gradedᵍ domsᵍ
```

这版不需要 `RootSupply`，因此检查到了“β 证据能否直接接在同一槽位行上”。答案对这个接口是否定的：`no-beta-step` 的前提实填 `B₀`、前缀 1、β 为 ω、`small-step` 为 β 的前缀证据、既有 `whole-branch`。指定孩子 c=1 的 feed 仍是 ω，却被要求承载 ψ₀(2)，由 `no-ω²` 否定。

本反例的源结点 `Ω p g` 的 g 不是规范 `Ωt (fn 1)` 的 g；不能把这个否定扩大成规范 Ω 或实际链域上所有较弱保持定理的否定。

#### 4. 可满足的最小实例、闭项与结论档

两段实际折叠均由 `YiSUFold.fold` 给出，没有调用 `Leaf`、全域 `Rows` 或矛盾消去。

1. `support-one o r : Support (fn 1) o r (B₀ (fn 1)) []`，配 `rows-one`，β 是零层的 1，源树是规范 `Ωt (fn 1)`，源关系是 `leaf-fin 1`。`empty-fold` 得到实际输出承载 `E.ψ [] (E.Ωt (E.natT 1)) ∷ []`。
2. `support-next o r : Support ℓ o r Bnext t`，其中 ℓ=fn1、t=1、Bnext 为逐点 next 的底。β 是 ω、其前缀证据是既有 `small-step`，同一规范源树与源关系给 `prefix-fold`。根前缀 1 的证据确实参与实际归约。

两例的孩子层都是零，递归更新后的 `Support zero ...` 为 `⊤`，所以它们没有实填一个非零孩子层上的前缀更新定理；本路如实把它限定为最小层实例。一般 `UpdateSupply` 的可满足性未证明。

| 问题 | 位置 | 档与结论 |
|---|---|---|
| 实际折叠的补条件归约是否重编 | `YiSUFold.fold` | 编译定理，显式 Support |
| 根与递归更新底是否分开追踪 | `RootPrefix`、`Updated`、`UpdateSupply` 与 `mU` 行 | 编译接口及定理 |
| 补条件版是否有非空最小实际实例 | `empty-fold`、`prefix-fold` | 编译实例，均不使用 Leaf |
| 原域能否总给 Support | `YiSUReduce.no-root-one` | 编译否定 |
| 缩到规范 Ω 当前槽位是否能总给 | `YiSULocal.no-local-root` | 编译否定 |
| β 替代后的链步进是否成立 | `YiSULocal.no-beta-step` | 编译否定；一般 g 域 |
| β 接线能否归约到原 LowKeep | `YiSUBetaFold.beta→lowKeep` | 编译条件定理；步进前提已假，非强度成果 |
| 原 StepU′ 到 LowKeep 的无额外供给归约 | 无定理 | 未交付、未否定 |
| 规范 Ω/较弱链域证明是否被封死 | 无相应否定 | 未判定，不关闭路线 |

首次任务的第 0 步和原接口反例、修正步进最小实例仍见首次回报；本次补完的是该归约的真实条件版、供给跟踪、最小整段折叠与同一调用处的两种重设计检查。

#### 5. 定理表（逐字陈述）

下面多行签名折叠为空格；局部记号按各源码的定义，`ℓ = fn 1`。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `start-one` | `StartU (fn 1)` | 最小层槽位起点直接实填 | YiSUSupport | 编译定理 |
| `support-one` | `∀ o r → Support (fn 1) o r (B₀ (fn 1)) []` | 规范底、空前缀的供给实例 | YiSUSupport | 编译定理 |
| `rows-one` | `Rows (fn 1)` | 最小层所有需要的行 | YiSUSupport | 编译闭项 |
| `fold` | `∀ ℓ → Rows ℓ → SupportedPres ℓ` | 显式前缀供给的实际折叠保持 | YiSUFold | 编译定理 |
| `supported-low` | `∀ ℓ → Rows ℓ → RootSupply ℓ → LowAt ℓ` | 对原 LowAt 域加根供给的归约 | YiSUReduce | 编译条件定理 |
| `rows-from-leaf` | `Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU′ ℓ) → ∀ ℓ → Rows ℓ` | Leaf 只供应起点，与修正步进组装行 | YiSUReduce | 编译条件定理 |
| `steps′→lowKeep⁺` | `Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU′ ℓ) → (∀ ℓ → RootSupply ℓ) → Laws.LowKeep gradedᵍ domsᵍ` | 额外假设显露的接线记录 | YiSUReduce | 编译条件定理 |
| `no-root-one` | `RootSupply ℓ → ⊥` | 原域全根供给在最小层已假 | YiSUReduce | 编译否定 |
| `support-next` | `∀ o r → Support ℓ o r Bnext t` | 前缀 1 的实际根供给非空 | YiSUActual | 编译定理 |
| `fold-one` | `SupportedPres ℓ` | 最小层的整段条件保持 | YiSUActual | 编译定理 |
| `empty-fold` | `GR.R zero (E.ψ [] (E.Ωt (E.natT 1)) ∷ []) (proj₁ (ψ ℓ o (rb-no ℓ) (B₀ ℓ) zero (z≤ ℓ) (Ωt zero) (proj₁ (Ωt ℓ))))` | 规范底的实际折叠关系 | YiSUActual | 编译实例 |
| `prefix-fold` | `GR.R zero (E.ψ [] (t ++ E.Ωt (E.natT 1)) ∷ []) (proj₁ (ψ ℓ o (rb-no ℓ) Bnext zero (z≤ ℓ) (next⁺ (Ωt zero)) (proj₁ (Ωt ℓ))))` | 带前缀根供给的实际折叠关系 | YiSUActual | 编译实例 |
| `local-one` | `LocalStep ℓ` | 当前槽位步进在最小层有全称实例 | YiSULocal | 编译定理 |
| `Chain.local-chain` | `∀ n → GR.Low ℓ p (E.γT (t ++ a) ν n) (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))` | 用当前槽位前缀重编实际回灌链；上下文前提见源码 Chain 模块 | YiSULocal | 编译条件定理 |
| `no-local-root` | `LocalRootSupply ℓ → ⊥` | 向当前规范 Ω 根槽位要供给也失败 | YiSULocal | 编译否定 |
| `no-beta-step` | `BetaStep ℓ → ⊥` | β 不能替代实际槽位底的前缀证据 | YiSULocal | 编译否定 |
| `from-beta` | `Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → BetaStep ℓ) → ∀ ℓ → PresU ℓ` | β 版 Ω 行到所有零目标保持的接线 | YiSUBetaFold | 编译条件定理 |
| `beta→lowKeep` | `Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → BetaStep ℓ) → Laws.LowKeep gradedᵍ domsᵍ` | β 版直接连到原 LowKeep | YiSUBetaFold | 编译条件定理 |

#### 6. 源码、冷编与扫描

首次冻结的五件源码、首次回报及它们的冻结清单均原样保留；本次已按首次 `freeze.json` 的 SHA-256 核实未变。

续做只新增六件（仓库根目录 `<仓库>/`）：

1. `probes/OCF/Lean/YiSUSupport.lagda.md`
2. `probes/OCF/Lean/YiSUFold.lagda.md`
3. `probes/OCF/Lean/YiSUReduce.lagda.md`
4. `probes/OCF/Lean/YiSUActual.lagda.md`
5. `probes/OCF/Lean/YiSULocal.lagda.md`
6. `probes/OCF/Lean/YiSUBetaFold.lagda.md`

代码行口径仍为代码块内非空非注释行，含模块头、导入。续做 374 行，和首次 354 行合计 728 行、11 个验收文件；不能计为成品定义成本或强度提升。

| 文件（均在 `probes/OCF/Lean/`） | 代码行 | 总行 | 冷编退出码 | 最大 residency（字节） | 秒 |
|---|---:|---:|---:|---:|---:|
| `YiSUSupport.lagda.md` | 55 | 72 | 0 | 1,479,963,976 | 15.452 |
| `YiSUFold.lagda.md` | 87 | 101 | 0 | 1,413,435,888 | 15.460 |
| `YiSUReduce.lagda.md` | 43 | 55 | 0 | 1,347,697,264 | 15.635 |
| `YiSUActual.lagda.md` | 32 | 43 | 0 | 1,393,674,912 | 16.650 |
| `YiSULocal.lagda.md` | 79 | 95 | 0 | 1,332,869,552 | 15.746 |
| `YiSUBetaFold.lagda.md` | 78 | 92 | 0 | 1,347,852,208 | 15.610 |

冷编均逐件删除自身字面接口路径后执行，依赖保持热；单 Agda、`+RTS -M5G -s -RTS`。六件的禁用构造、本机路径、Funext 扫描均 0，覆盖全文，详见 `resume/scan-results.json`。没有运行 HTML、依赖切片，没有把失败编译当成通过。

实验目录沿用 `<实验目录>/`，续做产物只在其 `resume/` 子目录；库文件沿用该私有目录中的 `libraries`。本次没有新 scratch 数学源码，保留的数学文件均为上述 literate 文件。

全部续做编译日志（位于 `<实验目录>/resume/`）：

- `YiSUSupport-1.log`
- `YiSUFold-1.log`
- `YiSUReduce-1.log`
- `YiSUActual-1.log`
- `YiSULocal-1.log`
- `YiSUBetaFold-1.log`（42，多传旧实参的实现错误）
- `YiSUBetaFold-2.log`（修正后 0）
- `YiSUSupport-cold.log`
- `YiSUFold-cold.log`
- `YiSUReduce-cold.log`
- `YiSUActual-cold.log`
- `YiSULocal-cold.log`
- `YiSUBetaFold-cold.log`

其他续做产物：`cold.py`、`cold-results.json`、`cold-summary.json`、`scan-results.json`、`freeze.json`，均在上述 resume 子目录。当前完整续报为 `<临时目录>`；首次完整回报为 `<临时目录>`，两份都保留。

#### 7. 事故、引用范围与冻结

本次重读了实际 `YiLKFold`、`YiLKSlot`、`YiLKIface`、`Bdᵍ` 与原五件；新实际归约直接复用 `YiLKFold` 的归纳行，模块文首已注明来源。没有以未独立复核的外部结果作新强度结论；成熟依赖使用现有接口，没有整条依赖闭包冷编。

没有改 `src/`、`archive/`、原五件、共享接口、原 Bd 或量化域，没有新增全域 Leaf 假前提的实例，没有用 `Leaf → ⊥`。未派子路、未装包、未提交、未推送，没有删其他前缀接口。续做的唯一 42 已在上面列明；没有 251、124、154，没有加大堆。

停止范围仅限当前两种供给修补，遵照主审最新要求和 AGENTS 的连续同形退化反例规则。本路没有关闭原 LowKeep 路线，也没有断言只能有这些办法；更弱链域与规范 Ω 上的证明仍未定。

续做六件定稿并自查后冻结，交主审独立冷编；冻结摘要保存源码与续报 SHA-256，原冻结摘要不覆盖。

