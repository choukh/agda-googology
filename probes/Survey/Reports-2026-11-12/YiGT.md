# 一般目标的统一保持（数学，攻 Ω 槽位那一步） (YiGT)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十九批；外部模型，作者转发 |
| 前缀 | `YiGT` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：一般目标的统一保持（数学，攻 Ω 槽位那一步）（前缀 YiGT）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十九批四路之一（选项原文 "一般目标的统一保持 (Recommended)"），与在跑的 YiXV、YiFM、YiLL、YiMX 在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- **再上一批**（主审复核过）：`YiLKSlot.steps→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → Laws.LowKeep gradedᵍ domsᵍ`（`YiLKIface`、`YiLKFold`、`YiLKSlot`；回报 `probes/Survey/Reports-2026-11-12/YiLK.md`）：折向第 0 层的各行对一切层号证完，剩每层一条槽位回灌的步进 `StepU`。第一档交付（合法闭项、内部 View、FGH）已在新主线上编译（`YiVW*`）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **卡住的一步**（`YiLKSlot` 第 70 行起）：`OmegaStep k h`，即 Ω 形状层号 `nd (sΩ k) h` 上的槽位步进，结论是
  `GR.R k (E.γT (t ++ a) ν (suc n)) (proj₁ (ψ (nd (sΩ k) h) o r B k (ink self) (B k (ink self)) (g c)))`，
  即同一高层的树折到槽位层 k（不是第 0 层）后保持关系。`omega-step : ∀ k h → StepU (nd (sΩ k) h) → OmegaStep k h`。
- **现有的统一保持只到第 0 层**：`YiLKIface.PresU ℓ` 的目标是第 0 层；`YiLKFold.uniform : ∀ ℓ → KidU ℓ → PresU ℓ`，`fromSlots` 按层号结构递归消去孩子。YiLK 回报："更低源层的零目标保持没有直接提供 OmegaStep 所需的同源分级目标折叠。后续候选是发展按目标读回下标 ν 参数化的模拟律"。
- **槽位步进的陈述**（`YiLKIface.StepU`）：
  ```agda
  StepU ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
    → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
    → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
    → GR.Low ℓ p (E.γT (t ++ a) ν n) c
    → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
    → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)
  ```
  其中 `feed ℓ o r B p g c = fromBr ℓ p (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c)))`（`YiLKIface` 第 40–59 行）。
- **接口里现成的律**（`YiAbsGIface` 第 138–143 行）：`SelfKeep`（同层：`ψ ℓ b ℓ self β x`）、`UpKeep`、`LowKeep`。`eboᵍ` 只用 `LowKeep`，`YiGI` 没有主张 `SelfKeep`、`UpKeep`。
- **AGENTS "树的语言"**：折叠是 FGH 的推广；在某层的树上分支时按该层与目标的关系取效果：低于目标保留，同层以输出作下标对角，高于目标经该层走链。
- **主审的判断（未编译）**：目标取 k 时，槽位层 k 就是 "同层"，那一步走对角，即 `SelfKeep` 在 k 上；而 k 是 `nd (sΩ k) h` 的结构子项。所以 "一切目标的保持" 也许能对层号结构递归闭合，可数槽位与 Ω 槽位一起解决。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：写出一般目标的保持 `PresJ ℓ j`（目标 j ⊑ ℓ，路径域你定并说明理由；`domsᵍ` 的 `Wl` 只给标准零层路径），以及递归骨架：`OmegaStep`（源 `nd (sΩ k) h`，目标 k）⇐ 目标 k 上的各行 + k 上的 `SelfKeep`；k 上的 `SelfKeep` ⇐ k 的各行 + k 的槽位（k 的结构子项）上的步进。未知的引理写成模块参数，确认终止检查接受这个互递归。再在 ℓ = `tw 1`（k = `zero`）上确认它落到第 0 层已有的事实（`YiGICheck.low-zero`、`YiLKFold` 的 `self-zero` 一类）。终止检查两次重新设计仍不过就停下回报，附首个错误。
1. **一般目标的各行**：照 `YiLKFold.Fold.LF`，把目标从第 0 层换成任意 j，各行（结点、嵌入、ℕ 极限、Ω 分支，以及低于、同层、高于目标三种分支效果）对一切层号证完。
2. **`SelfKeep` 与 `OmegaStep`**：按第 0 步的递归证 `SelfKeep` 对一切层号，由此得 `OmegaStep` 与 `∀ ℓ → StepU ℓ`。若证明需要 `StepU` 之外的前提（例如 g 在一切孩子上满足整条 Ω 分支律，或底与前缀 t 的联系），用改过的陈述并写清差别（并行的 YiSU 在查 `StepU` 的可满足性）。
3. **合成**：编译 "`Leaf`（加你实际需要的、写成具名假设的前提）⇒ `eboᵍ` 要的 `LowKeep`"，经 `steps→lowKeep` 或其改写；精确列出剩下的前提。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiGT`（模块名 `OCF.Lean.YiGT…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiFM`、`YiLL`、`YiMX`、`YiSU`、`YiPF`、`YiPX`）。验收文件，文首标明。
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

### YiGT 完整回报（已冻结）

#### 1. 判决与范围

本路没有提高主线的无条件强度，也没有组装 EBO 条件终点。未改树、折叠、合法性；只新增验收侧的一般目标候选陈述与最小前提检查。

第 0 步的**抽象终止骨架通过**（实验 `YiGTMin.Skeleton`，首次编译退出 0）。但它把关键的槽位桥 `slots` 整条作为参数；这个编译事实不证明该参数可以实填，也不证明实际 Ω 槽位递归已经闭合。真实的 Ω 槽位归约未完成，因此本轮按简报“第 0 步不成立”停止条件停在第 0 步；这里的“未完成”不是编译否定定理，不关闭一般目标路线。

最小前提检查给出两个分开的结果：

1. **编译定理**：在实际 `tw 1`、默认底 `B₀ (tw 1)`、目标 `zero`、读法 `ν = []` 上，`OK` 成立，空前缀的槽位底关系成立；但前缀为 `natT 1` 时的槽位底关系推出 `⊥`。所以无法把 `OK B` 当作一般前缀底关系的提供者。否定仅针对这个补前提的办法，不是否定 `OmegaStep`、`StepU`、`PresJ` 或规范塔域上的保持。
2. **编译过的条件归约（只留实验目录）**：如果已经有同一高源层 `nd (sΩ k) h` 到 `k` 的 `PresJ`，并补上相应前缀的 `SlotBase`，则可推出补过前提的 `OmegaStepB`。这个 `PresJ` 的源仍是高层，不能用 `k` 自己的 `SelfJ` 直接代替；这是第 0 步尚未闭合的位置。该条件归约的高源层前提未实填、未给出全域可满足实例，不将它列作强度成果。

未进入第 1 步的一般目标各行证明，未证明全层 `SelfKeep`、`OmegaStep`、`StepU`，未交付新的 `LowKeep` 或 EBO 下界。没有从已知为假的全域 `Leaf` 前提推出任何强度成果。

##### 问题表

| 问题 | 位置 | 档 |
|---|---|---|
| 目标需要由读法 `ν` 参数化；原 `SelfKeep` 在实例中固定写 `ψ []` | `YiGTCheck.PresJ`；实验 `PresJ` | 候选定义与纸面判断，未证明全域成立 |
| 抽象结构递归可被终止检查接受 | `YiGTMin.Skeleton.allJ/selfJ/step` | 编译检查；未知行、槽位桥仍是模块参数 |
| 零层、零读法的保持可复用已有事实 | `YiGTCheck.zero-target` | 编译定理（来源 `YiLKIface.self-zero`） |
| `OK` 不能补出任意前缀的槽位底关系 | `YiGTCheck.no-base-one/no-ok→base` | 编译否定定理，前提实例由 `base-ok` 交出 |
| 最小实际 `tw 1` 空前缀、第 0 步样例可通过 | `YiGTCheck.sample-*` | 有限样例（已编译），不是全层保持证明 |
| 实际槽位桥需要高源层到 k 的保持，尚未归约为 k 的自身保持 | `YiGTBridge.pres→omega` 的第三参数 | 条件归约已编译；“尚未闭合”是本轮工作状态，不是路线否定 |

#### 2. 文件、编译与资源

只新增一个仓库文件：

- `<仓库>/probes/OCF/Lean/YiGTCheck.lagda.md`（78 行，其中 Agda 代码 67 行）。

全部实验源码与目录：

- 实验目录：`<实验目录>/`
- `<实验目录>/YiGTMin.agda`（57 行；候选 `PresJ`、参数化终止骨架、零层实例）。
- `<实验目录>/YiGTBridge.agda`（36 行；`SlotBase`、`OmegaStepB`、`pres→omega`）。
- `<实验目录>/YiGTBaseProbe.agda`（36 行；默认底的最小前提检查）。
- `<实验目录>/libraries`（本路私有库清单）。

所有编译串行，均带 `+RTS -M5G -s -RTS`，未加堆、未用 `--ignore-interfaces`。定稿逐件只删除了本路自己的接口，依赖沿用缓存。首个文件 `YiGTMin.agda` 在本轮前段已经编译退出 0，未等待一般证明完成；首个编译耗时约 15.6 秒。

| 文件 | 总行 / 代码行 | 冷编退出码 | 最大 residency（bytes） | RTS 总内存（MiB） | 秒（并行环境） |
|---|---:|---:|---:|---:|---:|
| `YiGTCheck.lagda.md` | 78 / 67 | 0 | 1,381,855,512 | 2459 | 15.50 |
| `YiGTMin.agda` | 57 / 57 | 0 | 1,421,568,352 | 2381 | 16.09 |
| `YiGTBridge.agda` | 36 / 36 | 0 | 1,494,203,800 | 2496 | 15.41 |
| `YiGTBaseProbe.agda` | 36 / 36 | 0 | 1,420,098,384 | 2379 | 15.25 |

每份冷编日志均只有本模块的一行 `Checking`，未重编共享依赖。全部四份源码禁用构造、函数外延与本机路径扫描均为 0（私有 `libraries` 本身按任务要求列库路径，不计为数学源码）。

全部编译日志（不隐去失败轮）：

- `<实验目录>/min-first.log`：0。
- `<实验目录>/bridge-first.log`：0。
- `<实验目录>/base-first.log`：0。
- `<实验目录>/check-first.log`：42；样例最后一行的非单射头无法推断隐式 `a/x`，见下文事故记录。
- `<实验目录>/check-fixed.log`：0。
- `<实验目录>/check-cold.log`：定稿冷编。
- `<实验目录>/YiGTMin-cold.log`：定稿冷编。
- `<实验目录>/YiGTBridge-cold.log`：定稿冷编。
- `<实验目录>/YiGTBaseProbe-cold.log`：定稿冷编。

检查记录：

- `<实验目录>/cold-status.json`：实际命令、退出码、耗时。
- `<实验目录>/scan.json`：仓库新文件的禁用构造、本机路径、函数外延扫描。
- `<实验目录>/verification.json`：最后冷编、Checking 行与扫描汇总。

接口删除范围逐字为：

- `probes/_build/2.8.0.2/agda/OCF/Lean/YiGTCheck.agdai`
- `<实验目录>/YiGTMin.agdai`
- `<实验目录>/YiGTBridge.agdai`
- `<实验目录>/YiGTBaseProbe.agdai`

#### 3. 陈述、定理与样例

##### 候选定义（不是已经成立的保持定理）

`PresJ` 用完整的实际路径类型 `≤ = Pth true`，因为 Ω 槽位的实际路径是 `ink self`，更深槽位还经 `inc`；仅沿 `domsᵍ.Wl` 的标准零路径会丢掉本任务要求的目标。此处**没有**把所有路径都列为已满足的 `Wl`，也没有改共享域。

```agda
PresJ : (ℓ j : L) → j ≤ ℓ → Set
PresJ ℓ j w = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (ν t : E.T) → GR.Rd j ν
  → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))

SlotBase : ∀ k h → Base (nd (sΩ k) h) → E.T → E.T → Set
SlotBase k h B ν t = GR.R k (E.ψ ν t ∷ []) (proj₁ (B k (ink self)))
```

`SlotBase` 的白话：回灌所选的槽位底，确实承载当前目标下标 ν、前缀 t 对应的 ψ 值；这比 `OK` 给的 Ω 树下界多了前缀信息。

##### 仓库交付的逐字陈述

```agda
zero-target : (o : Ok zero) (r : Rb zero) (B : Base zero) → OK B
  → (t : E.T) (β : Tr⁺ zero) → GR.R zero (E.ψ [] t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R zero a x
  → GR.R zero (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ zero o r B zero self β x))

rd₀ : GR.Rd zero []

base-ok : OK (B₀ (tw 1))

base-empty : SlotBase zero h₁ (B₀ (tw 1)) [] []

no-base-one : SlotBase zero h₁ (B₀ (tw 1)) [] (E.natT 1) → ⊥

no-ok→base : (OK (B₀ (tw 1)) → SlotBase zero h₁ (B₀ (tw 1)) [] (E.natT 1)) → ⊥

sample-child : (η : E.T) → GR.R (tw 1) (E.fsT (E.Ωs []) (E.γT (η ++ E.Ωs []) [] zero)) (suc zero)

sample-low : (η : E.T) → GR.R zero (E.γT (η ++ E.Ωs []) [] zero) (suc zero)

sample-step : (o : Ok (tw 1)) (r : Rb (tw 1))
  → GR.R zero (E.γT (E.Ωs []) [] (suc zero))
      (proj₁ (ψ (tw 1) o r (B₀ (tw 1)) zero (ink self)
        (B₀ (tw 1) zero (ink self)) (suc zero)))
```

白话与档位：

| 名字 | 一句白话 | 档 |
|---|---|---|
| `zero-target` | 零层、零读法的保持是已有 `self-zero` 的直接实例 | 编译定理；没有证明所有读法与源层 |
| `rd₀` | 零层可以读零下标 | 编译定理；显式实例 |
| `base-ok` | `tw 1` 的默认底满足现有 `OK` | 编译定理；显式实例 |
| `base-empty` | 该默认底承载空前缀的零目标 ψ 值 | 编译定理；显式实例 |
| `no-base-one` | 同一默认底不能承载前缀 1 的零目标 ψ 值 | 编译否定定理 |
| `no-ok→base` | 不能从 `OK` 推出这个前缀 1 的底关系 | 编译否定定理；`OK` 前提由 `base-ok` 实填 |
| `sample-child` | 常值树 1 给出最小 Ω 步进的源关系输入，任意前缀时链首项相同 | 有限样例已编译；未给 Ω 分支的全分支关系律 |
| `sample-low` | 树 1 给出该最小步进的下标关系输入 | 有限样例已编译 |
| `sample-step` | 实际 `tw 1`、空前缀、常值分支的第 0 步结论成立 | 有限样例已编译；不推广到任意前缀或 g |

上述否定没有矛盾的实质前提：`OK` 的实例是 `base-ok`；目标读法是 `rd₀`；`base-empty` 是同类型底关系在空前缀的正实例。实际 `tw 1` 的 `Ok` 已有 `Ok-tw 1`，比较表已有 `YiMTTab.rbᶻ (tw 1)`，样例的两个输入关系由 `sample-child/sample-low` 给出。`no-base-one` 否定的正是前缀为 1 的关系本身，没有假定该关系能先被构造。

##### 只留临时目录的条件归约（不计强度）

```agda
OmegaStepB : (k : L) → (Tr k → L) → Set
OmegaStepB k h = (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) → OK B
  → (t a ν : E.T) → GR.Rd k ν → E.cof a ≡ E.cΩ ν → SlotBase k h B ν t
  → (g : Tr k → Tr (nd (sΩ k) h)) (n : ℕ) (c : Tr k)
  → GR.R k (E.γT (t ++ a) ν n) c
  → GR.R (nd (sΩ k) h) (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.R k (E.γT (t ++ a) ν (suc n))
      (proj₁ (ψ (nd (sΩ k) h) o r B k (ink self) (B k (ink self)) (g c)))

pres→omega : ∀ k h → PresJ (nd (sΩ k) h) k (ink self) → OmegaStepB k h
```

证明只将给定高源层保持作用于 `m`，再由 `fsT++` 改写 γ 后继。原 `OmegaStep` 不带的额外前提是 `SlotBase k h B ν t`。前提 `PresJ (nd (sΩ k) h) k (ink self)` 尚未实填，不能把这条参数归约当成消除了原障碍。

终止骨架的未知参数逐字为：

```agda
(row0 : AllJ zero)
(rows : ∀ s h → ((c : Ch s) → AllJ (h c)) → StepU (nd s h) → AllJ (nd s h))
(slots : ∀ s h → ((c : Ch s) → AllJ (h c)) → KSelf s → StepU (nd s h))
```

`KSelf (sΩ k) = SelfJ k`，其它形状取 `⊤`；`AllJ ℓ = (j : L) (w : j ≤ ℓ) → PresJ ℓ j w`。`allJ` 在同层调用 `step`，`step` 只调用结构子项上的 `allJ/selfJ`，检查器接受。但真正需要证明的就是这里的 `slots`；用上面的实际 `pres→omega` 替换时，它需要高源层的 `PresJ`，而不是 `KSelf` 交出的较低源层 `SelfJ k`。未实填这些参数，也未声称整个参数接口可满足。

#### 4. 第一个障碍与停止依据

精确位置是 `YiGTBridge.pres→omega` 的第三参数：

```agda
PresJ (nd (sΩ k) h) k (ink self)
```

本轮编译验证的桥需要它；目标层 k 的 `SelfJ k = PresJ k k self` 具有不同的源关系、输入树类型与实际折叠，不能直接提供该参数。与此同时，直接用一般保持证明桥时还要 `SlotBase`，而 `no-ok→base` 已否定从现有 `OK` 直接补它的办法。

因此没有完成原简报要求的“真实 Ω 槽位步进 ⇐ 较低源层各行和 SelfKeep”的第 0 步，不进入一般行证明。这个停止依据是**本轮第 0 步未完成**；不是宣称两种机制以外不可能有别的证明，也不是宣称任何一般目标路线已被否定。抽象骨架通过不等于真实递归闭合。

建议（未执行，需由主审另行决定）：下一次若继续，应先确定一个可满足的、随实际前缀更新的槽位底域，以及能消去“同一高源层到 k”前提的准确桥陈述；不要再把 `slots` 整条放进参数后报告已经完成结构递归。也可等待并行 YiSU 对原 `StepU` 的可满足性结果，再决定真实步进陈述；本路未读取或依赖其结果。

#### 5. 偏离、事故、引用与冻结

- 未修改任何已有仓库文件，未改 README、LOG、台账或留档，未碰 src/archive，未提交、未推送、未派子路。
- 唯一编译错误：仓库样例首轮 42，`sample-step` 调用的隐藏 `a/x` 经非单射的 `ψ` 无法推断；按手册显式写 `{a = E.natT 1} {x = suc zero}` 并显式给关系构造子的 `t/x`，下一轮 0。不是终止检查失败，没有使用强制终止或其它禁用构造。
- 无堆耗尽、超时或内部错误；没有两次重设计终止失败。停止于真实第 0 步未完成，不把它写成“编译器否定了一般路线”。
- 已完整读任务简报、仓库 AGENTS、手册 §4；读了 `YiLKIface`、`YiLKFold`、`YiLKSlot`、`YiGIRel`、`YiGIInst`、`YiAbsGIface`、`YiTBRow`，并查阅相关签名与局部证明。
- `YiLLLeafNeg` 的 `Fin.one-ref` 与 `conflict` 已读源码后复用；本路未调用 `noLeaf`，也未从假 `Leaf` 消去得到结论。按入站消息，`noLeaf` 已由主审冷编复核；本路没有自删 LL 接口重新复核它。只自删本路接口。
- `YiFMFin.rd-zero` 仅检索到签名与相关行，未导入、未使用；YiSU 没有结果文件供本轮引用，未读取其回报。
- 主线已有内部 View/FGH、此前 EBO 条件终点与 `noLeaf` 的主审状态，只按简报/入站消息作背景，未在本路重新从头复核，未算本路成果。
- **冻结状态：四份源码已冻结。最终逐件自删接口冷编均为 0，日志 Checking 行符合范围，扫描均为 0；此后不再改源码。**主审仍需独立复核仓库交付。



## 主审最终复核

15件958行均主审删自身接口5G冷编0（原Check哈希未变、此前已冷编），扫描0；真实LF/update/chain互递归消去SlotPres/StepU′参数，剩显式索引与前缀。同步框架在fn2及实际tw1被编译否定；只否定该框架，不否定一般保持或SelfKeep。LowAt′仍多PrefixU，原LowKeep未得。具体实例与剩余目标见LOG、台账V189。

## 最终续作回报原文（主审已独立复核）

### YiGT 完整回报（续作完成当前接口构造与配对否定；已冻结）

#### 1. 判决、范围与对纲领的意义

本轮没有提高实际主线的无条件强度，没有组装 EBO 条件终点，没有更改树、折叠、合法性或既有证书。新增的是验收侧一般目标保持的构造定理、补前缀的槽位步进，以及针对本轮新增同步框架的编译否定。

**关键构造已完成并编译：**按实际源关系推导互递归生成一般目标保持 `LF`、更新底的前缀证据 `update` 和槽位回灌链 `chain`，因而 `YiGTDirect.direct` 的参数中不再含 `SlotPres` 或 `StepU′`。它仍需要明确的路径证据 `IndexOK` 与递归的槽位路径证据 `IndexTree`。固定本层比较表的 `layer-at` 使用 `LayerIndex`，避免无谓要求本层所有比较表都符合证据域。

**关键限制也已编译：**`NodeFrame` 要求实际 `kp` 的保留/走链同参照下标比较同步。`fn 2` 上对任意目标下标 ν 都存在同一框架内的冲突：两个槽位允许同一余尾下标 0，而实际 kp 在目标 `fn 1` 的指定孩子路径上一个保留、一个走链，因而同时要求 `Pen (cmpᵀ (sucT []) ν)` 和 `cmpᵀ (sucT []) ν ≡ gt`。由此本轮的 `IndexTree (tw 1)` 和任意固定实际 o/r 下的 `LayerIndex (tw 1) o r` 都被否定。

这个否定**只针对新增的 NodeFrame/IndexOK/SlotIndex/IndexTree/LayerIndex 证据域**。它不是 SelfKeep、SelfJ、StepU′、LowKeep、树的定义、规范塔强度或一般目标路线的否定。原第 2 步的实际 tw 1 槽位保持未交付，原第 3 步 `Laws.LowKeep gradedᵍ domsᵍ` 未交付；`LowAt′` 明确多了 PrefixU 前提，不能改称原 LowKeep。

对“树自足”的意义：一般行及回灌链的闭包证明不按站点定制，覆盖任意源层和目标层，但本轮的验收框架仍读记号，而且同步字段在第二有限层已经不可实填。因此不能作为成品证书；它给出了一个编译过的、精确到字段的修改依据，未反过来指导前三层定义。

##### 原任务推进位置

| 原步骤 | 本轮完成内容 | 限制 / 档 |
|---|---|---|
| 0 最小检查 | 原参数化骨架 0；续作真实 `LF/update/chain` 互递归 0；零层、最小层和实际 tw 1 的零槽路径证据都有实例 | 编译检查 / 编译定理；tw 1 的整个 IndexTree/LayerIndex 有编译否定 |
| 1 一般各行 | 零、后继、ℕ 极限、Ω 保留与走链、弱化、参照向下封闭；自身、一致路径、Ω 下标路径、后继指定孩子、ℕ 比较、Ω 比较表两条有证据分支 | `PresAt` 在 IndexOK+Kit 下；`direct` 在 IndexTree 下。表缺项的指定孩子路径被当前证据域排除，不声称任意路径保持 |
| 2 SelfKeep / ΩStep | 一般 ψν 自身保持有 NodeFrame 条件；真实递归消去 SlotPres/StepU′ 参数；给出槽位保持、StepU′、固定 o/r 的 Ω 步进归约 | 原抽象 SelfKeep 固定 ψ[]；只在零层实填搭接。没有实填实际 tw 1 的完整步进 |
| 3 LowKeep 合成 | `low-at′`、`low-when-prefix`、`low-layer-prefix` 编译；原主线比较表下前缀 1 的最小层实例 `low-one-next` 编译 | 多 PrefixU 且要 IndexTree/LayerIndex。原 LowKeep 未得，不引用假 Leaf 消去矛盾 |

本轮没有把“未知引理作参数”当成不符合第 0 步。首次回报在未实填 slots、OK 不供前缀处停下，被主审纠正后已继续。原首次回报原样保存在实验目录的 `YiGT-report-initial.md`，原冻结 `YiGTCheck` 源码未改。

##### 问题表

| 问题 | 精确位置 | 档 |
|---|---|---|
| 同一高源层到槽位目标的递归是否能由检查器接受 | `YiGTDirect.Direct.LF/update/chain` | 编译定理；真实互递归通过，不仅是参数骨架 |
| 一般后继、极限、上折、嵌入如何对目标下标参数化 | `YiGTGen`、`YiGTUp`、`YiGTEmb` | 编译定理，明确比较/搬运或路径条件 |
| 当前 Frame 能否由 Rd 自动供给 | `YiGTIndexNeg.no-read→frame₁` | 编译否定，只否定供给字段 |
| 当前 Frame 能否覆盖 fn 2 到 fn 1 | `YiGTIndexNeg.no-frame₂` | 任意 ν、任意 Ok 的编译否定 |
| 实际 tw 1 是否有当前 IndexTree / LayerIndex | `no-index-tree-tw1`、`no-layer-tw1` | 编译否定，只否定本证据域 |
| 补前缀条件及递归域是否有可满足片段 | `YiGTInst.it-one/kit-one/prefix-one`、`YiGTOmega.layer-Ω₀/prefix-Ω₀` | 编译闭项，含非空前缀及 Ω 形状 |
| 是否得到原 StepU 或原 LowKeep | 没有 | 不作否定判断；原 StepU 的 YiSU 否定仅作共享候选背景 |

#### 2. 证明链与剩余前提

##### 2.1 一般各行：先交具名条件，再消去循环参数

`PresAt ℓ` 固定实际折叠 `YiTBRow.ψ`，目标是 j，路径是 `j ≤ ℓ`，参照结果为 `ψν(t+a)`，额外显式给 `PrefixU B t` 与 `IndexOK ℓ o r j w ν`。它没有修改共享 `domsᵍ.Wl`。

`IndexOK` 的组成：

- `NodeFrame` 对实际 kp 的结果给证据。保留时交目标槽位、Nu、Low 的全分支搬运和 Pen 比较；走链时交相反的 gt 比较。
- `RouteOK` 对自身、一致、下标层、指定孩子与比较表分支交结构较低源层的同类证据。指定孩子的 Ω 比较表缺项时取 `⊥`，这是当前证据域的限制，未由此否定原回退行。

`YiGTFold.pres : ∀ ℓ → Kit ℓ → PresAt ℓ` 完成一般各行；`Kit` 中确实还含 SlotPres/StepU′。本轮进一步证明 `YiGTDirect.direct : ∀ ℓ → IndexTree ℓ → PresAt ℓ`，其互递归直接在关系推导的更小输入上生成所需的槽位调用和更新前缀；不是把 SlotPres 改名后留在参数里。

`IndexTree` 给每个实际槽位的 IndexOK，并递归给孩子。`LayerIndex` 只固定本层的 o/r，孩子仍带 IndexTree。两者都属于读记号的验收证据，不进入最终定义与证书。

##### 2.2 一般 ψν 自身保持与抽象 SelfKeep 的区别

`YiGTSelf.self-pres`：在任意层 ℓ、任意 ν 上，若自身路径有 `NodeFrame ℓ o ℓ self ν`，则 β 承载 ψν(t)、x 承载 a 时，自身折叠承载 ψν(t+a)。证明不用 PrefixU、Leaf、StepU′、SlotPres 或 IndexTree。

当前 `gradedᵍ.cl` 是 `λ ℓ t → ψ [] t ∷ []`，不是按 ν 的 ψν。因此搭接原抽象 `Laws.SelfKeep` 必须取 ν=[]，不能用 `self-one`（ν=natT 1）冒充。

`YiGTCompat.SelfAtᵍ` 是原 SelfKeep 在一个固定层上的逐字形状；`self-under-frame` 给 ν=[] 的局部搭接；`self-zeroᵍ` 实填零层。原全层 SelfKeep 没有实填。`no-self-frame₁-zero` 与 `no-read→frame₁` 只说明这个同步框架不能供给它，不说明原 SelfKeep 为假。

##### 2.3 槽位步进与 LowKeep 的准确差别

`slot-pres : IndexTree ℓ → SlotPres ℓ` 与 `step′ : IndexTree ℓ → StepU′ ℓ` 已编译。`step-layer`、`omega-step-at` 固定 o/r，增加 PrefixU，与原 `OmegaStep` 的全称 o/r 陈述有区别。具体非空 Ω 片段由 `YiGTOmega.step-Ω₀` 交出：下标层 0、孩子层恒 0、比较表逐字返回 self；它不是规范塔的强度结果。

`LowAt′` 在原 LowAt 的参数中增加 `PrefixU (proj₂ (proj₂ b)) t`，其余原 Wl、Bd、主线表与 Ω 树限制原样列出。`low-at′` 在 IndexTree 下给它；`low-layer-prefix` 固定实际 o/r 的 LayerIndex。本轮没有声称 `OK B` 或原 `Bdᵍ` 可以给这个新前提。

仍缺什么：原全域 LowKeep 需要一种不要求当前同步 Frame、且不从原 Bd 凭空补 PrefixU 的外部证明。实际规范塔域是否能用不同的量化域或关系证明补足，未证明、未否定；本轮没有改共享域，也没有改树/折叠/合法性。

#### 3. 可满足片段与否定的范围

| 具名条件 | 正实例 | 不是哪种成果 |
|---|---|---|
| `NodeFrame` | 零源层框架；`one-frame` 在 fn 1、ν=1 的自身框架 | 不表示 Rd 自动给 Frame；ν=0 的同层 Frame 有否定 |
| `IndexOK` | `index-zero` 对所有源层的标准零路径；`index-tw1-slot` 对实际 tw 1 的 ink self 零目标 | 不表示实际 tw 1 的所有槽位都在证据域 |
| `Kit` / `IndexTree` | 零层、`kit-one`、`it-one` | 不表示规范塔 n=1 已闭合；fn 1 不是 tw 1 |
| 固定 metadata 的 `LayerIndex` | `layer-Ω₀` 的 Ω 形状闭项 | 不是实际 tw 1；没有强度/值验收声称 |
| `PrefixU` | `one-prefix` 空前缀、`prefix-one` 前缀 1、`prefix-Ω₀` 空前缀 | 不由任意 OK/Bd 给出 |
| 关系与非零底 | `one-leaf`、`beta-one`；`low-one-next` 可作用于 one-leaf | 原始 R 关系不等于已交付序数值出口或 EBO 下界 |

否定的所有非结论前提都实填：两个 Nu 坐标均用 `GR.c0 refl`；Ok 取 `okf 1/2`，比较表取 `rb-no` 或任意 r。`no-frame₂` 对任何 ν、任何 Ok 都否定同一个 NodeFrame。两槽位的实际 kp 一支保留、一支走链；失败的是比较字段，不是全分支 Low、不是树合法性或值。没有把它归入 LPO/W/V/C 壁垒。

原 `Leaf` 已被主审否定这一信息没有被用作消去规则。本轮所有构造与否定都不调用 `YiLLLeafNeg.noLeaf`，不从假 Leaf 出发交付结果。旧 Check 复用该文件的 Fin.one-ref/conflict；新增部分也未通过它们制造假强度。

##### 3.1 候选与纸面判断（供主审入台账）

- 当前已执行候选：把一般目标的所有行做成 IndexOK 条件下的推导归纳，再把前缀更新与链并入该归纳。真实互递归已编译，不是假定一条同名保持律。
- 当前证据域的失败：NodeFrame 强制参照比较与实际 kp 同步；fn 2 的两个 Nu 坐标允许同一个 0，导致比较字段冲突。此处量化了所有 Nu 读法，不能据此否定带指定坐标的规范读回域；反例位置是规范有限层号，失败的读法坐标不必是该层的指定读回。
- 已执行的量化修订：LayerIndex 固定本层 o/r，孩子仍用 IndexTree。Ω 常零孩子配字面完整 self 表有实例；但实际 tw 1 仍因其孩子 fn 2 的 IndexTree 失败。这个片段不作为规范塔强度。
- 未执行候选：把目标参考下标 ν 提升到一个有字面证据的 μ，要求 ν≤μ，利用底在 μ 的 PrefixU 及 ψ 下标单调读回 ν。原同步 NodeFrame 在 fn 2 的该路径上对任何 μ 都有 no-frame₂，故仅换 μ 而保留同一字段不会给出该字段实例；这不否定含其它补偿律的覆盖接口。
- 未执行候选：把关系的槽位量化缩到规范构造实际使用的指定坐标/推导读回域，从而不要求当前两个非同步 Nu 坐标一起派发。未改原 R/Nu/Rd 或共享域，未写此修订的闭包证明。
- 未执行候选：原 LowKeep 可能需要链指标移位或共尾性论证，而不是逐步生成任意前缀的原 StepU。未证明这种办法，也未把 PrefixU 供给失败解读成它的否定。
- 未执行判断：自身折叠在非零层、ν=[] 时也许能用参照比较之外的外部支配证明；本轮 NodeFrame 否定不涉及这种证明。以上不是穷尽列表。

#### 4. 文件、冷编与内存

| 文件（probes/OCF/Lean/） | 总行 / 代码行 / 非空代码 | 冷编退出 | RTS max residency（bytes） | RTS 总内存 MiB | 秒 |
|---|---:|---:|---:|---:|---:|---:|
| `YiGTCheck.lagda.md` | 78 / 67 / 55 | 0 | 1,381,855,512 | 2459 | 15.09 |
| `YiGTGen.lagda.md` | 114 / 108 / 93 | 0 | 989,005,432 | 1891 | 12.10 |
| `YiGTUp.lagda.md` | 84 / 77 / 70 | 0 | 988,942,896 | 1895 | 11.93 |
| `YiGTNode.lagda.md` | 105 / 98 / 88 | 0 | 1,337,493,064 | 2529 | 15.11 |
| `YiGTIndex.lagda.md` | 98 / 91 / 78 | 0 | 1,497,059,424 | 2504 | 15.15 |
| `YiGTEmb.lagda.md` | 75 / 68 / 64 | 0 | 1,417,381,472 | 2370 | 15.32 |
| `YiGTSelf.lagda.md` | 74 / 67 / 63 | 0 | 1,329,158,992 | 2434 | 15.22 |
| `YiGTFold.lagda.md` | 74 / 67 / 61 | 0 | 1,430,336,792 | 2524 | 15.45 |
| `YiGTDirect.lagda.md` | 116 / 109 / 98 | 0 | 1,356,607,376 | 2315 | 15.36 |
| `YiGTSlot.lagda.md` | 77 / 71 / 63 | 0 | 1,350,115,392 | 2508 | 15.24 |
| `YiGTLow.lagda.md` | 48 / 41 / 37 | 0 | 1,317,100,792 | 2448 | 15.27 |
| `YiGTIndexNeg.lagda.md` | 59 / 52 / 42 | 0 | 1,486,829,464 | 2583 | 15.51 |
| `YiGTInst.lagda.md` | 96 / 89 / 75 | 0 | 1,395,273,648 | 2343 | 15.60 |
| `YiGTCompat.lagda.md` | 34 / 28 / 25 | 0 | 1,354,215,912 | 2284 | 15.74 |
| `YiGTOmega.lagda.md` | 60 / 53 / 46 | 0 | 1,522,954,552 | 2577 | 15.45 |

合计 1192 总行，958 非空代码行；最终禁用构造、本机路径、函数外延扫描全部为 0。

行数口径同时列总行、代码块内行、非空且非纯注释代码行。全部 15 件均是验收侧文件。旧 YiGTCheck 的源码 SHA-256 保持首次冻结值 `70840b5f3f1638a8cf8ebc14654b64ff7b0ca94aa09b47587bb0a1719d233137`。

所有 Agda 串行，均 `+RTS -M5G -s -RTS`。定稿时逐件只删除自身 `.agdai` 后冷编，依赖接口不删；不用 --ignore-interfaces。RTS residency 不是进程 RSS。最终冷编日志要求仅有本模块一个 Checking 行，结果见 `final-cold-results.json`。

所有实验目录、源码、脚本、日志与记录：

仓库源码（全部 15 件）：

- `<仓库>/probes/OCF/Lean/YiGTCheck.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTGen.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTUp.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTNode.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTIndex.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTEmb.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTSelf.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTFold.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTDirect.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTSlot.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTLow.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTIndexNeg.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTInst.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTCompat.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGTOmega.lagda.md`

实验目录仅 `<实验目录>/` 及其中 `continue/`；私有源码为初始 YiGTMin.agda、YiGTBridge.agda、YiGTBaseProbe.agda，均按原回报冷编 0。所有私有文件逐件列出如下（.agdai 为对应同名源码的编译接口，不作为源码交付）：

- `<实验目录>/YiGT-report-initial.md`
- `<实验目录>/YiGTBaseProbe-cold.log`
- `<实验目录>/YiGTBaseProbe.agda`
- `<实验目录>/YiGTBridge-cold.log`
- `<实验目录>/YiGTBridge.agda`
- `<实验目录>/YiGTMin-cold.log`
- `<实验目录>/YiGTMin.agda`
- `<实验目录>/base-first.log`
- `<实验目录>/bridge-first.log`
- `<实验目录>/check-cold.log`
- `<实验目录>/check-first.log`
- `<实验目录>/check-fixed.log`
- `<实验目录>/cold-status.json`
- `<实验目录>/continue/YiGTCheck-final-cold.log`
- `<实验目录>/continue/YiGTCompat-final-cold.log`
- `<实验目录>/continue/YiGTDirect-final-cold.log`
- `<实验目录>/continue/YiGTEmb-final-cold.log`
- `<实验目录>/continue/YiGTFold-final-cold.log`
- `<实验目录>/continue/YiGTGen-final-cold.log`
- `<实验目录>/continue/YiGTIndex-final-cold.log`
- `<实验目录>/continue/YiGTIndexNeg-final-cold.log`
- `<实验目录>/continue/YiGTInst-final-cold.log`
- `<实验目录>/continue/YiGTLow-final-cold.log`
- `<实验目录>/continue/YiGTNode-final-cold.log`
- `<实验目录>/continue/YiGTOmega-final-cold.log`
- `<实验目录>/continue/YiGTSelf-final-cold.log`
- `<实验目录>/continue/YiGTSlot-final-cold.log`
- `<实验目录>/continue/YiGTUp-final-cold.log`
- `<实验目录>/continue/compat-1.log`
- `<实验目录>/continue/compat-2.log`
- `<实验目录>/continue/direct-1.log`
- `<实验目录>/continue/direct-2.log`
- `<实验目录>/continue/direct-3.log`
- `<实验目录>/continue/direct-fixedmeta.log`
- `<实验目录>/continue/emb-1.log`
- `<实验目录>/continue/final-cold-results.json`
- `<实验目录>/continue/final-cold.py`
- `<实验目录>/continue/final-scan.json`
- `<实验目录>/continue/fold-1.log`
- `<实验目录>/continue/fold-2.log`
- `<实验目录>/continue/freeze.json`
- `<实验目录>/continue/gen-1.log`
- `<实验目录>/continue/gen-2.log`
- `<实验目录>/continue/gen-3.log`
- `<实验目录>/continue/index-1.log`
- `<实验目录>/continue/indexneg-1.log`
- `<实验目录>/continue/indexneg-2.log`
- `<实验目录>/continue/inst-1.log`
- `<实验目录>/continue/inst-2.log`
- `<实验目录>/continue/low-1.log`
- `<实验目录>/continue/node-1.log`
- `<实验目录>/continue/node-2.log`
- `<实验目录>/continue/node-3.log`
- `<实验目录>/continue/node-4.log`
- `<实验目录>/continue/omega-1.log`
- `<实验目录>/continue/refactor-1.log`
- `<实验目录>/continue/scan-pre-cold.json`
- `<实验目录>/continue/slot-1.log`
- `<实验目录>/continue/slot-2.log`
- `<实验目录>/continue/up-1.log`
- `<实验目录>/continue/up-2.log`
- `<实验目录>/continue/up-3.log`
- `<实验目录>/libraries`
- `<实验目录>/min-first.log`
- `<实验目录>/scan.json`
- `<实验目录>/verification.json`

完整最终回报本身为 `<临时目录>`。原阶段统计 `cold-status.json/verification.json` 与续作最终统计 `continue/final-cold-results.json` 分开存放，不能把前者误读为新增 14 件的冷编记录。

#### 5. 定理表（重要出口）

下表引用的逐字签名在后面的源码签名附录中。所有“编译定理”均是 Agda 检查的对应陈述；条件定理连同条件一起读。

| 名字 | 白话 | 档 |
|---|---|---|
| `YiGTGen.nextψ/limψ/nodeψ/emb-pres` | 任意层上的后继、ℕ 极限、保留 Ω、字面路径嵌入保持 | 编译定理 |
| `YiGTUp.up-pres` | 明确 UpFrame 下的一般上折保持 | 编译定理；框架非自动 |
| `YiGTNode.Core.node-row` | 给出链时的通用 Ω 行，包括保留与走链 | 编译定理 |
| `YiGTIndex.index-zero` | 所有源层的标准零路径都有 IndexOK | 编译定理 |
| `YiGTIndex.index-tw1-slot` | 实际 tw 1 的主下标槽位路径有 IndexOK | 编译定理；不是 IndexTree |
| `YiGTIndex.shift-prefix` | SlotPres 供给递归更新底的 PrefixU | 编译定理；后由 Direct 消去 SlotPres 参数 |
| `YiGTEmb.emb-row` | 指定证据域内的实际嵌入各行 | 编译定理；表缺项行未覆盖 |
| `YiGTSelf.self-pres` | 一般 ψν 的自身折叠保持 | 编译定理；不是原全层 SelfKeep |
| `YiGTFold.pres` | Kit 下的一般目标各行合成 | 编译定理；Kit 包含槽位保持/步进 |
| `YiGTDirect.direct/layer-at` | 按推导互递归消去 SlotPres/StepU′ 参数 | 编译定理；仍需 IndexTree/LayerIndex |
| `YiGTSlot.slot-pres/step′/kit` | IndexTree 给槽位保持、补前缀步进与旧合成所需 Kit | 编译定理；不能声称实际 tw 1 已实例化 |
| `YiGTSlot.step-layer/omega-step-at` | 固定本层 o/r 的补前缀步进 | 编译定理；Ω 形状有非空片段 |
| `YiGTLow.low-at′/low-layer-prefix` | 多 PrefixU 的原 LowKeep 形状 | 编译定理；原 LowKeep 未得 |
| `YiGTInst.slot-one/it-one/self-one` | 最小非零层的槽位、递归域和 ψ₁ 自身保持 | 编译定理 |
| `YiGTInst.low-one-next` | 主线比较表下前缀 1、逐点 next 底的最小层保持 | 编译定理；无值出口声称 |
| `YiGTCompat.self-zeroᵍ` | 原抽象 SelfKeep 的零层实例 | 编译定理 |
| `YiGTOmega.layer-Ω₀/prefix-Ω₀/step-Ω₀` | Ω 形状条件域与步进的非空片段 | 编译定理；不是规范塔强度 |
| `YiGTIndexNeg.no-frame₂` | 当前同步 Frame 在 fn 2 到 fn 1 对任意 ν 都失败 | 编译否定，只杀该字段 |
| `YiGTIndexNeg.no-index-tree-tw1/no-layer-tw1` | 当前证据域覆盖不了实际 tw 1 | 编译否定，只杀该证据域 |
| `YiGTIndexNeg.no-read→frame₁` | Rd 不能自动供给本同步 Frame | 编译否定，不否定原 SelfKeep |
| `YiGTCheck.no-ok→base` | 原 OK 不能补一般前缀底关系 | 编译否定；旧冻结文件未改 |

#### 6. 事故、偏离、引用与冻结

- 首次停止把未知参数未实填当作第 0 步不成立，这个判断不符合原简报。主审纠正后续作，已完成真实互递归与各行；不再拿首次停止的理由作为当前接口的否定依据。
- 一次真正的终止失败在 `YiGTUp.up-pres` 首稿：同时沿源层与关系推导递归时，mw/mc 调用未获下降。第一次重设计改成外层对源层递归、内层固定源层对推导归纳后通过；没有第二次重设计失败。Direct 的真实互递归一次数学设计即获终止检查接受。
- 其余 42 是实现错误：Gen 的未知层 child 类型未化简，改为 nd 形状模块参数；Node 的显式 forall 语法；Emb 的 down stop 隐式 s/h 与新增局部前提的命名；Slot 的 [] 导入；Compat 的隐藏参数次序；Direct 的 ≡ 导入。未开启额外公理、K、强制终止或正性豁免。
- 没有 5G 堆耗尽、超时或内部错误。没有假造“两次重新设计失败”作为停止理由。当前证据域不能覆盖 tw 1 的依据是编译否定；它不关闭一般目标路线。原要求的全层实填与原 LowKeep 仍未完成。
- 只新建 YiGT 前缀文件；旧冻结 Check 原文未改。没有改已有共享文件、src/archive、README/LOG/台账/留档；未提交、未推送、未装包、未派子智能体。
- 已读完整原简报、AGENTS、手册 §4，以及原 LK/GI/TB 相关定义、关系、折叠与证明。续作完整读 YiSU 回报、YiSUIface、YiSUMin、YiSUBridge，复用 rd-zero、to-one、step′-one、prefix-zero、Bnext/ok-next/prefix-next 等候选。YiSU 当时主审仍在复核；本路没有自删 SU 接口独立冷编其闭包，依赖沿用缓存，交主审统一复核。
- `YiFMFin.rd-zero` 等只检索过签名和局部行，未导入；主审后台其它路线的回报未用于本轮数学成果。`YiLLLeafNeg` 只由旧 Check 用 Fin.one-ref/conflict，未调用 noLeaf。
- 未做 HTML、定义切片、无记号导入闭包声称；全部新增文件明确是读记号验收文件。数学定义没有回改前三层。

**已冻结：全部 15 件源码逐件自删接口冷编 0，日志仅本模块 Checking，扫描 0；旧 Check 哈希未变。冻结清单 `continue/freeze.json`。源码不再修改，交主审独立复核。原全层目标与原 LowKeep 未完成，未把本证据域的否定记作一般路线否定。**

#### 附录：全部源码签名（逐字）

##### YiGTCheck.lagda.md

```agda
PresJ : (ℓ j : L) → j ≤ ℓ → Set

SlotBase : ∀ k h → Base (nd (sΩ k) h) → E.T → E.T → Set

zero-target : (o : Ok zero) (r : Rb zero) (B : Base zero) → OK B
  → (t : E.T) (β : Tr⁺ zero) → GR.R zero (E.ψ [] t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R zero a x
  → GR.R zero (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ zero o r B zero self β x))

h₁ : Tr zero → L

rd₀ : GR.Rd zero []

base-ok : OK (B₀ (tw 1))

base-empty : SlotBase zero h₁ (B₀ (tw 1)) [] []

no-base-one : SlotBase zero h₁ (B₀ (tw 1)) [] (E.natT 1) → ⊥

no-ok→base : (OK (B₀ (tw 1)) → SlotBase zero h₁ (B₀ (tw 1)) [] (E.natT 1)) → ⊥

sample-child : (η : E.T) → GR.R (tw 1) (E.fsT (E.Ωs []) (E.γT (η ++ E.Ωs []) [] zero)) (suc zero)

sample-low : (η : E.T) → GR.R zero (E.γT (η ++ E.Ωs []) [] zero) (suc zero)

sample-step : (o : Ok (tw 1)) (r : Rb (tw 1))
  → GR.R zero (E.γT (E.Ωs []) [] (suc zero))
      (proj₁ (ψ (tw 1) o r (B₀ (tw 1)) zero (ink self)
        (B₀ (tw 1) zero (ink self)) (suc zero)))
```

##### YiGTGen.lagda.md

```agda
weakᴿ : ∀ ℓ {t x y} → GR.R ℓ t x → ℓ ⊢ x ◃ y → GR.R ℓ t y

weakenᴿ : ∀ ℓ {t x y} → GR.R ℓ t x → x ⊴ y → GR.R ℓ t y

closeᴿ : ∀ ℓ {s t x} → s ≤ᵀ t → GR.R ℓ t x → GR.R ℓ s x

limᴿ : ∀ ℓ {t x} → E.cof t ≡ E.cω → (∀ n → GR.R ℓ (E.fsn t n) x) → GR.R ℓ t x

nextᴿ : ∀ ℓ {t p} (β : Tr⁺ ℓ) → E.cof t ≡ E.cω
  → (∀ n → E.fsn t n ≡ replicate n p)
  → GR.R ℓ (p ∷ []) (proj₁ β) → GR.R ℓ t (proj₁ (next⁺ β))

cumᴿ : ∀ ℓ {t} (F : ℕ → Tr⁺ ℓ) (n : ℕ)
  → GR.R ℓ t (proj₁ (F n)) → GR.R ℓ t (proj₁ (limc⁺ F))

zlᴿ : ∀ ℓ {S : Sg} (F : T S → Tr ℓ)
  → (∀ {x y} → Lt S x y → ℓ ⊢ F x ◃ F y)
  → ∀ {t} → GR.R ℓ t (F zero) → ∀ x → GR.R ℓ t (F x)

nodeᴿ : ∀ ℓ (p : Pos ℓ) {t κ} {g : Br ℓ p → Tr ℓ}
  → E.cof t ≡ E.cΩ κ → GR.Nu ℓ p κ
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT t η) (g c))
  → GR.R ℓ t (Ω p g)

app≤ν : ∀ ν t {a b} → a ≤ᵀ b
  → (E.ψ ν (t ++ a) ∷ []) ≤ᵀ (E.ψ ν (t ++ b) ∷ [])

Ω≤ψ : ∀ ν t → E.Ωt ν ≤ᵀ (E.ψ ν t ∷ [])

emb-pres : ∀ ℓ (o : Ok ℓ) {k} (w : k ≤ ℓ) (y : Tr⁺ k) {a}
  → GR.R k a (proj₁ y) → GR.R ℓ a (proj₁ (emb ℓ o w y))

nextψ : ∀ ℓ ν t a → E.cof a ≡ E.c1 → (β : Tr⁺ ℓ)
  → GR.R ℓ (E.ψ ν (t ++ E.pred a) ∷ []) (proj₁ β)
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (next⁺ β))

limψ : ∀ ℓ ν t a → E.cof a ≡ E.cω → (x : Tr ℓ)
  → (∀ n → GR.R ℓ (E.ψ ν (t ++ E.fsn a n) ∷ []) x)
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) x

nodeψ : ∀ ℓ ν t a (p : Pos ℓ) {κ} {g : Br ℓ p → Tr ℓ}
  → E.cof a ≡ E.cΩ κ → Pen (E.cmpᵀ (E.sucT κ) ν) → GR.Nu ℓ p κ
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.ψ ν (t ++ E.fsT a η) ∷ []) (g c))
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (Ω p g)
```

##### YiGTUp.lagda.md

```agda
UpFrame : ∀ {ℓ} → E.T → (j : L) → Dn ℓ j → Set

down-frame : ∀ {ℓ} ν s h (d : Dn ℓ (nd s h)) → UpFrame ν (nd s h) d
  → (c : Ch s) → UpFrame ν (h c) (down d c)

zero-frame : ∀ {ℓ} ν (d : Dn ℓ zero) → UpFrame ν zero d

up-zero : ∀ {ℓ} ν (d : Dn ℓ zero) t (β : Tr⁺ ℓ)
  → GR.R ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R zero a x
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (Up zero d β x))

UpAt : L → Set

fold-up : ∀ s h → ((c : Ch s) → UpAt (h c)) → UpAt (nd s h)

up-pres : ∀ j → UpAt j
```

##### YiGTNode.lagda.md

```agda
KeepSpec : ∀ ℓ j ν (p : Pos ℓ) κ → Keep j (Br ℓ p) (fromBr ℓ p zero) → Set

NodeFrame : ∀ ℓ → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set

start-prefix : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) t → PrefixU B t
  → (p : Pos ℓ) (κ : E.T) → GR.Nu ℓ p κ → (g : Br ℓ p → Tr ℓ)
  → GR.Low ℓ p (E.Ωt κ) (feed ℓ o r B p g (fromBr ℓ p zero))

chain′ : ∀ ℓ → StepU′ ℓ → (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t → ∀ a (p : Pos ℓ) κ → GR.Nu ℓ p κ → E.cof a ≡ E.cΩ κ
  → (g : Br ℓ p → Tr ℓ)
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
  → ∀ n → GR.Low ℓ p (E.γT (t ++ a) κ n)
    (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))

ChainAt : ∀ ℓ → Ok ℓ → Rb ℓ → Base ℓ → E.T → E.T → (p : Pos ℓ) → E.T → (Br ℓ p → Tr ℓ) → Set

  F : Tr ℓ → Tr⁺ j

  node-at : ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → GR.Nu ℓ p κ
    → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
    → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → ChainAt ℓ o r B t a p κ g
    → (K : Keep j (Br ℓ p) (fromBr ℓ p zero)) → KeepSpec ℓ j ν p κ K
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (node⁺ K (λ c → F (g c)) (feed ℓ o r B p g)))

  node-row : NodeFrame ℓ o j w ν
    → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → GR.Nu ℓ p κ
    → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
    → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → ChainAt ℓ o r B t a p κ g
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F (Ω p g)))

  node-row : NodeFrame ℓ o j w ν
    → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → GR.Nu ℓ p κ
    → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
    → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F (Ω p g)))
```

##### YiGTIndex.lagda.md

```agda
CWReq : ∀ {A B : Set} → A ⊎ B → (A → Set) → (B → Set) → Set

DWReq : ∀ {A B : Set} → Maybe (A ⊎ B) → (A → Set) → (B → Set) → Set

  IndexOK : ∀ ℓ → Ok ℓ → Rb ℓ → ∀ j → j ≤ ℓ → E.T → Set

  RouteOK : ∀ ℓ → Ok ℓ → Rb ℓ → ∀ j → j ≤ ℓ → E.T → Set

zero-spec : ∀ ℓ (p : Pos ℓ) κ (K : Keep zero (Br ℓ p) (fromBr ℓ p zero)) → KeepSpec ℓ zero [] p κ K

zero-frame : ∀ ℓ (o : Ok ℓ) (w : zero ≤ ℓ) → NodeFrame ℓ o zero w []

index-zero : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → IndexOK ℓ o r zero (z≤ ℓ) []

index-lift : ∀ a (o : Ok (zero ⊕ a)) (r : Rb (zero ⊕ a))
  → IndexOK (zero ⊕ a) o r zero (self ∙ lift zero a) []

index-tw1-slot : (r : Rb (tw 1)) → IndexOK (tw 1) (Ok-tw 1) r zero (ink self) []

SlotPres : L → Set

shift-prefix : ∀ s h → SlotPres (nd s h)
  → (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → OK B
  → (t : E.T) → PrefixU B t → ∀ {a x} → GR.R (nd s h) a x → (c : Ch s)
  → PrefixU (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) (t ++ a)

PresAt : L → Set

Kit : L → Set
```

##### YiGTEmb.lagda.md

```agda
self-child : ∀ s h (o : Ok (nd s h)) ν → NodeFrame (nd s h) o (nd s h) self ν
  → (c : Ch s) → UpFrame ν (h c) (down {s = s} {h = h} stop c)

  (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h))

  (gb : OK B) (t : E.T) (pref : PrefixU B t) where

  cb : (x : Tr (nd s h)) (c : Ch s) → Base (h c)

  child-at : ∀ j ν {a b x} (c : Ch s) (v : j ≤ h c) → IndexOK (h c) (proj₂ o c) (proj₂ r c) j v ν
    → (β : Tr⁺ j) → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ β) → GR.R (nd s h) a x
    → PrefixU (cb x c) (t ++ a) → (y : Tr (h c)) → GR.R (h c) b y
    → GR.R j (E.ψ ν ((t ++ a) ++ b) ∷ []) (proj₁ (ψ (h c) (proj₂ o c) (proj₂ r c) (cb x c) j v β y))

emb-row : ∀ s h (child : (c : Ch s) → PresAt (h c))
  → (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (gb : OK B)
  → (t : E.T) (pref : PrefixU B t) → ∀ j (w : j ≤ nd s h) ν → IndexOK (nd s h) o r j w ν
  → (β : Tr⁺ j) → ∀ {a b x} (c : Ch s) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → GR.R (nd s h) a x
  → ((d : Ch s) → PrefixU (Top.cb s h child o r B gb t pref x d) (t ++ a))
  → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ (nd s h) o r B j w β x))
  → GR.R (h c) b y
  → GR.R j (E.ψ ν ((t ++ a) ++ b) ∷ []) (proj₁ (ψ (nd s h) o r B j w β (up x c y e)))
```

##### YiGTSelf.lagda.md

```agda
zero-self : (o : Ok zero) (r : Rb zero) (B : Base zero) (t ν : E.T) (β : Tr⁺ zero)
  → GR.R zero (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R zero a x
  → GR.R zero (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ zero o r B zero self β x))

  (B : Base (nd s h)) (ν t : E.T) (fr : NodeFrame (nd s h) o (nd s h) self ν)

  (β : Tr⁺ (nd s h)) (mb : GR.R (nd s h) (E.ψ ν t ∷ []) (proj₁ β)) where

  F : Tr (nd s h) → Tr⁺ (nd s h)

  LF : ∀ {a x} → GR.R (nd s h) a x → GR.R (nd s h) (E.ψ ν (t ++ a) ∷ []) (proj₁ (F x))

self-pres : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) ν t → NodeFrame ℓ o ℓ self ν
  → (β : Tr⁺ ℓ) → GR.R ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B ℓ self β x))
```

##### YiGTFold.lagda.md

```agda
pres-zero : PresAt zero

  (sp : SlotPres (nd s h)) (st : StepU′ (nd s h))

  (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (gb : OK B)

  (t : E.T) (pref : PrefixU B t) where

  F : ∀ j → j ≤ nd s h → Tr⁺ j → Tr (nd s h) → Tr⁺ j

  cb : (x : Tr (nd s h)) (c : Ch s) → Base (h c)

  LF : ∀ j (w : j ≤ nd s h) ν → IndexOK (nd s h) o r j w ν
    → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
    → ∀ {a x} → GR.R (nd s h) a x
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F j w β x))

pres : ∀ ℓ → Kit ℓ → PresAt ℓ
```

##### YiGTDirect.lagda.md

```agda
SlotIndex : ∀ ℓ → Ok ℓ → Rb ℓ → Set

IndexTree : L → Set

slot-index : ∀ ℓ → IndexTree ℓ → (o : Ok ℓ) (r : Rb ℓ) → SlotIndex ℓ o r

  (o : Ok (nd s h)) (r : Rb (nd s h)) (slots : SlotIndex (nd s h) o r)

  (B : Base (nd s h)) (gb : OK B)

  (t : E.T) (pref : PrefixU B t) where

  F : ∀ j → j ≤ nd s h → Tr⁺ j → Tr (nd s h) → Tr⁺ j

    LF : ∀ j (w : j ≤ nd s h) ν → IndexOK (nd s h) o r j w ν
      → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
      → ∀ {a x} → GR.R (nd s h) a x
      → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F j w β x))

    update : ∀ {a x} → GR.R (nd s h) a x → (c : Ch s)
      → PrefixU (Emb.Top.cb s h child o r B gb t pref x c) (t ++ a)

    chain : ∀ a (p : Pos (nd s h)) κ → GR.Nu (nd s h) p κ → E.cof a ≡ E.cΩ κ
      → (g : Br (nd s h) p → Tr (nd s h))
      → (∀ η c → GR.Low (nd s h) p η c → GR.R (nd s h) (E.fsT a η) (g c))
      → ChainAt (nd s h) o r B t a p κ g

direct : ∀ ℓ → IndexTree ℓ → PresAt ℓ

LayerIndex : ∀ ℓ → Ok ℓ → Rb ℓ → Set

layer-at : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → LayerIndex ℓ o r
  → (B : Base ℓ) → OK B → (t : E.T) → PrefixU B t
  → (j : L) (w : j ≤ ℓ) (ν : E.T) → IndexOK ℓ o r j w ν
  → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))
```

##### YiGTSlot.lagda.md

```agda
slot-pres : ∀ ℓ → IndexTree ℓ → SlotPres ℓ

step-from-slot : ∀ ℓ → SlotPres ℓ → StepU′ ℓ

step′ : ∀ ℓ → IndexTree ℓ → StepU′ ℓ

kit : ∀ ℓ → IndexTree ℓ → Kit ℓ

layer-index : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → LayerIndex ℓ o r → SlotIndex ℓ o r

step-layer : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → LayerIndex ℓ o r
  → (B : Base ℓ) → OK B → (t : E.T) → PrefixU B t
  → (a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (OCF.Lean.YiLKIface.feed ℓ o r B p g c)

OmegaStepAt : (k : L) (h : Tr k → L) → Ok (nd (sΩ k) h) → Rb (nd (sΩ k) h) → Set

omega-step-at : ∀ k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h))
  → LayerIndex (nd (sΩ k) h) o r → OmegaStepAt k h o r
```

##### YiGTLow.lagda.md

```agda
LowAt′ : L → Set

low-at′ : ∀ ℓ → IndexTree ℓ → LowAt′ ℓ

low-when-prefix : ∀ ℓ (it : IndexTree ℓ) (b : Bsᵍ ℓ) (β : Tr⁺ zero) (t : E.T)
  → Bdᵍ b (z≤ ℓ) β t → PrefixU (proj₂ (proj₂ b)) t
  → ∀ {a x} → GR.R ℓ a x
  → GR.R zero (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψᵍ ℓ b zero (z≤ ℓ) β x))

low-layer-prefix : ∀ ℓ (b : Bsᵍ ℓ) → LayerIndex ℓ (proj₁ b) (proj₁ (proj₂ b))
  → (β : Tr⁺ zero) (t : E.T) → Bdᵍ b (z≤ ℓ) β t → PrefixU (proj₂ (proj₂ b)) t
  → ∀ {a x} → GR.R ℓ a x
  → GR.R zero (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψᵍ ℓ b zero (z≤ ℓ) β x))
```

##### YiGTIndexNeg.lagda.md

```agda
p-top : Pos (fn 2)

p-deep : Pos (fn 2)

pen-gt : ∀ {m} → Pen m → m ≡ E.gt → ⊥

no-frame₂ : ∀ (o : Ok (fn 2)) ν → NodeFrame (fn 2) o (fn 1) (inc tt self) ν → ⊥

no-slot-index₂ : ∀ (o : Ok (fn 2)) (r : Rb (fn 2)) → SlotIndex (fn 2) o r → ⊥

no-index-tree₂ : IndexTree (fn 2) → ⊥

no-index-tree-tw1 : IndexTree (tw 1) → ⊥

no-layer-tw1 : ∀ (o : Ok (tw 1)) (r : Rb (tw 1)) → LayerIndex (tw 1) o r → ⊥

no-self-frame₁-zero : (o : Ok (fn 1)) → NodeFrame (fn 1) o (fn 1) self [] → ⊥

no-read→frame₁ : ((ν : E.T) → GR.Rd (fn 1) ν → NodeFrame (fn 1) (okf 1) (fn 1) self ν) → ⊥
```

##### YiGTInst.lagda.md

```agda
slot-one : SlotPres (fn 1)

kit-one : Kit (fn 1)

pres-one : PresAt (fn 1)

slot-index-one : (o : Ok (fn 1)) (r : Rb (fn 1)) → SlotIndex (fn 1) o r

it-one : IndexTree (fn 1)

one-frame : (o : Ok (fn 1)) → NodeFrame (fn 1) o (fn 1) self (E.natT 1)

self-one : (o : Ok (fn 1)) (r : Rb (fn 1)) (B : Base (fn 1)) (t : E.T) (β : Tr⁺ (fn 1))
  → GR.R (fn 1) (E.ψ (E.natT 1) t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R (fn 1) a x
  → GR.R (fn 1) (E.ψ (E.natT 1) (t ++ a) ∷ [])
      (proj₁ (ψ (fn 1) o r B (fn 1) self β x))

tw1-index : (r : Rb (tw 1)) → IndexOK (tw 1) (Ok-tw 1) r zero (ink self) []

one-leaf : GR.R (fn 1) (E.Ωs []) (proj₁ (Ωt (fn 1)))

one-prefix : PrefixU (B₀ (fn 1)) []

rd-one : GR.Rd (fn 1) (E.natT 1)

prefix-one : PrefixU Bnext (E.natT 1)

beta-one : GR.R zero (E.ψ [] (E.natT 1) ∷ []) (proj₁ (next⁺ (Ωt zero)))

low-one-next : ∀ {a x} → GR.R (fn 1) a x
  → GR.R zero (E.ψ [] (E.natT 1 ++ a) ∷ [])
      (proj₁ (ψ (fn 1) (okf 1) (MT.rbᶻ (fn 1)) Bnext zero (z≤ (fn 1)) (next⁺ (Ωt zero)) x))
```

##### YiGTCompat.lagda.md

```agda
SelfAtᵍ : L → Set

self-under-frame : ∀ ℓ (b : Bsᵍ ℓ) → NodeFrame ℓ (proj₁ b) ℓ self []
  → (β : Tr⁺ ℓ) → ∀ {P a x} → GR.R ℓ (E.ψ [] P ∷ []) (proj₁ β) → GR.R ℓ a x
  → GR.R ℓ (E.ψ [] (P ++ a) ∷ []) (proj₁ (ψᵍ ℓ b ℓ self β x))

self-zeroᵍ : SelfAtᵍ zero
```

##### YiGTOmega.lagda.md

```agda
Ω₀ : L

oΩ : Ok Ω₀

rΩ : Rb Ω₀

zero-path : (w : zero ≤ zero) → IndexOK zero tt tt zero w []

layer-Ω₀ : LayerIndex Ω₀ oΩ rΩ

  slots : OCF.Lean.YiGTDirect.SlotIndex Ω₀ oΩ rΩ

prefix-Ω₀ : PrefixU (B₀ Ω₀) []

step-Ω₀ : OmegaStepAt zero (λ _ → zero) oΩ rΩ
```
