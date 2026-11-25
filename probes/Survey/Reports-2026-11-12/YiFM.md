# 新旧两族对接（数学，合并同类引理） (YiFM)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十七批；外部模型，作者转发 |
| 前缀 | `YiFM` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：新旧两族对接（数学，合并同类引理）（前缀 YiFM）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十七批五路之一（选项原文 "新旧两族对接 (Recommended)"），与在跑的 YiPJ、YiNX、YiXV 以及本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **两套关系族**：
  - 新族 `YiGIRel`：`R : (ℓ : L) → E.T → Tr ℓ → Set`，层号的读法 `Rd ℓ = Cl (Hd ℓ)`，闭包 `Cl` 的构造子是 `c0`、`ca`、`cL`（ℕ 极限）、`cc`（沿项序向下封闭）。`YiGICheck.rd-fin : ∀ n → GR.Rd (fn n) (E.natT n)`。
  - 旧族 `YiHCFam`：`M : (n : ℕ) → E.T → Tr (fn n) → Set`，按指定的自然数读法（`Lw⁼`、`LwP`、`Nw`）；底层数据类型是 `YiHCRel.Mᴴ`（构造子含 `mc`）。
- YiGI 回报：**没有证明新族在有限层等于 `YiHCFam.M`；原有限族的高层保持定理不能直接搬用。**
- **用旧族写成的、主线折叠上的已有结果**：`YiLTFold`（`Qu`、`LF`）、`YiLTKid`、`YiLTLift`（`Q : E.T → L → Set`，`StepS`，`lift-red : StepS → Lift₁`）、`YiKPRel`、`YiKQ*`。在跑的 YiPJ 也在用旧族的 `Q` 补 `StepS`。
- 主审的读法（判断）：`eboᵍ` 的 `Leaf`、`Lift` 只谈读法；YiLT 的 `Lift₁`、YiKQ 的 `Lift₂` 是 `LowKeep` 在读回层号上的片段。AGENTS："同类引理以不同名字第二次出现时, 合并成一条并写进接口"。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：在 n = 1 上写出两个方向 `M 1 s x → R (fn 1) s x` 与反方向，确认类型正确，并在 x = `Ωt (fn 1)` 的树上各给一个实例。不成立就停下回报。
1. **旧 ⇒ 新**：对一切 n 证 `M n → R (fn n)`（要一条 `Mᴴ` 对参数单调的映射引理；`Nw` ⇒ `Rd` 用 `rd-fin` 与 `cc`）。
2. **新 ⇒ 旧**：证明，或者交第一个精确的差别（哪一种 `Rd` 推导在旧族里没有对应）。若不成立，找出足够搬运保持定理的最弱陈述（例如在 `mc` 封闭之下的反方向）。
3. **搬运**：
   - 写出 `eboᵍ` 的 `LowKeep` 限到有限源层号 `fn n`、目标第 0 层的形式，并用旧族上最强的现有保持定理（`YiLTFold` 一类）给出它；
   - 写出 YiLT 的 `Lift₁` 在新族里的对应陈述（读回层号上的 `LowKeep` 片段加 `Leaf`），编译 "`YiLTLift` 的 `Lift₁` ⇒ 这个对应陈述"，使 YiPJ 将来的结果能接进 `eboᵍ`。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiFM`（模块名 `OCF.Lean.YiFM…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiNX`、`YiXV`、`YiLK`、`YiLL`、`YiPC`、`YiVW`）。验收文件，文首标明。
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

3 件、149 同口径代码行；主审逐件删自身接口、5G 独立冷编全 0，各仅自身 Checking，哈希不变；禁用构造、洞、本机路径、Funext 0。已读全部源码与完整范围、停止依据。RegularCheck 独立复跑 0，两次改写独立复跑 42，首错与原报告相同。mapᴴ 的 Low 逆向、Ch/Nu 正向；首层双向与第二层旧到新已证。余尾字段直接反向及两种指定抬高被否定，一般关系反向未证也未否定。第 3 步搬运未做；没有新增值界。

## 回报原文（本会话执行）

### YiFM 完整回报（定稿）

源码已冻结；三份仓库源码已逐件删除自身接口后冷编，均退出 0。等待主审独立冷编复核。本报告不代替主审复核。

#### 1. 判决与执行范围

对纲领与目标的意义：前三层的树、折叠、合法性完全未改。本路给验收关系补了一条共用的参数搬运引理，明确了分支关系的逆向要求，并完成首层双向及第二层旧到新的对接。它没有提高主线的无条件序数值下界，没有填出全域 Leaf、Lift、LowKeep 或全塔出口条件，也没有证明两套关系族不等价。

按简报顺序先完成第 0 步。`YiFMMin.agda` 的两个全称方向及 Ω 树上的往返实例均退出 0；不是仅验证类型名字或留前提。该临时目录创建后约 1 分钟内完成第一次检查，满足 30 分钟要求。第 1 层方向的范围是所有参照项、所有该层树，所以这是固定层上的全称编译定理，不是有限树样本测试。

| 简报步骤 | 实际完成情况 | 档 |
|---|---|---|
| 0：第 1 层双向与 Ω 树实例 | 已完成，临时文件及正式文件都有证明 | 编译定理 |
| 1：所有有限层旧 ⇒ 新 | 完成 `mapᴴ`；n=0 定义性一致，n=1、2 有全称转换；任意 n 未完成 | 已列部分为编译定理；一般式未走通 |
| 2：新 ⇒ 旧或第一处精确差别 | n=1 已证；第 2 层顶槽的 Nu 字段直接反向映射被精确否定；`R (fn 2) → M 2` 未证也未否定 | 编译定理与未走通分别列明 |
| 2：足以搬保持的最弱陈述 | 未确立；`regular-back` 仅覆盖正规叶，不能宣称足够搬运任意关系推导 | 编译片段；足够性未证 |
| 3：有限源 LowKeep 与 Lift₁ 新族对应 | 停止条件触发前未进入；未交付这两条搬运 | 未开展 |

停止发生在试图把第 2 层新族的 `mΩ` 搬回旧族的同一处。初始直接字段映射由 `no-direct-nu-back²` 排除；之后两次改写分别为仅抬内层和同时抬内外层，最小临时检查均退出 42，对应的精确否定已经编译。依简报“同一处两次重新设计仍过不了检查器”停止数学扩展，后续只整理既有源码、冷编、检查前提实例和生成报告。没有改题，没有修改共享定义，也没有把这两个改写的失败扩大为整个关系对接路线的否定。

##### 问题表

| 问题 | 精确位置 | 结论与档 |
|---|---|---|
| 本构造子逐行搬运中的 Low 方向 | `YiFMMap.mapᴴ` 的第一个前提 | 本引理使用 `Low₁ → Low₀`，编译定理；未证明不存在采用别种方法的协变映射 |
| 新读法是否仍是旧族的指定自然数读法 | `YiFMFin.p²`，即 fn 2 的顶槽 | 新字段接受 []、旧字段要求 natT 1；直接字段映射被否定，编译定理 |
| mc 能否吸收第一个较小余尾 | `YiFMNode.regular-back` | 正规 Ω 叶可以；这说明字段差别不能直接当成关系不等价，编译定理 |
| 非叶结点能否同样吸收 | `YiFMNode.node-new` 的旧族对应 | 新族闭实例已交；旧族推导未走通；没有值上的否定 |
| 仅抬内层是否可重建旧 mΩ | `YiFMNode.no-inner↑-slot` | 共尾度变为 cω，排除这个指定改写，编译定理 |
| 同时抬两层后能否用 mc 搬原分支 | `YiFMNode.no-both↑-branch-mc` | 对一切 η，所需项序方向不成立，排除这个指定的一步 mc 改写，编译定理 |

不把这些问题归到 W、V、C 或已知壁垒：本路只检查了验收关系中的生成字段和指定项序，不涉及一般高层派发、判定或值序。

#### 2. 文件、冷编和全部产物

全部仓库源码均在 `probes/OCF/Lean/`，只新建 YiFM 前缀文件。行数按 Agda 代码块内物理行计算，包含导入及空行；另列非空代码行，不与定义级切片行数混用。内存取每份冷编日志的 RTS `maximum residency` 与 `total memory in use`，不是操作系统 RSS。各次均为一个 Agda、`-M5G`，依赖使用现有接口。

| 文件 | 代码行 / 非空代码行 | 全文行 | 冷编退出码 | RTS 最大驻留 bytes | RTS 总内存 MiB |
|---|---:|---:|---:|---:|---:|
| `probes/OCF/Lean/YiFMMap.lagda.md` | 22 / 21 | 28 | 0 | 1,041,123,720 | 1819 |
| `probes/OCF/Lean/YiFMFin.lagda.md` | 83 / 68 | 89 | 0 | 1,375,495,920 | 2275 |
| `probes/OCF/Lean/YiFMNode.lagda.md` | 76 / 60 | 83 | 0 | 1,435,270,376 | 2346 |

三份冷编日志各只有自身模块的一条 `Checking`；未出现重新检查共享依赖的 `Checking`。依次删除的接口只有：

```
probes/_build/2.8.0.2/agda/OCF/Lean/YiFMMap.agdai
probes/_build/2.8.0.2/agda/OCF/Lean/YiFMFin.agdai
probes/_build/2.8.0.2/agda/OCF/Lean/YiFMNode.agdai
```

仓库源码的禁用构造、洞、禁用选项与本机路径联合检索为 0；头部行数依次为 4、4、5。未使用 Funext。审计范围恰为这三份新增源码，没有把该结果扩大成对整个导入闭包的重新安全审计。

私有实验目录：`<实验目录>`。库文件为其中 `libraries`，两行路径按简报创建。没有使用其他实验目录。完整回报为 `<回报原文>`。

##### 全部编译日志与直接取得的退出码

| 日志（均在私有实验目录） | 退出码 | 内容 |
|---|---:|---|
| `YiFMMin.log` | 0 | 第 0 步的首层双向与 Ω 树往返实例 |
| `YiFMFin.log` | 42 | 正式有限层文件首轮，`rd-one-zero` 中未指定的 μ 导致未解隐参 |
| `YiFMFin-fixed.log` | 0 | 将 μ=natT 1 与 ν=[] 显式写出后通过 |
| `YiFMFin-shared-map.log` | 0 | 首层两向改为共用 mapᴴ 后通过，陈述未变 |
| `YiFMNodeMin.log` | 0 | 非叶探针的最小新族实例 |
| `YiFMNode.log` | 0 | 非叶探针、正规叶吸收、两种改写的精确否定 |
| `YiFMRedesignInner.log` | 42 | 第一改写的最小共尾度检查，cω != cΩ (natT 1) |
| `YiFMRedesignBoth.log` | 42 | 第二改写的一步 mc 分支搬运检查，两个 ψ 下标不一致 |
| `YiFMMap-cold.log` | 0 | 删除自身接口后冷编，仅本模块 Checking |
| `YiFMFin-cold.log` | 0 | 删除自身接口后冷编，仅本模块 Checking |
| `YiFMNode-cold.log` | 0 | 删除自身接口后冷编，仅本模块 Checking |
| `YiFMRegularCheck.log` | 0 | 为 regular-back 的分支前提提供可满足实例 |

退出码均直接来自工具返回的 Agda 进程状态，没有经过管道；所有 Agda 输出先落文件。42 的首行均不是 LibraryError。没有 251、124、154。

##### 临时源码与辅助文件

纯 Agda 临时源码全部如下；失败的两份保留原样，供复核工程失败的位置，不应作为可导入成果：

- `YiFMMin.agda`：第 0 步。
- `YiFMNodeMin.agda`：非叶新族闭实例先验检查。
- `YiFMRedesignInner.agda`：第一改写，预期被检查器拒绝的断言。
- `YiFMRedesignBoth.agda`：第二改写，未走通的一步 mc。
- `YiFMRegularCheck.agda`：正规叶吸收前提的具体实例。

脚本与元数据：`audit.py`、`report.py`、`audit.json`、`audit-output.json`、`libraries`。成功临时模块的接口为 `YiFMMin.agdai`、`YiFMNodeMin.agdai`、`YiFMRegularCheck.agdai`。除此之外的临时文件就是上表列明的 12 份日志。完整目录清单附在报告末尾。

#### 3. 定理与构造表

以下签名按源码逐字提取；表格中只合并换行空白，未增减参数。保留换行的签名原文附在本节后。`YiFMFin` 的 F 是 `YiHCFam`，G 是 `YiGIRel`；`YiFMNode` 的 HF 是 `YiHCFam`，G 是 `YiGIRel`。所有表内定理都已冷编；标为“闭构造”的行只交构造和类型，不把它当成序数值定理。

##### YiFMMap

| 名字 | 逐字签名（合并换行） | 白话 | 档 |
|---|---|---|---|
| `mapᴴ` | `mapᴴ : ∀ {S : Sg} {Low₀ Low₁ : (p : P S) → E.T → B S p → Set} {Ch₀ Ch₁ : (c : C S) → E.T → D S c → Set} {Nu₀ Nu₁ : P S → E.T → Set} → (∀ p {η c} → Low₁ p η c → Low₀ p η c) → (∀ c {s y} → Ch₀ c s y → Ch₁ c s y) → (∀ p {ν} → Nu₀ p ν → Nu₁ p ν) → ∀ {t x} → Mᴴ S Low₀ Ch₀ Nu₀ t x → Mᴴ S Low₁ Ch₁ Nu₁ t x` | 槽位分支关系逆向、孩子关系与余尾字段正向时，搬运遗传封闭关系的推导。 | 编译定理 |

签名原文：

```agda
mapᴴ : ∀ {S : Sg}
  {Low₀ Low₁ : (p : P S) → E.T → B S p → Set}
  {Ch₀ Ch₁ : (c : C S) → E.T → D S c → Set}
  {Nu₀ Nu₁ : P S → E.T → Set}
  → (∀ p {η c} → Low₁ p η c → Low₀ p η c)
  → (∀ c {s y} → Ch₀ c s y → Ch₁ c s y)
  → (∀ p {ν} → Nu₀ p ν → Nu₁ p ν)
  → ∀ {t x} → Mᴴ S Low₀ Ch₀ Nu₀ t x → Mᴴ S Low₁ Ch₁ Nu₁ t x
```

##### YiFMFin

| 名字 | 逐字签名（合并换行） | 白话 | 档 |
|---|---|---|---|
| `fω₁≢[]` | `fω₁≢[] : ∀ {t} (v : Vω t) → fω v 1 ≡ [] → ⊥` | 任何共尾度为 ℕ 的参照项，其第 1 个视图基本列项都不是空项。 | 编译定理 |
| `rd-zero` | `rd-zero : ∀ {ν} → G.Rd zero ν → ν ≡ []` | 零层的所有新读法推导只能读出空项。 | 编译定理 |
| `old-new¹` | `old-new¹ : ∀ {s x} → F.M 1 s x → G.R (fn 1) s x` | 第 1 层旧族到新族，对任意参照项与任意该层树成立。 | 编译定理 |
| `new-old¹` | `new-old¹ : ∀ {s x} → G.R (fn 1) s x → F.M 1 s x` | 第 1 层新族到旧族，对任意参照项与任意该层树成立。 | 编译定理 |
| `old-leaf¹` | `old-leaf¹ : F.M 1 (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))` | 第 1 层的 Ω 树具有旧族的标准叶推导。 | 编译定理 |
| `new-leaf¹` | `new-leaf¹ : G.R (fn 1) (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))` | 同一 Ω 树的旧推导搬到新族。 | 编译定理 |
| `back-leaf¹` | `back-leaf¹ : F.M 1 (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))` | 同一 Ω 树的新推导再搬回旧族。 | 编译定理 |
| `low-back²` | `low-back² : ∀ p {η c} → G.Low (fn 2) p η c → F.LwP 2 p η c` | 第 2 层全部槽位的分支关系从新族搬回旧族。 | 编译定理 |
| `nu-forward²` | `nu-forward² : ∀ p {ν} → Nw 1 p ν → G.Nu (fn 2) p ν` | 第 2 层旧族的指定余尾读法进入新族读法。 | 编译定理 |
| `old-new²` | `old-new² : ∀ {s x} → F.M 2 s x → G.R (fn 2) s x` | 第 2 层旧族到新族，对任意参照项与任意该层树成立。 | 编译定理 |
| `p²` | `p² : Pos (fn 2)` | 第 2 层指向第 1 层本身的顶槽，作为差别的具体位置。 | 闭构造 |
| `rd-one-zero` | `rd-one-zero : G.Rd (fn 1) []` | 第 1 层的新读法接受空项；证明明确使用向下封闭 cc。 | 编译定理 |
| `nu-new²` | `nu-new² : G.Nu (fn 2) p² []` | 第 2 层顶槽的新余尾字段接受空项。 | 编译定理 |
| `nu-old²-empty` | `nu-old²-empty : Nw 1 p² [] → ⊥` | 同一顶槽的旧余尾字段不接受空项。 | 编译定理 |
| `no-direct-nu-back²` | `no-direct-nu-back² : (∀ {ν} → G.Nu (fn 2) p² ν → Nw 1 p² ν) → ⊥` | 不存在保持余尾下标不变的全称字段反向搬运函数。 | 编译定理 |

签名原文：

```agda
fω₁≢[] : ∀ {t} (v : Vω t) → fω v 1 ≡ [] → ⊥

rd-zero : ∀ {ν} → G.Rd zero ν → ν ≡ []

old-new¹ : ∀ {s x} → F.M 1 s x → G.R (fn 1) s x

new-old¹ : ∀ {s x} → G.R (fn 1) s x → F.M 1 s x

old-leaf¹ : F.M 1 (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))

new-leaf¹ : G.R (fn 1) (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))

back-leaf¹ : F.M 1 (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))

low-back² : ∀ p {η c} → G.Low (fn 2) p η c → F.LwP 2 p η c

nu-forward² : ∀ p {ν} → Nw 1 p ν → G.Nu (fn 2) p ν

old-new² : ∀ {s x} → F.M 2 s x → G.R (fn 2) s x

p² : Pos (fn 2)

rd-one-zero : G.Rd (fn 1) []

nu-new² : G.Nu (fn 2) p² []

nu-old²-empty : Nw 1 p² [] → ⊥

no-direct-nu-back² : (∀ {ν} → G.Nu (fn 2) p² ν → Nw 1 p² ν) → ⊥
```

##### YiFMNode

| 名字 | 逐字签名（合并换行） | 白话 | 档 |
|---|---|---|---|
| `t` | `t : E.T` | 非叶探针的参照项：E.ψ (E.natT 1) (E.Ωt (E.natT 1)) ∷ []。 | 闭构造 |
| `fold¹` | `fold¹ : Tr (fn 1) → O.Tr⁺ (fn 1)` | 主线折叠在第 1 层折到自身，以该层 Ω 树起步。 | 闭构造 |
| `g` | `g : Tr (fn 1) → Tr (fn 2)` | 把上述折叠输出嵌入第 2 层，作为结点分支。 | 闭构造 |
| `node⁺` | `node⁺ : O.Tr⁺ (fn 2)` | 顶槽 p² 上具有非零证书的闭树。 | 闭构造 |
| `at-g` | `at-g : ∀ η c → G.R (fn 1) η c → G.R (fn 2) (E.ψ (E.natT 1) η ∷ []) (g c)` | 分支上的新族推导，复用旧族 Self.PF 与首层双向转换。 | 编译定理 |
| `node-new` | `node-new : G.R (fn 2) t (proj₁ node⁺)` | 上述闭树在新族中对着非叶参照项 t；这是关系推导，不是序数值验收。 | 编译定理 |
| `regular-back` | `regular-back : ∀ {h : Tr (fn 1) → Tr (fn 2)} → (∀ η c → HF.M 1 η c → HF.M 2 η (h c)) → HF.M 2 (E.Ωt (E.natT 1)) (Ω p² h)` | 正规 Ω 叶的较小余尾可以先按较大槽位生成，再经 mc 向下吸收。 | 编译定理 |
| `inner↑` | `inner↑ : E.T` | 只把探针内层的 Ω 下标从 1 改为 2 的参照项。 | 闭构造 |
| `both↑` | `both↑ : E.T` | 把探针外层与内层的下标都改为 2 的参照项。 | 闭构造 |
| `cof-t` | `cof-t : E.cof t ≡ E.cΩ []` | 原探针共尾度是 cΩ []。 | 编译定理 |
| `cof-inner↑` | `cof-inner↑ : E.cof inner↑ ≡ E.cω` | 只抬内层后共尾度变成 cω。 | 编译定理 |
| `no-inner↑-slot` | `no-inner↑-slot : E.cof inner↑ ≡ E.cΩ (E.natT 1) → ⊥` | 只抬内层的项不能用于要求 cΩ (natT 1) 的旧顶槽。 | 编译定理 |
| `cof-both↑` | `cof-both↑ : E.cof both↑ ≡ E.cΩ (E.natT 1)` | 同时抬两层可以得到旧顶槽要求的共尾度。 | 编译定理 |
| `fsT-t` | `fsT-t : ∀ η → E.fsT t η ≡ E.ψ (E.natT 1) η ∷ []` | 原探针的 Ω 基本列逐项是第 1 层的 ψ 项。 | 编译定理 |
| `fsT-both↑` | `fsT-both↑ : ∀ η → E.fsT both↑ η ≡ E.ψ (E.natT 2) η ∷ []` | 同时抬两层后的 Ω 基本列逐项是第 2 层的 ψ 项。 | 编译定理 |
| `no-both↑-branch-mc` | `no-both↑-branch-mc : ∀ η → E.fsT both↑ η ≤ᵀ E.fsT t η → ⊥` | 新要求的分支项不在原分支项之下，所以不能用这一个 mc 搬过去。 | 编译定理 |

签名原文：

```agda
t : E.T

fold¹ : Tr (fn 1) → O.Tr⁺ (fn 1)

g : Tr (fn 1) → Tr (fn 2)

node⁺ : O.Tr⁺ (fn 2)

at-g : ∀ η c → G.R (fn 1) η c → G.R (fn 2) (E.ψ (E.natT 1) η ∷ []) (g c)

node-new : G.R (fn 2) t (proj₁ node⁺)

regular-back : ∀ {h : Tr (fn 1) → Tr (fn 2)}
  → (∀ η c → HF.M 1 η c → HF.M 2 η (h c))
  → HF.M 2 (E.Ωt (E.natT 1)) (Ω p² h)

inner↑ : E.T

both↑ : E.T

cof-t : E.cof t ≡ E.cΩ []

cof-inner↑ : E.cof inner↑ ≡ E.cω

no-inner↑-slot : E.cof inner↑ ≡ E.cΩ (E.natT 1) → ⊥

cof-both↑ : E.cof both↑ ≡ E.cΩ (E.natT 1)

fsT-t : ∀ η → E.fsT t η ≡ E.ψ (E.natT 1) η ∷ []

fsT-both↑ : ∀ η → E.fsT both↑ η ≡ E.ψ (E.natT 2) η ∷ []

no-both↑-branch-mc : ∀ η → E.fsT both↑ η ≤ᵀ E.fsT t η → ⊥
```

##### 前提可满足性与量化范围

- `mapᴴ`：取两边完全相同的 Low、Ch、Nu，三条证据函数均取恒等，即有平凡实例；正式文件中的首层两向及第二层旧到新是非平凡实填实例。
- `regular-back`：临时 `YiFMRegularCheck.premise` 取 `h c = proj₁ (upz tt (suc c , z◃ c ◃s))`，分支证明为 `mU mz (mwN 1 m ◃s)`；`instance-old` 对规范 Ω 树实例化，退出 0。
- `no-direct-nu-back²`：被否定函数的输入域有闭实例 `nu-new²`，不是由于新域为空而成立。
- `no-inner↑-slot` 与 `no-both↑-branch-mc` 没有额外侧前提；它们的唯一否定目标分别是写明的共尾等式与写明的项序不等式，不能要求再给该否定目标的实例。后者的 η 可任取，例如 []；它的结论是对所有 η 的编译否定。
- `old-new¹`、`new-old¹`、`old-new²` 没有标准形、出口或合法性附加前提，量化域就是签名写的所有该层树。

`node⁺` 的闭构造与 `node-new` 的关系推导分开交付。未为它交 `readRW` 的序数值下界或上界，也没有因此以“读法太低”关闭它。`node-new` 的记号项含第 1 层 ψ；这不是本路宣称的新强度，未得到任何新增 ψ₀(Ω_x) 主线强度界。

#### 4. 第一个障碍、两次改写与停止位置

第一个不能直接继续的关系引理是：

```agda
back² : ∀ {s x} → G.R (fn 2) s x → F.M 2 s x
```

这里 F 指 `YiHCFam`。该签名作为未完成目标写在报告中，没有在仓库文件中留下洞或假定。要用本路的构造子逐行搬运方法得到第三层的旧 ⇒ 新，顶槽的分支证据就会要求这个第二层反向转换。`mapᴴ` 不能只用正向的低层映射。

直接写 `back²` 的 mΩ 行时，新余尾推导可取 `nu-new² : G.Nu (fn 2) p² []`；旧行要求 `Nw 1 p² []`，即 [] ≡ natT 1。`no-direct-nu-back²` 编译地排除了这种保持构造子及余尾下标的字段搬法。它没有排除以不同推导重建同一关系结论。

正规叶情形已明确重建成功：`regular-back` 先用旧顶槽生成 Ω₂，再用 mc 向下到 Ω₁。这一成功实例是不能由 Nu 差别断言两族不等价的直接理由。

第一个保留下来的非叶探针是 `YiFMNode.t`，其新族实例 `node-new` 和带非零证书的闭项 `node⁺` 已编译。随后尝试的两次重设计都针对同一个 mΩ 重建问题：

1. 仅抬内层：把参照项改成 `inner↑`。需要它的共尾度是 cΩ (natT 1)，实际编译出 cω；`YiFMRedesignInner` 退出 42。正式的 `cof-inner↑` 和 `no-inner↑-slot` 证明了该指定改写的失败。
2. 同时抬内外层：改用 `both↑`，共尾度检查通过。但是分支要从原来的第 1 层 ψ 项搬到第 2 层 ψ 项，试图只用 mc；`YiFMRedesignBoth` 退出 42。正式 `no-both↑-branch-mc` 证明所需的不等式对每个 η 都不成立，所以这一指定的一步 mc 改写也被否定。

到此触发停止条件。没有继续构造第三种改写，没有把“抬高参照项”改成对树或折叠的修改，也没有绕过原顺序开始第 3 步。整个 `back²`、一般旧 ⇒ 新、两族关系等价与主线 LowKeep 均只记“未走通/未完成”，不记“已否定”。

建议（判断，未执行）：若作者续派，可把所需反向陈述先限制到规范 Ω 树，并与一般全树反向陈述区分；是否足以替代原第 3 步，需要另外核对 eboᵍ 实际消费的关系项。这里没有证明这一范围足够，也没有声称它是剩余唯一办法。

#### 5. 偏离、事故、阅读依据与交接

- 没有改已有源码、共享接口定义、导航、台账、留档、src 或 archive；没有提交、推送、安装软件、派子路、pkill、ignore-interfaces 或删除其他模块接口。对依赖只读取已有接口，未做依赖全冷编；主审应独立复核。
- 唯一工程性修正：`YiFMFin` 首轮失败于隐式 μ 未解，按手册明确写成 `{μ = E.natT 1}` 与 `{ν = []}` 后通过。不是数学反例，未计入两次重设计。
- 两次失败改写的临时文件故意保留其未通过的实质断言，没有洞。它们的 42 只作指定检查失败的工程事实；数学否定以正式模块的编译定理为据。
- 为减少同类证明重复，冻结前将首层两个七构造子递归转换改为调用共用 `mapᴴ`；签名未变。冻结后没有修改任何三份仓库源码，只做删自身接口冷编、审计与临时前提实例复核。
- 第 0 步是在临时文件中先检查后写一般参数搬运。非叶探针也是先在临时 `YiFMNodeMin` 编译后保存。正规叶吸收的分支前提先从已存在的 `YiHCFam.Mβ` 的证明正文确认可满足，最后另补了 `YiFMRegularCheck` 独立编译；该单独临时实例是在吸收引理写出之后补验，这一点没有计成先验文件检查。
- 已完整阅读：任务简报、AGENTS.md、EBOHandbook.md §4、YiGIRel、YiHCFam、YiHCRel、YiGICheck。其他文件只按签名和相关证明段检索，包括 YiCLFam、EboLeanBase/View/Def、YiRWBlock/Ops、YiLTFold 的 Self.PF 与末段 LFP/LFA、YiAbsGIface、YiGIInst、YiLTKid、YiLTLift；其中使用于新证明的具体依赖按类型检查通过，不宣称已独立冷编审计其全部证明。
- YiGIEnd.eboᵍ 的主审复核状态与 YiGI 历史回报来自简报背景，本路没有重新冷编它或凭此构造新值结论；没有读 YiGI 回报全文。YiPJ、YiNX 冻结源码可读但本路没有使用、没有依赖其结果；YiXV 同样没有使用。对这些文件没有作新的结论。
- 本路全部新增数学源码的档为验收文件；未做记号无关性切片，不把导入记号的验收结果当作成品候选。

##### 冻结源码 SHA-256


- `probes/OCF/Lean/YiFMMap.lagda.md`：`cb3380410d61e4b751b75b7a16c9fde0f24a2a77c8582ce602f323ba98aaf240`
- `probes/OCF/Lean/YiFMFin.lagda.md`：`7f3f2e36bbc48efdaa36cea3326b05e21a9591165813ae833730acac67ec35cb`
- `probes/OCF/Lean/YiFMNode.lagda.md`：`d4e33c6ea028e343675fa2915b41e6d9b9d33e62f72cc10523a7826638d151c4`

##### 私有实验目录最终文件清单

```
YiFMFin-cold.log
YiFMFin-fixed.log
YiFMFin-shared-map.log
YiFMFin.log
YiFMMap-cold.log
YiFMMin.agda
YiFMMin.agdai
YiFMMin.log
YiFMNode-cold.log
YiFMNode.log
YiFMNodeMin.agda
YiFMNodeMin.agdai
YiFMNodeMin.log
YiFMRedesignBoth.agda
YiFMRedesignBoth.log
YiFMRedesignInner.agda
YiFMRedesignInner.log
YiFMRegularCheck.agda
YiFMRegularCheck.agdai
YiFMRegularCheck.log
audit-output.json
audit.json
audit.py
libraries
report.py
```
