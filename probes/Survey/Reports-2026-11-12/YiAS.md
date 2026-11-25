# 不同步引理：接口与构造 (YiAS)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 05:39 至 05:56 |
| 工具调用 / agda 编译 (粗数) | 39 / 8 |
| token (usage 字段，按消息去重) | 输出 96173；新写入缓存的输入 265065；读缓存的输入 5600299；其余输入 70 |
| 写过的仓库文件 | `YiASIface.lagda.md`, `YiASProofLow.lagda.md`, `YiASProofMin.lagda.md`, `YiASProofPair.lagda.md` |
| 文件前缀 | `YiAS` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 不同步引理构造一路返回并复核; 第三十六批全部返回 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 有限层号上 LowKeep 在具体块 (gradedᴬ) 上实填 (lowKeepᶠ, 经 LFᶠ: 主线折叠折到任一真子层号保持关系), 不同步版 lowKeepAsyncᶠ 是其特例, 非平凡对 pair₁ 上成立 (low₁); 参照 ψ₂(P+Ω₂) 的一例成立 (async₀⁺); 障碍移到 Leaf: 松弛对不在关系 M 里 (no-Ω₁, no-Ω₂), 读法零、后继两条与 Leaf 在 M 上不相容 (no-leaf); 下一步在验收一侧 (关系对参照向下封闭, 或 Leaf 只对字面相等的读法); 五件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方，"构造" 一路。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-14，选项原文）
- 战略："(c) 中间形态 (Recommended)"：保留主线的树、层号、运算、路径与共用的七列行，只把 "经指定孩子" 那一行换成换基。
- 脉络："FGH → BTBO → 更高层 (Recommended)"。
- 第一批："(1) 不同步引理 + 配对否定 (Recommended)"，模型 "(1) Fable 5.2"。选项说明原文："有限层号、现有折叠、不改定义：参照保留而树走对角时保持是否成立（最小实例第 3 层折到第 2 层、参照 Ω₁）；另一路对同一接口写否定"。
- 作者此前定的判断标准（原话）："折叠是FGH在更高层次的推广, 既然是推广, 必然要有新的东西, 但又要尽可能顺着原来的脉络. 顺着原来的脉络看, 看是否自然, 这就是判断何为好的推广, 正确的推广的判断标准."

同批另一路是 "否定" 一路，前缀 `YiASNeg`，对你写的接口文件陈述否定。你不动它的文件。

###### 要做的
**第一件，20 分钟内写出并编译共用的接口文件** `probes/OCF/Lean/YiASIface.lagda.md`。这个文件定稿后只增不改，另一路会导入它。只放陈述（`Set`）与必要的定义，不放证明。内容：
1. **"不同步对" 的谓词**：参照项的余尾 Ω 下标低于目标层（记号一侧保留结点），而树一侧对应的槽位不低于目标层（走对角，输出是 ℕ 极限）。
   - 在分级接口 `YiAbsGIface` 的语言里写，量化域作参数；
   - 并给出有限层号实例（`YiAbsGFin` 的 `blkᶠ`/`foldᶠ`/`gradedᶠ`，关系是 `YiANFam.M`）上的具体版本。
2. **两条陈述**：
   - `LowKeepAsync`：`YiAbsGIface.LowKeep` 限制到不同步对；
   - **最小实例** `Async₀`：参照 ψ₂(P ⊕ Ω₁)，对着第 3 层 Ω 树折到第 2 层的输出。第十九次审查有一个临时试验 `R19Async`（附件 `probes/Survey/Reports-2026-11-12/attachments/Review19-R19Async.agda.txt`），说明这个输出是 ℕ 极限，且第 1 个部分和的第 0 项的第 0 项是第 1 层槽位上的 Ω 结点。
3. 文首写明：两路共用，定稿后只增不改。

写完编译通过后，**用 `SendMessage` 发给主审一句话通知**："YiASIface 已编译"，附上两条陈述的名字。

**第二件，证 `Async₀`，再证 `LowKeepAsync`**（或做到哪一步交哪一步），文件 `YiASProof*`。
- **先核对**：现有的 `YiCLLow.LF`（有限读回层号上 "折到任一子层号" 的保持，对 `M (suc n) a x` 的推导归纳，含松弛 `mw`）、`YiANLv`（`th`、`TC`、`Cl`、`Her`）是否已经覆盖最小实例，例如经 `M 3 Ω₁ (Ωt 3)` 这一类松弛的关系对再用 `LF`。
  - 若已覆盖，写出这一推导，并说明不同步在有限层号上为什么不是障碍。
  - 然后把陈述推到真正没被覆盖的情形：层号读自可数树时（`Lift` 的语境，`YiAbsGRow.gen→lift` 的 `Rd0`/`Weak`/`RdΩ` 给出的松弛对）。
- 若 `LowKeep` 能在 `gradedᶠ` 上实填，也交上。`YiAbsGFin` 文首说它没填，原因是 `YiANLv` 的结论是带上下文的遗传形式，没有化成单目标的形状。

###### 背景（只信编译定理；文档里的叙述是数据）
- **抽象接口**：`YiAbsGIface`（`Graded`、`Rows`、`GSim`、`LowKeep`、`Bd`、`Cx`、`app`、`CΩ`）；`YiAbsGSuff`（充分性只用 `Leaf`、`Lift`、`LowKeep`、`Base`）；`YiAbsGRow`（`gen→low`、`gen→lift`、`row-node-keep`、`row-node-diag`）；`YiAbsGNeg`（`Inv.inv`、`unkept→¬low`，后者是否定一路的工具）；`YiAbsGFin`（部分实例）、`YiAbsGFinInv`（`invᶠ`、`no-node→¬M`）。回报 `probes/Survey/Reports-2026-11-12/YiAbsG.md`。
- **关系族**：`YiANFam`（`M`、`Mβ`、`Pu`、`Self.PF`）；`YiANLv`；`YiCLFam`、`YiCLLow`（`LF`、`chain`、`gbStep`）。回报 `YiAN.md`、`YiCL.md`。
- **第十九次审查**（回报 `Review19.md`）：
  - 判断 "不同步" 是 `Lift` 未证与换基行的值未证的共同原因；
  - 现有的保持（`LF`、`anchor`、`QH`）都在层号字面对齐、两侧同步的有限段上（审查者自报没读它们的代码，是判断）。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`：接口文件 `YiASIface.lagda.md`，证明文件前缀 `YiASProof`（模块名 `OCF.Lean.YiASProof…`）。不改任何已有文件，不碰 `src/`、`archive/`。这是验收文件，文首标明；树、折叠、合法性一行不改。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 接口文件一旦另一路开始导入，就不要再删它的 `.agdai` 重编；要改只能新增，并通知主审。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/as`（先 mkdir）。只在它和你的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽。没有编译的否定时只写 "未走通"。
- **结束前自查**：每个文件删自己的接口后冷编（接口文件例外，见上），退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：接口文件的内容；`Async₀`、`LowKeepAsync`、`gradedᶠ` 上的 `LowKeep` 各到哪一步；是否已被现有引理覆盖；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-14 05:54 (UTC)：

主审转告：否定一路 `probes/OCF/Lean/YiASNeg.lagda.md` 已返回，主审冷编复核过，退出码 0。以下是编译过的事实。你的目标改为下面写的；简报的其余部分不变。

**已被编译否定，不要再证：**
- `¬pair₀ : Pair₀ → ⊥`：第 3 层 Ω 树与 Ω₁ 没有 `M` 关系，即 `¬M₀ : M 3 (Ωᴺ 1) (Ωt (fin 3)) → ⊥`。原因是 `Ωt (fin 3)` 沿第一位置序与孩子都不含槽位层 0 的结点。
- `¬async₀ᶜ : Async₀ᶜ → ⊥` 与 `¬async₀ : Async₀ → ⊥`。
  - 原因：`out₀` 说明对角输出不新造结点；`async₀-needs` 说明结论要求 β 或底的第 2 层分量含槽位层 0 的结点；而标准底、β 取第 2 层 Ω 树、P 为空时两者都不含。
  - 前提在这一例上可满足（`gb₀`）。
- 否定一路的判断：`Async₀` 对一切满足 `GBᶠ` 的底与一切 β 量化，量化域过宽。

**没有被否定，仍然开放：**
- `LowKeepAsyncᶠ`。否定一路证明了在这个工具下否定不可得：
  - `async-kept`：任何有 `M` 关系的不同步对，输出含余尾下标那一层槽位的结点；
  - `no-unkept`：任何满足三条封闭条件的 H 都在输出上成立。
- 两条归约用的定理：
  - `async→weak`：不同步对的关系只能来自放宽，即存在 `x′ ◃ x` 且 `M n a x′`；
  - `async-step`：结论沿折叠单调从 x′ 传回 x。
- 否定一路的判断：`LowKeepAsyncᶠ` 归约到同一参照项在严格在下的树上的 `LowKeepᶠ`，不是独立的新律。
- 一个有关系、非平凡的不同步对：`pair₁ : AsyncPairᶠ {n = 3} 2 (Ωᴺ 1) x₁`、`M₁ : M 3 (Ωᴺ 1) x₁`，其中 x₁ 是第 3 层 Ω 树左加搬上来的 Ω₁ 树；`kept₁` 说明它的输出含第 0 层槽位的结点。

**建议的目标：**
- 证 `LowKeepAsyncᶠ`，或者经 `async→weak` 与 `async-step` 归约到 `LowKeepᶠ` 再证 `LowKeepᶠ`；
- 至少交非平凡实例 `pair₁` 上的结论：`M 2 (ψᴺ 2 (t₀ ++ Ωᴺ 1)) (ψs … x₁)` 一类。
- 接口 `YiASIface` 可以在文末追加新的陈述（例如 `pair₁` 一例的陈述），但不改已有内容、不删它的 `.agdai`。若追加，通知主审。

`YiASNeg` 的名字可以直接导入使用。

转录时间戳 2026-11-14 05:55 (UTC)：

主审转告作者刚定的原则（作者原话，属作者指令）：

"但是我觉得不管怎样, 不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"

对你的影响：
- 你的目标是 `LowKeepAsyncᶠ`、`LowKeepᶠ`、`pair₁` 一例，都在验收一侧，符合这条，照常做。
- 若证不下去，出路只能在验收一侧找：调整关系 `M`、参照系统，或者补记号一侧的外部定理。否定一路的判断是 "`M` 对参照一侧不向下封闭"，例如可以借记号一侧的基本列支配性质，让关系对参照向下封闭。
- 不要以 "让树与记号同步" 为理由，提议改树、折叠或合法性的定义。
- 回报里若写到 "下一步"，按这条原则分清：哪些是验收一侧的出路，哪些（若有）是树侧自身要求逼出的定义改动。

## 回报原文

#### 构造一路回报 (YiAS, 2026-11-14)

##### 1. 判决

**对纲领与目标的意义.** 有限层号、主线折叠、不改任何定义的前提下, "不同步" 不是 `LowKeep` 的障碍: `LowKeep` 在关系 `M` 上对一切有关系的对成立 (编译, 无前提), 不同步对是它的特例. 障碍在别处: 第十九次审查设想的松弛对 (Ω_m 对着第 n 层 Ω 树, m < n) 根本不在 `M` 里, 所以 `Leaf` 在松弛的读法下先失败 (`no-leaf`, 编译). 按作者刚定的原则, 这一条的出路在验收一侧 (关系或参照系统), 不构成改树、折叠、合法性的理由. 全部是验收文件, 读记号, 不算 "树自足".

**各项到哪一步.**
- `LowKeepᶠ` (即 `gradedᴬ` 上实填 `LowKeep`): **已证**, `lowKeepᶠ`. 路径含 `self`. 注意这是 `gradedᴬ`, 不是 `gradedᶠ`: `gradedᶠ` 的 `Bd` 是空, `LowKeep` 在它上面空真; 我在接口里另取了上下文是前缀 t₀、`Bd` 是 `GBᶠ` 的实例.
- `LowKeepAsyncᶠ`: **已证**, `lowKeepAsyncᶠ`, 是 `lowKeepᶠ` 丢掉不同步对那个参数.
- `pair₁` 一例: **已证**, `low₁` 与闭的 `low₁ᶜ` (经接口上的 `lowKeepAsyncᶠ` 取得, 导入了 `YiASNeg` 的 `x₁`, `M₁`, `pair₁`).
- `Async₀`, `Async₀ᶜ`, `Pair₀`: 按字面不成立, 否定一路已编译, 我不重证. (我在收到通知前独立写过 `¬Pair₀` 并编译通过, 已删; `¬async₀` 一版只写到作用域错误就按通知撤掉了, 没有编译过.)
- 参照改取 ψ₂(P + Ω₂) 的一例: **已证**, `async₀⁺`, `async₀⁺ᶜ`. 这是审查的 `R19Async` 实际看到的东西: 那个 "第 1 层槽位上的结点" 的分支在第 1 层, 对应余尾下标 1, 即 Ω₂ 的余尾, 不是 Ω₁. 这一对 (Ω₂, 第 3 层 Ω 树) 同样不在 `M` 里 (`no-Ω₂`), 但结论成立.

**是否已被现有引理覆盖.** 没有字面覆盖: `YiCLLow.LF` 在候选 A 的块上 (`YiRWBlock`/`YiKVFold`, 层号 `fn n`, 关系是 `YiCLFam.M`), 而 `gradedᶠ` 是主线块 (`YiLegBlock`/`YiLegFold`, `fin n`, `YiANFam.M`), 两族关系不同. `YiANLv` 在主线块上, 但结论是带上下文的遗传形式. 我把 `LF` 的证明逐情形搬到主线块上 (`LFᶠ`), 一次编译通过; 两个块在有限层号上的折叠同形.

**不同步在有限层号上为什么不是障碍.** `M` 的结点规则 `mΩ` 要求槽位层恰等于余尾下标 (`Nw`), 所以头部不同步的对只能来自放宽 `mw` (否定一路的 `async→weak` 是这条的编译陈述). `LFᶠ` 对推导归纳, `mw` 一步用折叠的单调性, 内部那个同步的结点照常保留.

**问题表.**

| 问题 | 位置 | 档 |
|---|---|---|
| 松弛对 (Ω₁, 第 n+2 层 Ω 树) 不在 `M` 里; 读法的零、后继两条与 `Leaf` 在 `M` 上不能同时成立 | `YiASProofPair.no-Ω₁`, `no-leaf` | 编译 |
| `Lift` 的语境 (层号读自可数树, `gen→lift` 的松弛对) 没有做: 按上一行, 在 `M` 上它在 `Leaf` 处已不成立, 不到 `LowKeep` | 无 | 判断 (由 `no-leaf` 推到 `Lift` 语境这一步是判断) |
| `M` 对参照一侧不向下封闭; `async₀⁺` 是一个不在 `M` 里而结论成立的对 | `no-Ω₂` 加 `async₀⁺` | 两条各自编译; "所以该让关系向下封闭" 是判断 |
| `LFᶠ` 只到后继形状的有限层号, 不含 ℕ 极限与 Ω 形状层号 | `YiASProofLow` | 范围 |
| 接口里 `Async₀` 的参照取 Ω₁ 是我按简报字面写的, 与 `R19Async` 的观察对不上 | `YiASIface.Async₀` | 已由否定一路判决 |

**下一步 (按作者原则分开).** 验收一侧: 让关系对参照向下封闭 (借记号一侧基本列的支配性质), 或把 `Leaf` 的陈述改成只对读法字面相等的对; 然后再看 `Lift`. 树侧自身要求逼出的定义改动: 这一轮没有.

##### 2. 文件表

| 文件 | 代码行 | 冷编退出码 | 内存 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiASIface.lagda.md` | 79 | 0 (未带 `-s` 统计; 定稿后未删接口重编) | 未测 |
| `<仓库>/probes/OCF/Lean/YiASProofLow.lagda.md` | 196 | 0 | 2102 MiB |
| `<仓库>/probes/OCF/Lean/YiASProofPair.lagda.md` | 97 | 0 | 1978 MiB |
| `<仓库>/probes/OCF/Lean/YiASProofMin.lagda.md` | 34 | 0 | 2171 MiB |

三个证明文件删自己的接口后冷编, 日志里各只有自己模块一行 `Checking`. 禁用构造与本机路径检索为 0. 日志在 `<实验目录>/agents/as/`.

##### 3. 定理表 (全部是编译定理, 无前提)

| 名字 | 陈述 (逐字) | 白话 | 文件 |
|---|---|---|---|
| `LFᶠ` | `∀ {n j} (s : Sbᶠ n j) (t₀ : E.T) (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (B : Base (fin (suc n))) → GBᶠ n B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β → ∀ {a x} → M (suc n) a x → M j (ψᴺ j (t₀ ++ a)) (ψs (fin (suc n)) ε ρ B (fin j) (ins (pthᶠ s)) β nβ x)` | 主线折叠折到任一真子层号保持 `M`, 对一切推导 | ProofLow |
| `lowKeepᶠ` | `LowKeepᶠ` (= `Laws.LowKeep gradedᴬ domsᴬ`) | 接口的 `LowKeep` 实填 | ProofLow |
| `lowKeepAsyncᶠ` | `LowKeepAsyncᶠ` (= `Async.LowKeepAsync gradedᴬ domsᴬ cutᶠ`) | 限制到不同步对 | ProofLow |
| `Slot.inv` | `∀ n {s o} → M n s o → cof s ≡ cΩ κ → H n o` | 余尾下标 κ 的项只对着一阶位置可达处有槽位层恰为 κ 的结点的树 | ProofPair |
| `Slot.no-rel` | `∀ n {s o} → cof s ≡ cΩ κ → clean n o → M n s o → ⊥` | 碰不到这种结点就没有关系 | ProofPair |
| `no-Ω₁` | `∀ n → M (suc (suc n)) (Ωᴺ 1) (Ωt (fin (suc (suc n)))) → ⊥` | Ω₁ 与第 n+2 层 Ω 树无关系 (n = 1 与 `YiASNeg.¬M₀` 重合) | ProofPair |
| `no-Ω₂` | `M 3 (Ωᴺ 2) (Ωt (fin 3)) → ⊥` | Ω₂ 与第 3 层 Ω 树无关系 | ProofPair |
| `no-leaf` | `(Rd : ℕ → E.T → Set) → Laws.Rd0 (gradedᴿ Rd) domsᴬ → Laws.RdS (gradedᴿ Rd) domsᴬ → Laws.Leaf (gradedᴿ Rd) domsᴬ → ⊥` | 关系取 `M` 时, 读法的零、后继两条与 `Leaf` 不相容 | ProofPair |
| `async₀⁺` | `(ε : Ev (fin 3)) (ρ : Rt (fin 3)) (B : Base (fin 3)) (P : E.T) → GBᶠ 2 B P → (β : Tr (fin 2)) (nβ : fin 2 ⊢ zero ◃ β) → M 2 (ψᴺ 2 P) β → M 2 (ψᴺ 2 (P ++ Ωᴺ 2)) (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ (Ωt (fin 3)))` | 参照 ψ₂(P+Ω₂) (保留) 对着第 3 层 Ω 树折到第 2 层 (对角) 成立 | ProofPair |
| `gbᶜ` | `∀ n → GBᶠ n (B₀ (fin (suc n))) []` | 标准底满足底的条件, 各定理前提可满足 | ProofMin |
| `low₁` | `(ε : Ev (fin 3)) (ρ : Rt (fin 3)) (B : Base (fin 3)) (t₀ : E.T) → GBᶠ 2 B t₀ → (β : Tr (fin 2)) (nβ : fin 2 ⊢ zero ◃ β) → M 2 (ψᴺ 2 t₀) β → M 2 (ψᴺ 2 (t₀ ++ Ωᴺ 1)) (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ x₁)` | 否定一路的非平凡不同步对上结论成立 | ProofMin |
| `low₁ᶜ`, `async₀⁺ᶜ` | 上两条在 `B₀ (fin 3)`, 前缀 `[]`, 底值 `Ωt (fin 2)` 处的闭实例 | 闭的一例 | ProofMin |

`no-leaf` 的三个前提: 两条读法单独可满足 (`Rd n ν` 取 "ν 是不超过 n 的自然数", 这一实例我没有写成代码, 是纸面说明); `Leaf` 单独可满足 (`YiAbsGFin.leafᶠ`).

接口文件的内容: 抽象的 `Async.Cut`, `Async.AsyncPair`, `Async.LowKeepAsync`; 有限层号的 `Sbᶠ`, `pthᶠ`, `GBᶠ`, `gradedᴬ`, `domsᴬ`, `cutᶠ`, `AsyncPairᶠ`; 陈述 `LowKeepᶠ`, `LowKeepAsyncᶠ`, `Async₀`, `Async₀ᶜ`, `Pair₀`. 定稿后没有追加.

##### 4. 第一个障碍

`Laws.Leaf` 在松弛读法下, 精确到 `no-Ω₁ 0 : M 2 (Ωᴺ 1) (Ωt (fin 2)) → ⊥`: `Rd0` 加 `RdS` 给出 `Rd 2 (natT 1)`, `Leaf` 就要这一对有关系. 机制是 `mΩ` 的 `Nw` 要求槽位层与余尾下标字面相等.

##### 5. 偏离与事故; 没有读的东西

- 接口没用 `gradedᶠ` 而另取 `gradedᴬ`, 理由见上.
- `Slot.inv` 第一版直接对 `M` 的推导递归, 停机检查不过; 改用 `YiAbsGFin.Ind.ind` 后通过 (一次重新设计).
- 三次 agda 调用被系统挪到后台, 我等它结束再跑下一个, 没有并行两个 agda.
- `YiASProofPair` 里的 `Slot` 与否定一路的 `Has`/`async-kept` 功能有重叠, 是各自独立写的, 没有合并.
- 没有读、只凭转述: `YiANLv` 只读了文首、`Th` 表与 `Anchor`, 没读证明主体; `YiAbsGSuff`, `YiAbsGToy`, 回报 `YiAbsG.md`, `YiAN.md`, `YiCL.md` 没读; `YiASNeg` 只检索了签名, 它的 `async-kept`, `no-unkept`, `out₀`, `async₀-needs` 是按主审转述引用的; `E.Ωt`, `natT` 的定义是从归档文件与能否通过类型检查推断的.
