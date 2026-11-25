# E 路：换基候选的独立审查（先读定义，后读结论）（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 03:57 至 04:08 |
| 工具调用 / agda 编译 (粗数) | 23 / 2 |
| token (usage 字段，按消息去重) | 输出 56337；新写入缓存的输入 179350；读缓存的输入 2624832；其余输入 46 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `AuditE` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审核封存哈希一致（81b1231c…，UTC 2026-11-17T04:03:01Z）；两个判定件主审 8G 冷编退出 0（附件 attachments/AuditE-*.txt）；换基方向对路但保留判定 kp 原样导入，塔第 2 项顶结点的下标槽位低于目标仍走链（AuditEKeep.drop₂、chain₂）；Schema 自己给出保留路径（AuditEKeepFix.keepS）；漏记的缺口还有 seen 内部用 rb-no、替身单调只对不含 Ω 形状的偏移；不建议现在换主线 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b77/AuditE.md`。先用 Read 工具完整读它，再逐条照做（含 "先读"、"第 1 步封存之前不要读"、"规则" 与 "回报" 各节）。只在简报指定的临时目录里写，不改仓库里任何文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### E 路回报：换基候选的独立审查（Fable 5.2）

#### 0. 对纲领与目标意味着什么

- 换基行不触壁垒，方向对：它不比较孩子 c 与 c′，只用层号字面的地板 `floor` 与路径复合（`split`）。在塔第 1 项那一格上，纸面上能承载需要的参照。
- 换基候选 `YiBSFold` 还不是 "低于目标保留" 的完整实现。它只改了 `up` 行，保留判定 `kp` 原样导入。塔第 2 项起，顶结点的槽位低于目标仍走链，这一条我编译了（`AuditEKeep.drop₂`、`chain₂`）。
- 现有换基值定理全在塔第 1 项（偏移不含 Ω 形状）。到 EBO 要过的是塔第 2 项以上，那里另有两处没有记进 "剩下的三件"：上面这格，和替身内部用 `rb-no`。
- 对 "让树自足"：缺的那条保留路径由换基证据 `Schema` 自己给出（`AuditEKeepFix.keepS`，编译，不读记号）。这回答了 V291 "谁来给路径"。
- 没有新的值定理。不建议现在换主线。

#### 1. 第 1 步的封存

- SHA-256：`81b1231cbe1c7a0632279a7e02c6c5c8c03a39ce2a0787f49bc222b441305a5a`
- UTC：2026-11-17T04:03:01Z
- 文件：`<实验目录>/audit/E/plan.md`，封存后未改，回报前重算哈希一致。
- 封存前的越界：用 `grep` 查 `readRW` 时带出了 `YiKVRel` 文首判决段两行（讲 `Mᴰ`、`lower⁰`，不涉及换基）。其余只读了定义体。

计划全文：

```
# E 路第 1 步：只读定义后的判断（封存件）

读过的只有定义体：YiRWBlock, YiRWOps, YiRWPath, YiRWFold, YiTBRow, YiMTTab, YiBSBase, YiBSFold, YiRBSib (证据与 ψ 前几行), YiBSRead, YiSYReduce, YiSYDesc.Node, EboLeanDef, YiKVRel.readRW/M⁰/lower⁰, Value.≼。以下除标明处外全是纸面判断，没有编译。

## (a) 换基行在同步对象链步上做什么

- 换基只改一行：`YiBSFold.ψ (nd (sΩ k) h) o r B j (inc c′ v) β (up x c y e)`。有 `Schema`（h c ≡ floor ⊕ offsets c）时用 `route`（= `split`）把目标分成两支：`j ≤ floor` 时经 `back` 在原孩子 h c 上朝 j 折 y（不需要比较 c 与 c′，逐字保真）；`floor ≤ j` 时取 `seen S j … β c ⊞ ψ₀(y)`，其中 `seen` = 在层号 `j ⊕ offsets c` 上沿 `lift j (offsets c)` 朝 j 折 `Ωt (j ⊕ offsets c)`，底是 x 的折叠。y 只以折到第 0 层的尾项出现。
- 同步对象 `nd (sΩ zero) a₁`，`a₁ c = tw 1 ⊕ ↑(Ωt (h₁ c))`。顶层链 `feed` 走 `ink self`，是 `ink` 行，不碰这一格。碰到这一格的地方在孩子里面：折 `Ωt (a₁ z)` 时，偏移里的 Ω 形状结点下标层是 `h₁ m`（经 `OkO↑` 的 `posW k p ∙ v`，路径是经 tw 1 的孩子 m 的 `inc`），于是要把 `Ωt (tw 1) = Ω⁺ (inj₁ (inj₁ tt)) (λ c → upz c (Ωt (h₁ c)))` 朝 `j = h₁ c′` 折。这个结点被 `kp` 保留（`kp … (inj₁ t) (inc c v)`，v = self，h₁ c′ ≠ zero 时得 `just`），分支 z 上是 `up zero z (Ωt (h₁ z))`，目标经孩子 c′：就是这一行。
- 现行表（`tbᶻ`, `tb`）只在一方为零或两方都是字面自然数时有项，其余走 `β ⊞ ψ₀(y)`：每个分支是可数的，结点的值远低于 ψ_{c′}(Ω_{Ω₁})。换基行在 tw 1 的 Schema（floor = zero, offsets = ↑ zero，`rb-tw`）下给每个分支 ψ_j(Ω_{j ⊕ ↑z})，z 遍历 Tr zero，纸面上值不低于 ψ_{c′}(Ω_{Ω₁})（c′ = ω 的情形同）。判断：换基行在这一格上能承载需要的参照。
- 但把它变成编译下界需要 z ↦ `seen S j u β z` 对 z 的保持：链点 e 与参照 γ 只由关系 `M⁰ γ e` 相连，不是字面路径。字面前缀（z 到 suc z，f n 到 lim f）有 `inc` 路径，可望成立；对一般的值嵌入，`seen` 依赖 `↑ zero z` 的形状而不是 z 的值，这是跨层号的单调，我预计是主要难点。

## (b) 会不会在别处掉值；最危险处

1. **`kp` 那一格没有被换基修**（我认为最危险）。`YiBSFold` 原样导入 `YiRWFold.kp`，其中 `kp (nd (sΩ k) h) _ (inj₂ _) (inc _ _) = nothing` 仍在。`kp … (inj₁ t) (inc c′ v)` 用固定见证 `kh c′`（塔上是 `lift`，`psh` 走 `c₀`）把槽位推进孩子，目标路径 v 若在 offsets c′ 内部的 Ω 形状结点上走 `inc c″`，就落进这一格，得 `nothing`，结点改成可数链 `limc⁺`。tw 1 的偏移 `↑ zero c′` 没有 Ω 形状，不触发；tw 2 起偏移 `↑ (tw 1) c′` 有 Ω 形状，会触发，而此时槽位层 ≤ floor ≤ j，本该保留。Schema 自己就能给出修法：`route` 得 `floor ≤ j` 时用 `psh (index-floor ∙ u) t` 直接给出 Pos j 里的槽位。现在的换基折叠没有这样做。
2. **嵌套的换基被截断**。`seen` 调的是 `YiRBSib.ψ` 配 `rb-no`，不是 `YiBSFold.ψ` 自己（`Ωt (j ⊕ offsets c)` 不是结构更小的参数，自调用过不了停机检查）。重建树内部若再遇到 Ω 形状行（offsets c 含 Ω 形状，即 tw 2 起），走的是无表回退行。顶层经 `lift`（`inu` 行）不受影响，受影响的是重建树里底 `B` 的求值与内部链经 `inc` 的路径。要么按层号分层定义折叠，要么找到良基度量。
3. **原孩子树只进低层尾项**。y = `Ωt (h c)` 时无损（重建的就是同一个配方）。y 远大于 `Ωt (h c)` 时丢值。Ωt 生成的树里 Ω 形状行的 y 只有 `Ωt (h c)` 与经 `emb` 落到孩子 zero 的树（`emb … (ink v)`, `(inu vs)`）；后者在 `floor ≤ j` 支被 `Ωt (j ⊕ offsets zero)` 取代，纸面上是高估不是丢值。所以在 Ωt 读回域内这一条我判断不丢，在全域上丢。
4. 高估：y 很小而 `seen` 给 ψ_j(Ω_{j⊕off c})。对下界无害，对将来的互相 `≼` 有害。
5. 回灌输出作块：输出只作下标 c 进入，换基只用 `offsets c` 的形状，不看 y，这一处本身不丢；难点仍是 (a) 末的保持。上折（`self` 行）未改。

## (c) 进主线要重做什么

- 合法性：`YiBSFold.mono` 已与 ψ 同时定义，闭项 `closed n` 已有；Λ 的 `Rb` 是 `tt , rb-tw`，EBO 闭项可以直接写。View 与 FGH 在 Tr zero 上，不依赖折叠的行，应当可原样套用。
- 已证站值（对 `YiTBRow.ψ`/`rbᶻ` 的下界，`keelᶻ`, `Uᶻ` 等）不能直接搬：表有项处旧行做精确搬运，新行做 `seen`，两个折叠不逐字相等。要么重证，要么证 "换基折叠 ≽ 表折叠"（又是跨层号比较），要么写成 "先查表再换基" 的合行保住旧证。
- LowKeep 一类关于 `kp` 的引理：`kp` 没变则不必重做；若按 (b)1 修 `kp`，要重做。
- 若采用 `Read` 码（让行能对 y ≠ Ωt 重建），`up` 要带码，块 `Tr` 的定义要改，前三层全部重做。

## (d) 形状来自树还是记号

- 由树逼出的部分：c 与 c′ 不可比较（壁垒），所以不派发，改用字面公共地板 floor 与复合（`split` 只看路径字面）；Schema 的 floor/offsets 读自 `tw` 自己的定义 `tw n ⊕ ↑ (tw n) c`，属于层号龙骨。记号的规则 6 与 `fsn0 … (cΩ ν)` 靠 `cmpᵀ` 三歧，没有 "j ⊕ offsets" 这种东西。
- 受记号引导的部分：选 "在 j ⊕ offsets c 上重建 Ωt" 而不是别的替身，是用参照值（ψ_ω(Ω_{Ω₁})）挑出来的；`Read` 文法若进 `up`，是为验收域加的脚手架。判断：行的形状主要由树的要求逼出，值的取舍受记号验收引导，应如实记账；`Read` 码进块算新增脚手架。
```

#### 2. 对照之后：与主审判断的异同（5 问）

##### 问 1：会不会在别处掉值

- **同**：材料是 `Ωt (h c)` 时不丢，y 一般时丢。我的封存 (b)3 与 YiSV 的判断一致。两边都是判断，没有丢值的定理。
- **补充（判断）**：`YiBCReach.reach` 里到达换基行的嵌入块 `yₑ` 落在孩子 `c₀`。`floor ≤ j` 一支用 `Ωt (j ⊕ offsets zero)` 取代它，而 `j ⊕ offsets zero` 字面上在 `floor ⊕ offsets zero` 之上，嵌入块的来源层不高于后者。所以纸面上这是高估，不是丢值。只要下界时，嵌入块不需要码；需要的是参照一侧一条 "替身支配嵌入块" 的引理。
- **异（编译）**：主审第七十六批的小结没有列出下面这格。在 `YiBSFold` 上，取塔第 2 项，孩子 c′ = `Ωt (tw 1)`，目标 j = 偏移顶 Ω 形状结点的第 0 个孩子（逐字是 `nd sS (λ _ → tw 1)`）：
  - `route` 给 `inj₂`，即 `tw 1 ≤ j`（`above`）。
  - j 自己有分支类型 `Tr (tw 1)` 的槽位（`q-at`、`q-br`）。
  - 顶结点的保留判定是 `nothing`（`drop₂`，`refl`）。
  - `Ωt (tw 2)` 朝 j 的换基折叠对一切底与起点是 ℕ 极限（`chain₂`）。
- **这格与已有记录的区别**：`YiBLFold.main-noEv` 说的是孩子槽位（`inj₂ (c , t)`）。这里是下标层槽位（`inj₁ t`），失败在 `psh` 沿 `c₀` 推、而目标沿另一条 `inc` 走。它与 Review18 "换基后 D2 的槽位逐字高于目标，走链是对的" 一句不符：那句只对被换基的 `up` 行里面成立，对外面这个 Ω 结点不成立。
- **这格的档位**：形状档的编译事实。它在 EBO 的实际链上是否被问到是判断。依据是塔第 1 项的同形情形确实被问到（目标 `h₁ m` 经 `inc m self`，那里 v = self 所以保留）；高一层时目标路径会穿过偏移里的 Ω 形状结点。我没有在真实链点上展开。
- **嵌套（判断）**：`seen` 内部用 `rb-no`，封存 (b)2 与 `YiBCCover` 文首 "`YiBSFold` 那里现用 `rb-no`" 一致。`YiBCCover.rb-row` 给了证据，但没有人把它接进折叠。接进去要过停机检查，V149 记过 "写进互递归不过停机检查（只试一种写法）"。这是结构性缺口，小结里没有列。

##### 问 2：剩的三件是不是对的下一步

- **`StepS`**：是对的，也是我封存 (a) 末预计的难点。链点与参照只由关系相连，`YiSVRed.liftC` 把它归到后继一步。它在塔第 1 项、目标孩子 ω，且 `YiSVMono` 文首写明 "偏移含 Ω 形状时没有做"。
- **按读回域的充分性与参照出口**：对。
- **嵌入码**：我判断优先级应降。
  - 折叠拿到的是树 y，不是码。`YiBSFold` 只会用 `seen`（即 `omega`），`YiBSReadNeg.Ω-only-not-next` 已说明它不实现别的码。
  - 给 `Read` 加嵌入码只改变验收谓词 `Domain` 的范围，不改变折叠的值。要让折叠用码，`up` 得带码，那是改块。
  - 只要下界时，用问 1 里那条支配引理代替。
- **漏掉的更早缺口**（都在塔第 2 项起）：
  1. 上面编译的 `drop₂` 一格。
  2. `seen` 内部的 `rb-no`。
  3. 替身单调在偏移含 Ω 形状时没有。
- 塔第 1 项的值做得再全，也不触及这三处。

##### 问 3：是否在翻译记号

- **不读自基本列的部分**：
  - Review18 的 `seen` 来自 FGH 读法（"从层 j 看一块"），用的是 `Ok⊕`、`OkO↑`、`lift`。
  - `Schema` 的 `floor`/`offsets` 读自 `tw` 的定义 `tw n ⊕ ↑ (tw n) c`，按 "龙骨不算翻译" 不算。
  - 记号的规则 6 与 `fsn0 … (cΩ ν)` 用 `cmpᵀ` 三歧，没有 "目标 ⊕ 偏移" 的字段。
- **受记号引导、要如实记账的部分**：
  - 替身选 `Ωt (j ⊕ offsets c)`，是用参照值校准出来的（Review18 第 88 行 "与 Buchholz 的值相同"，`YiBSCrit`）。
  - V158 记的 "比孩子层号高两层" 的偏移（`tgt-shift`）是树与记号基本列的差，应留在翻译账里。
- **加深翻译的风险点**：`Read` 码与嵌入码。它们只能用验收域说明用途；若进 `up` 的字段，就是 AGENTS 说的 "闭包定理为它新增专属前提"。目前它们只在验收侧，没有进定义，应保持。

##### 问 4：进主线的代价，是否现在开完整闭项

**不建议现在换主线，也不建议现在开 "换基主线候选" 的全套值工作。** 依据是 `drop₂`/`chain₂`：候选折叠在塔第 2 项上还有保留判定的缺格，先定折叠的行。

- **闭项很便宜，可以现在写**：`Rb Λ = tt , rb-tw`，EBO 闭项与 `closed n` 是一行，合法性就是 `YiBSFold.mono`。这是 "交付拆成闭项与值" 里的 (a)。
- **View 与 FGH**：只依赖 `Tr zero`，判断可原样套用，我没有核文件。
- **站值要重证或加比较定理**：两个折叠在表有项的行上不逐字相同。
- **若按 `keepS` 改保留判定**：LowKeep 一类引理、`YiBL*` 的 `keepᴮ` 要重做。
- **若让 `up` 带码**：前三层全部重做，不建议。

##### 问 5：过程

- **把判断写成较强的话**：
  - 第七十六批小结 "剩下的是" 三件，读起来像穷尽。按 AGENTS "穷尽是判断" 应标判断，且漏了问 2 的三处。
  - 留档索引 "换基在替身树上保留"：`keep-lift` 证的是目标槽位的副本沿 `lift` 保留，`top-noEv` 同时证了替身自己的孩子层槽位不保留。一句话里应两条都写。
- **范围**：换基的值定理全在塔第 1 项、目标孩子 ω（ω 代替真实链点，记录里已写明）。"换基一路在三处都没有撞到否定" 属实，但三处都没有测塔第 2 项。这与 D 路指出的 "测试都在数字孩子上" 是同一类取样偏差，高了一层。
- **接口的否定读成值的否定**：没有发现。`YiBLNeg`、`YiBCNeg`、`YiDG` 的文首都写了 "不否定值"。
- **重复**：`YiSVMono` 与 `YiLTLift.upS`/`upL` 同形，已记，已派 YiZS 合并。没有发现新的重复派发。
- **依据的档位**：关闭现行折叠那一格的依据是两份 Fable 封存审核（第二种依据），记录里写了 "没有值的编译否定"，合规。

#### 3. 缺口清单

| # | 缺口 | 精确陈述 | 档 |
|---|---|---|---|
| G1 | 换基折叠的保留判定在塔第 2 项顶结点缺格 | `AuditEKeep.drop₂ : kp (tw 2) (Ok-tw 2) (inj₁ (inj₁ tt)) (inc c′ v) ≡ nothing`，同时 `above`（`tw 1 ≤ j`）、`q-at : at j q ≡ tw 1`；`chain₂` | 编译（形状）；在真实链上是否被问到是判断 |
| G2 | `seen` 内部无换基证据 | `YiBSBase.seen` 用 `R.rb-no`；接 `YiBCCover.rb-row` 需过停机检查 | 定义事实；后果是判断 |
| G3 | 替身单调只对不含 Ω 形状的偏移 | `YiSVMono.mono-path` 的 `NoΩ` 前提 | 编译定理的前提 |
| G4 | 后继一步 | `YiSVRed.StepS`，η = ω+2 起 | 未证，无否定 |
| G5 | 参照一侧出口 | `YiBLFold.lowᴮ` 的前提 `OutR`、`Sys.Out` 未实填 | 条件定理 |
| G6 | 嵌入块 | `YiBCNeg.emb∉read`、`YiBCReach.yₑ∉`；我判断下界只需 "替身支配嵌入块" 的参照侧引理，这条引理没有陈述 | 编译否定只对码域；其余是判断 |
| G7 | 换基折叠与表折叠的比较 | 没有 `YiTBRow.ψ … ≼ YiBSFold.ψ …` 一类定理，旧站值不能搬 | 缺陈述 |
| G8 | y 一般时丢值 | 无定理 | 判断 |

#### 4. 推荐的下一步

1. **先定换基折叠的保留行**：把 `keepS`（`route` 落在地板之上时沿 `index-floor ∙ u` 推槽位）接进一个新的折叠文件，查它对 `obs→dec` 一族的前提（它不看孩子下标，只用 `Schema` 与路径，判断不落入），再重跑 `YiBL*` 的树一侧律。这是树侧理由的定义改动，按 AGENTS 交作者定。
2. **塔第 2 项的最小实例**：在真实链点或其 ω 代替上，查 G1 那格是否被问到，以及 G2 的 `rb-no` 在哪一行第一次起作用。仿 YiRK 的做法，高一层。
3. **`StepS` 继续**（YiZS 在跑），但把陈述写成对偏移参数的一步定理，前提不带 `NoΩ`，使它不必在塔第 2 项重证。
4. **嵌入码降级**：改成参照侧的支配引理（G6）。同时写出换基的 EBO 闭项（一行），只作闭项交付，不称主线。

换基方向对路。应现在补的是 G1、G2，不是换主线。

#### 5. 编译过的文件

都在 `<实验目录>/audit/E/`，纯 `.agda`，简报给的选项行，8G；无 `postulate`、洞、`TERMINATING`。

- **`AuditEKeep.agda`**：退出 0，日志只有自己的 Checking 行。
  - `j-shape : j ≡ nd sS (λ _ → tw 1)`
  - `rb-is : proj₁ (rb-tw 2) ≡ just S₂`
  - `above : Is₂ (route S₂ j c′ v)`
  - `q-at : at j q ≡ tw 1`、`q-br : Br j q ≡ Tr (tw 1)`
  - `drop₂ : kp (tw 2) (Ok-tw 2) (inj₁ (inj₁ tt)) (inc c′ v) ≡ nothing`
  - `chain₂ : (B : Base (tw 2)) (β : Tr⁺ j) → IsL (proj₁ (BS.ψ (tw 2) (Ok-tw 2) (rb-tw 2) B j (inc c′ v) β (proj₁ (Ωt (tw 2)))))`
  - 其中 `c′ = proj₁ (Ωt (tw 1))`，`v = inc zero self`。
- **`AuditEKeepFix.agda`**：退出 0，日志只有自己的 Checking 行。
  - `keepS : (S : Schema k h) (t : Pos⁼ k) → floor S ≤ j → Keep j (Br (nd (sΩ k) h) (inj₁ t)) (fromBr (nd (sΩ k) h) (inj₁ t) zero)`，对一切 Schema、槽位、目标。
  - `kp₂-kept : KeptAt q kp₂`：上面那格用 `keepS` 后保留在 q 上。
  - `step₂`：结点一步合法，直接用 `nodeLe`。
  - 只是保留判定的一行，没有接进折叠，没有值。

日志是同名加 `.log`。仓库文件未改（`git status` 的已改动文件与会话开始时相同）。

#### 6. 没有读、只凭转述引用的东西

- `AuditD.md` 全文、`YiRK.md`、`YiFI.md`、`YiCT.md`、`YiBL.md`、`YiBC.md`、`YiDG.md` 回报原文没有读，只读了 LOG 里主审的复核段与留档索引。`YiSV.md` 只看了检索到的三行。`Review18.md` 只看了检索 "换基/seen" 得到的行。
- 台账只读了 V149、V158、V290、V291、V293、V294、V296、V297 全文；V287 到 V289、V292、V295 只见截断的首行。
- 模块：
  - 没有打开：`YiRKChain`、`YiCTCall`、`YiFIIface`、`YiFIFold`、`YiFINeg`、`YiSVOmega`、`YiBLIface`、`YiDGDiag`、`YiDGCell`。
  - 只读了文首：`YiBCCover`、`YiBCReach`、`YiBSCrit`、`YiBSAccept`、`YiSVMono`。
  - 读了文首与部分陈述：`YiBLFold`、`YiBLNeg`、`YiBCNeg`、`YiSVRed`、`YiRKCell`、`YiBSUpNeg`、`YiBSReadNeg`。
- View 与 FGH 的现有文件没有核，"可原样套用" 是判断。
- "塔第 2 项那格在真实链上被问到"、"嵌入块是高估不是丢值" 都是纸面推演，没有编译。
- Bedrock 性能手册、`EBOHandbook.md` 没有读（本次编译没有遇到堆问题）。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：E 路，换基候选的独立审查（先读定义，后读结论）（Fable 5.2）

你在 Agda 研究仓库 `<仓库>` 上做一次独立的数学审查。全程用中文。作者 2026-11-17 选的选项原文："Fable 先读定义审查换基候选"。你的临时目录是 `<临时目录>/`，只在那里写。

#### 先读
- `AGENTS.md` 全文。
- **第 1 步封存之前不要读**：`probes/README.md`、`probes/LOG.md`、`probes/RESULTS.md`、`probes/Survey/RouteReview3.md`、`probes/Survey/IdeaLedger.md`、`probes/Survey/GoalOdds.md`、`probes/Survey/Reports-*`，以及各模块文首的判决段。

#### 问题
终点是 EBO = ψ₀(Λ)，要一个序数值 ≥ EBO 的编译定理。现行折叠在 "Ω 形状结点下、目标经某个孩子的路径、比较表在那一对孩子上缺项" 时不保留低于目标的槽位，作者已关闭现行折叠上的那一格。现在的候选是 "换基"：Ω 形状层号上经某个孩子朝目标折时，不用原孩子树，在 "目标层 ⊕ 偏移" 上重建 Ω 树沿 `lift` 朝原目标折。你的任务：独立判断换基候选对不对、会不会在别处掉值、它进主线要重做什么、它是不是在翻译记号。

#### 第 1 步：只读定义，写自己的判断并封存
只读这些定义（`grep`/`sed` 查签名与定义体，不整篇读大文件；都在 `probes/OCF/Lean/`，参照在 `probes/OCF/Align/`）：
- 块与现行折叠：`YiRWBlock`（`L`、`Tr`、`tw`、`_⊕_`、`↑`、`up`）、`YiRWOps`（`Ωt`、`Tr⁺`、`_⊞_`）、`YiRWPath`（`Ok`、`inc`/`inu`/`ink`、`lift`）、`YiRWFold`（`Base`、`Keep`、`kp`）、`YiTBRow`（`ψ`）、`YiMTTab`（`rbᶻ`、`twᶻ`、`EBOᶻ`）。
- 换基：`YiBSBase`（`Schema`、`split`、`rbO`、`rb-tw`、`seen`）、`YiBSFold`（`ψ`）、`YiRBSib`（核）、`YiBSRead`（`Read`、`read`、`Domain`）。
- 同步对象：`YiSYReduce`（`h₁`、`a₁`、`oᴱ`、`Bᴱ`、`Sync`、`chain`）。
- 参照：`probes/OCF/Align/EboLeanDef`（`fsn`、`fsT`）、`probes/OCF/Align/EBO`（`γT`、`Ωs`）、`probes/OCF/Align/Value`（`≼`）、`YiKVRel`（`readRW`）。
写一页以内的判断：(a) 换基行在同步对象的链步上做什么，能否承载需要的参照（例如目标孩子 ω 时 ψ_ω(Ω_{Ω₁})），依据哪几行；(b) 换基会不会在别处掉值（原孩子树只进低层尾项；回灌输出作块；上折；嵌套的换基），哪一处最危险；(c) 换基替换主线时，第一档成品（View、FGH、合法性）与已证的站值、LowKeep 哪些要重做；(d) 换基行的形状是由树的要求逼出，还是读自记号的基本列（AGENTS "攀爬与摆脱翻译要平衡"、"龙骨不算翻译"）。把这一页写进 `<临时目录>/plan.md`，用 `shasum -a 256` 算出哈希，记下 UTC 时间，回报里给出。封存后不再改它。

#### 第 2 步：对照已编译的结果并挑战
封存后读：`probes/Survey/Reports-2026-11-16/README.md`（第七十五批起）；`probes/LOG.md` 从 "2026-11-17: 路线审核 D 路 (Fable 5.2) 回来" 起到文末；`probes/Survey/Reports-2026-11-16/AuditD.md`；`probes/Survey/Reports-2026-11-12/Review18.md`（换基的来源）；台账 V149、V158、V287 到 V297。关键模块：`YiRKCell`、`YiRKChain`、`YiCTCall`、`YiFIIface`、`YiFIFold`、`YiFINeg`、`YiSVMono`、`YiSVOmega`、`YiSVRed`、`YiBLIface`、`YiBLFold`、`YiBLNeg`、`YiBCCover`、`YiBCNeg`、`YiBCReach`、`YiDGDiag`、`YiDGCell`，以及更早的 `YiBSCrit`、`YiBSAccept`、`YiBSReadNeg`、`YiBSUpNeg`。
挑战，逐条：
1. 换基会不会在别处掉值；"原材料只进低层尾项" 在回灌链里（一般嵌入）是否丢值（YiSV 判断会丢）。
2. 换基一路现在剩的三件（替身值的后继一步 `StepS`、按读回域的充分性与参照出口、码域的嵌入码）是不是对的下一步；有没有漏掉的更早的缺口。
3. 换基是否在翻译记号（Review18 的 `seen` 形状从哪里来；字段形状是否读自基本列）。
4. 换基进主线的代价清单；是否应当现在就开一个 "换基主线候选" 的完整闭项（`tw` 各项、`EBO`、View、FGH）。
5. 过程：这两批的记录里有没有把判断写成定理、把接口的否定读成值的否定、或重复派发。

#### 第 3 步（可选）：编译一个判定件
若某个判断能用一个小文件判定，写成纯 `.agda` 放在你的临时目录，选项行 `{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}`。编译（仓库根目录）：
`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes -i <临时目录> <文件> > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
退出码 0 通过，42 类型错误（先看日志首行是不是 `LibraryError`），251 堆耗尽，124 超时。同时只跑一个 agda，堆上限 8G。不许 `postulate`、洞、`TERMINATING`、K。

#### 规则
- 只在你的临时目录里写文件。不改仓库里任何文件（包括 README、LOG、台账、留档），不删 `.agdai`，不用 `--ignore-interfaces`，不 `rm`/`pkill`，不写 `/tmp`，不装包，不提交。
- 区分三档：编译定理、有限测试、判断或纸面分析。判断路线走不通必须指明依据（编译否定的名字与陈述，并核它否定的确实是这条路线）；没有就写 "未走通" 或 "存疑"。
- 不用比喻和 "只差"、"自然"、"严格更弱" 一类形容；说哪个定理、哪个前提。强度写 ψ₀(Ω_x)，x 用 Ω 的算术。

#### 回报（最后一条消息就是回报，主审会原样留档）
0. 对纲领与目标意味着什么（几句）。
1. 第 1 步的封存：哈希、UTC、计划全文。
2. 对照之后：你的判断与主审判断的异同，逐条（上面 5 问）。
3. 缺口清单：每个缺口精确到引理名或陈述，标档。
4. 推荐的下一步（按优先级，最多 4 条）；若认为换基不对路或应当现在就进主线候选，明说并给依据。
5. 你编译过的文件（若有）：路径、退出码、陈述。
6. 没有读、只凭转述引用的东西。

