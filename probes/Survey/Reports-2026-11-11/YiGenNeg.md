# 判定题，否定路 (YiGenNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 06:43 至 07:36 |
| 工具调用 / agda 编译 (粗数) | 71 / 23 |
| token (usage 字段，按消息去重) | 输出 301164；新写入缓存的输入 721739；读缓存的输入 20502657；其余输入 122 |
| 写过的仓库文件 | `YiGenNegAsk.lagda.md`, `YiGenNegLeft.lagda.md`, `YiGenNegNorm.lagda.md`, `YiGenNegOne.lagda.md`, `YiGenNegRel.lagda.md`, `YiGenNegShape.lagda.md`, `YiGenNegWall.lagda.md`, `YiGenNegWallWlpo.lagda.md` |
| 文件前缀 | `YiGenNeg` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 判定题的否定路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 条件的：LPO 型的墙不在链上；标准保留行下第 2 个链点问到极限层号字面相等的弱判定，加函数外延才是 WLPO；八件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是一道判定题的否定一侧: "规范的链是否必然要求被禁止的派发" — 你的任务是证明**必然要求**, 写成编译过的定理. 另一路 (构造路, 前缀 `YiGenFold`) 同时在找一条不要求它的链. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: 纲领四条 (第 3 条壁垒); "交替路线"; "量化域先取带证据的读回域" (反例对象不在读回域内的否定读作 "谓词太宽" — **这正是本题要避免的: 你的探针必须是链实际走到的对象**); Agda 一节; "结论的写法" (否定要编译定理且否定的确实是那条路线; 前提要可满足; 归到已知的墙要逐条核机制).
2. `probes/Survey/EBOHandbook.md` 只读 §3.1, §3.13, §4.1 到 §4.5, §5.4. `probes/Survey/Reports-2026-11-11/README.md` 的 §2. **必读两份回报原文**: 同目录 `YiOmNeg.md` (上一轮否定路; 尤其 O4, 走查的判断, §6 没写成的条目) 与 `YiOmFold.md` (上一轮构造路; 尤其 §4 替代行, §5 第一个障碍).
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - **本轮的共用接口 `YiGenIf`**: `OwnFold q`, `Honest q F ξ`, `point₀`, `point-step`.
   - 上一轮否定路: `YiOmNegBranch` (`TopBranch`, `top-branch→lpo`, `found→link`, `root-below`, `at-one-dec`, `own-in-branch`, `plus-node`, `plus-leaf`), `YiOmNegBranchFixed` (`FixedBranch`, `fixed→wlpo`, 条件), `YiOmNegSlot`, `YiOmNegTop` (`TopKeep`), `YiOmNegTrunk`; 再上一轮 `YiRawNegOmega` (`K₂ω`, `br`, `Link`, `compare-link`, `no-compare-tw2`, `dec-at→lpo`, `keep-fold→wlpo`, `oracle-model₂`).
   - 上一轮构造路 (被判定的对象): `YiOmFoldBase` (`RΩ`, `plusΩ`), `YiOmFoldChain` (`Φˢ⁺`: 自目标折叠, 保留一切结点, `top` 的行是归一坐标上的 `topᴺ`; `pointsᴺ`: 归一链), `YiOmFoldNorm` (`nrm`, `γ`, `βᴺ`, `topᴺ`, `norm-keep`, `point₁ᴺ-not-dom`), `YiOmFoldRel` (相对坐标的行 `rowᴿ`, `rel-compare`), `YiOmFold` (`Φ⁰`), `YiOmFoldGap`.
   - 更早的: `YiLvNegKeep` (`LPO`, `Locate`, `coordᴸ`, `levelᴸ`, `bare-way→lpo`), `YiLvNegCompare` (`At`, `coordᴺ`), `YiIrrNegWide` (`IrrSearch`, `Found`), `YiIrrNegWideDecide` (`IrrDecide`).
   - 块: `RR5IrrCore`, `RR5IrrCheck`; 接口 `YiOmIf`, `YiRawIf`, `YiLvIf`.
   查签名用检索, 大文件不要整篇读.

### 1 问题

乙线: 层号是树. 塔的第 3 项的闭项已做成. 第 4 步第一站 (公共上界 `tw 2`, 目标闭项是 `Ω̂ (suc (tw 2))` 的目标层 0 折叠, 读法 ψ₀(Ω_{Ω₁+1})) 没有过去. 已定的:

- `top-branch→lpo`: 目标落在某一支里, 树是 `top`: 各支的像对一切带守卫的坐标定义并满足保留律 (只对路径相连的对要求), 则 LPO. 它的目标族 `qα α` 是不是链点, **没有判定**.
- 构造路的相对坐标的行 `rowᴿ` 合法并保留根; 它只取尾部, 是替代行, 不是上一条否定的那一行.
- 链: 自目标折叠 `Φˢ⁺` 保留一切结点, 归一链 `pointsᴺ` 对一切 n 合法; 从第 1 个链点起, 目标层 0 的折叠缺分支槽位结点处的 `own` 折叠.
- 两路各自走查的判断 (没有定理): 第 1 到 2 个链点之后, `own` 会遇到别的支上的结点.

**要判定的:** 把链点 `pointsᴺ n` 折到第 0 层时, 折叠问到的每一对 (目标位置 q, 根在位置 r 的子树) 上, 能否都有 `YiGenIf.Honest` 的 `OwnFold`. 你做 "不能" 的一侧.

### 2 任务, 按次序; 每条交编译过的定理, 或写明 "没写成"

**G1 把走查变成编译事实.** 写出 `pointsᴺ 1`, `pointsᴺ 2` 的形状 (`refl` 的等式, 或对其中你要用的那一部分的等式): 根是什么结点, 起点那一支里有哪些分支槽位结点, 它们的位置与层号, 它们的分支里有没有 `top`, 有没有别的支上的结点. 目的是把 "折叠问到哪些 (q, r)" 定成事实, 不靠纸面走查.

**G2 链上问到的对.** 按目标层 0 的折叠的行 (结点层非零时: 链在结点自己的层里, 由目标在这个结点位置上的折叠 `own` 推进; `own` 作用在结点的分支上) 给出一个归纳的谓词 "链点的折叠问到 (q, ξ)": 它只含链实际走到的对 (链在结点内部的后续点依赖折叠自己的输出, 这一部分你可以只取第 0 点, 即下界那一支, 并写明; 只取第 0 点得到的问到的对更少, 否定因此更强). 证明某个具体的对在其中.

**G3 否定.** 对 G2 给出的问到的对, 任何 `Honest` 的 `OwnFold` 族推出什么 (LPO, WLPO, `IrrDecide`, `IrrSearch`, 或什么都推不出). 要求: 探针必须是 G2 里的对, 不许用链之外的坐标. 若问到的对上只有闭的, 具体的层号, 派发在那里可能本来就可判定 (`at-one-dec` 是一例): 那就如实交 "在第 n 个链点上问到的对都可判定" 的定理, 这是对构造路有利的结果, 同样要交.

**G4 保留结点的分支 (全域) 是不是问到的.** `top-branch→lpo` 用的是: 保留一个根在主干槽位的结点时, 它的分支函数对一切带守卫的坐标 η 都要给出像. 在链上: 自目标折叠 `Φˢ⁺` 保留 `top` 的根, 它的分支是 `βᴺ`; 之后把它折到某个分支目标时 (G2 里的某一对), 根 (层号 0) 是否在目标之下因而要保留, 它的各支是否因此对一切 η 都要折到那个目标? 这是 "链必然要求被禁止的派发" 最可能成立的地方. 定成定理: 给出链上一个具体的 (q, ξ), ξ 的根在主干槽位, 证明 `Honest` 加上 "保留结点的各支是分支的折叠" (写成最弱的联系, 像 `TopKeep`, `TopBranch` 那样) 推出 LPO 或你得到的原则. 若目标层在链的这一处只是 0 或 1 (没有极限层号的位置), 那里不碰墙: 找出链上第一个目标层含极限层号位置的对, 或证明前若干个链点上没有.

**G5 相对坐标的绕法挡不挡得住.** 构造路会试 "分支只取相对目标所在一支的坐标". 检验: 在 G4 的那一对上, 用相对坐标的分支族写出的保留结点, 作为 `Raw` 的结点是否合法 (它的分支函数的定义域仍是一切带守卫的 η; 相对坐标只是换了分支函数的取值), 以及它与 "诚实" 的关系: 相对坐标的行满足不满足 `Honest`? `Honest` 只说根; 给出一个更强的, 说到各支的陈述, 使得 `top-branch→lpo` 的论证适用于它, 并说明相对坐标的行不满足它 — 这样两路的分歧就落在 "各支要不要诚实" 这一条上, 写清楚.

**G6 挑战.** 两路的走查都判断会碰墙. 找反例或支持.

做不完不要紧: G1 到 G4 是主要的. 每条定理写清: 否定的是哪一种写法; **探针是否在链实际走到的对里** (这是本题的全部要点); 前提的实例或模型. 不把 `IrrSearch`, `IrrDecide`, LPO, WLPO 说成矛盾.

### 3 规则

- **只新建文件**, 前缀 `YiGenNeg`, 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 `YiGenIf`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另几路用前缀 `YiGenFold` (构造路), `YiBtVal` (值定理), 不要动它们的文件, 也不要依赖它们. 对共用接口的增补写在你自己的文件里, 并在回报里说.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 所在文件文首标 "条件".
- 否定结果写成编译过的定理; 有限样本的测试标为测试. 没有编译定理的地方只写 "未走通" 或 "没写成". 每个否定定理与条件定理的前提给一个实例或说明为何可满足.
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 链点是大的闭项: 等式的两边逐字写, 必要时把大的子项放 `opaque` 或只对用到的那一部分陈述 (手册 §4.2). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径).
- 你的临时目录: `<实验目录>/agents/genneg`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0; `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 通过; 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 一段话, 先说对纲领与目标意味着什么: 规范的链是否必然要求被禁止的派发 — 定理, 条件定理, 还是仍没有判定; 墙在第几个链点, 哪一对上.
2. 文件表: 文件, 代码行数, 冷编译退出码.
3. 定理表, 按 G1 到 G6: 名字, 一句白话, 文件, 档. 每条否定写: 否定的是哪一种写法; 探针是否在链实际走到的对里; 前提的实例或模型.
4. 正面结果单列 (包括 "这些对上派发可判定").
5. 没写成的条目与第一个障碍 (检查器报错原文, 缺的引理的 Agda 类型).
6. 偏离与事故.

## 回报原文

### 回报：判定题否定一侧 (`YiGenNeg*`)

#### 1 判决

**对纲领与目标。** 归一链在第 2 个链点上，按上一轮 `YiRawFold.Ψ` 的保留行 (保留结点的各支是原来各支的折叠) 与链行，必然问到 "一个固定的、层号含极限层号位置的目标 × 一个根槽位结点的一切支"，这是全分支的高层比较。诚实的派发在那里等价于弱判定两个极限层号的字面相等 (`WeakEq`，编译定理，无函数外延)；加上 `FunextR` 是 WLPO (条件定理)。LPO 型的墙没有成立：上一轮两条否定的探针目标都不在链问到的对里 (编译定理)。所以结论是**条件定理**，不是无条件的不可能性。

分档：

- **定理，正面，无前提。** 结点内部的链只取第 0 点时，对一切 n，`pointsᴺ n` 的折叠问到的目标层号都是 0，派发不需要判定 (`zero-point-level`)。两路走查说的墙不在这个片段里。
- **定理。** 对一切 n、任何后续链点、含保留结点的一切支：问到的目标都在主干上或归一坐标 `suc (nrm a)` 的支里 (`asked-norm`)。`top-branch→lpo` 的目标族 `qα α` 与 `fixed→wlpo` 的 `q_f` 不是归一坐标的支，不在链上 (`lpo-target-off-chain`, `fixed-target-off-chain`)。
- **定理，无函数外延。** 第 2 个链点上对 `(r*, P₁)` 被问到。`r*` 是第 `suc (nrm (suc ω′))` 支的根，层号 `suc M*`，`M* = read0 (nrm ω′)` 是 ℕ 极限。`P₁` 的根在根槽位，保留，各支对一切坐标被问到 (`probe`)。这些对上 `Honest` 推出 `WeakEq` (`chain→weak-eq`)。
- **条件定理 (`FunextR`)。** 同样的前提推出 WLPO (`chain→wlpo`)。
- **墙的位置。** 第 2 个链点，对 `(r*, B₁ (coordᴸ α))`。路径：根上第 1 个内部链点 → `r₁` (层号 1) → `N₂ = P₁ + Φˢ⁺ top` 的根保留 → 一切支 → `r*` → `P₁` 的根保留 → 一切支。
- **第 1 个链点。** 沿同一条路径只问到层号 0 与 1 的目标，`r₁` 之下没有新目标 (`under-r₁`)。

**探针在不在链实际走到的对里：在，但相对于三条规则。**
1. 根上第 1 个内部链点是 `plus zero 1 y`，`y` 是第 0 层折叠在起点那一支上的输出。这是唯一依赖折叠输出的地方；需要的 "最左叶是 1" 由折叠的四行推出 (`premise₂`)。
2. 保留行取标准写法 (`o-keep`)。用了两次：`N₂` 在 `r₁` 之下，`P₁` 在 `r*` 之下。**这正是构造路的相对坐标要否认的一条。**
3. 链行的推进问 "目标在结点位置上" 的折叠在下界那一支上的值 (`z-own`, `o-own`)。

**没有判定的。** 无函数外延时 `WeakEq` 推出什么；`y` 的其余叶上问到什么；保留行是否必须取标准写法 (值是否需要它)。

#### 2 文件表

都在 `<仓库>/probes/OCF/Align/`。八个文件删自己的接口后按依赖序冷编译 (6G 上限) 退出码全 0，每个约 2 秒，常驻约 0.45G。`importclosure.py OCF.Align.<模块>` 八个都是 "禁用表命中 0, OK"。禁用构造与本机路径检索为 0；`FunextR` 只出现在 `YiGenNegWallWlpo` (文首标了条件)。

| 文件 | 代码行 / 总行 | 冷编译 |
|---|---|---|
| `YiGenNegShape.lagda.md` | 83 / 135 | 0 |
| `YiGenNegAsk.lagda.md` | 128 / 194 | 0 |
| `YiGenNegLeft.lagda.md` | 115 / 175 | 0 |
| `YiGenNegWall.lagda.md` | 246 / 363 | 0 |
| `YiGenNegWallWlpo.lagda.md` (条件) | 52 / 66 | 0 |
| `YiGenNegOne.lagda.md` | 123 / 172 | 0 |
| `YiGenNegNorm.lagda.md` | 167 / 225 | 0 |
| `YiGenNegRel.lagda.md` | 46 / 89 | 0 |

依赖序：Shape → Ask → Left → Wall → WallWlpo；One 依赖 Wall 与 Left；Norm 依赖 Ask；Rel 依赖 Wall。日志在 `<实验目录>/agents/genneg/` 下的 `<模块>.cold.log`。

#### 3 定理表

##### G1 形状 (`YiGenNegShape`，全是 `refl` 的等式加一条封闭引理)

| 名字 | 白话 |
|---|---|
| `point₁-root`, `point₂-root` | 两个链点的根都是根槽位上的结点，下界 1；第 η 支是 `B₁ η = top + Gκ η`，`B₂ η = P₁ + Φˢ⁺(top + Gκ η)` |
| `branch₁-root`, `branch₂-root`, `rᴺ-level` | 第 `suc a` 支的根在 `rᴺ a` (第 `suc (nrm a)` 支的根槽位) 上，层号 `read0 (nrm a)`，下界 `cO`，对一切 a |
| `start-level`, `start-bound` | 起点那一支 (a = 0) 的结点层号 0，下界 1 |
| `start₁-trunk`, `start₁-low`, `start₁-term₀` | 第 1 个链点里这一支的各支都在主干片段 `Tr` 里；下界那一支是 ℕ 极限，第 0 项是 `top + topᴬ t₀` |
| `top₁-node`, `topᴬ-low`, `plus-top` | 被加数出现在 `top` 的展开之下，所以树里有字面的叶 `top` |
| `N₂-image`, `N₂-root`, `N₂-branch` | 第 2 个链点里有 `N₂ = P₁ + Φˢ⁺ top`，它的第 `suc a` 支的根遍历一切 `rᴺ a` (别的支上的结点) |

##### G2 问到的对 (`YiGenNegAsk`)

- `Asked.Ask⁰`, `Asked.Ask`：归纳谓词，参数是起点树与第 0 层折叠的图 `Out`。规则：后继与极限逐项；目标层 0 的结点取第 0 点 (`z-obs`, `z-own`)；根槽位结点的第 1 点 (`z-next`，加法取 `plus zero`，同 `YiOmFold.NodeRow.next-row`)；保留行的一切支 (`o-keep`)；链行的推进 (`o-own`)。守卫都取相关证明。
- 取少了的地方：结点内部只取第 0 点与根槽位上的一种第 1 点。`Out` 取空关系就是只取第 0 点。
- 具体的对 (编译定理)：`asked₁` (第 1 个链点，目标 `rᴺ 0`)；`asked₂-start`, `asked₂-N₂` (第 2 个链点沿第 0 点走到 `N₂`，对任何 `Out`)。

##### G3 这些对上 `Honest` 推出什么

- **只取第 0 点：什么都推不出 (定理，正面)。** `ZeroPoint.zero-point-level`, `zero-point-fold`, `zero-point-honest`：对一切 n，目标层号都是 0，常值极限的折叠族在这些对上就是 `Honest` 的。无前提。
- **加上第 1 个内部链点与保留行：`WeakEq`**，见 G4。

##### G4 保留结点的全域分支 (`YiGenNegWall`, `YiGenNegLeft`, `YiGenNegWallWlpo`, `YiGenNegOne`)

| 名字 | 白话 | 档 |
|---|---|---|
| `Path.a-N₂`, `a-all` | `r₁` (层号 1) 之下走到 `N₂`；根保留，一切支被问到 | 定理 (带前提) |
| `r₁-dec` | 目标层 1 上派发可判定 | 定理 (正面) |
| `Path.b-own`, `b-P₁`, `b-all`, `probe` | `N₂` 的第 `suc (suc ω′)` 支的根 `r*` 在目标之上，推进问目标 `r*`；其下走到 `P₁`，根保留，一切支被问到 | 定理 (带前提) |
| `KeepRowAt`, `row→weak`, `row→weak-eq` | 最弱联系 (只有分支族与它相对于原各支的派发律，不含折叠，不写保留结点怎样装进输出) 在 `(r*, P₁)` 上推出 `WeakEq` | 定理 |
| `at→eq`, `eq→at` | "在 `suc M*` 的位置上" 等价于 "字面等于 `M*`" | 定理 |
| `eq→false`, `weak-eq→half` | `Eqᴸ α` 推出 α 全假；`WeakEq` 给出 "不等，或 α 全假" (无函数外延能得到的一半) | 定理 |
| `chain→weak-eq` | `Rows Out` + `Out (B₂ 1) y` + 链点守卫 + 问到的对上 `Honest` ⟹ `WeakEq` | 定理 |
| `Rows`, `rows→left`, `desc-start₂`, `premise₂` | 四行 (`top` 的值最左叶是 1；后继、极限、结点的输出是 ℕ 极限且第 0 项是下一层的值) 推出 `LeftOne y` | 定理 |
| `weak-eq→wlpo`, `row→wlpo`, `honest→wlpo`, `chain→wlpo` | 加 `FunextR` 得 WLPO | 条件定理 |
| `Path₁.asked-r₁`, `under-r₁`, `under-asked` | 第 1 个链点：`r₁` 被问到，其下结点层号都是 0，目标不变 | 定理 (正面) |

- **否定的写法：** "保留行取标准写法，且在问到的每一对上派发完全且不多保留"。不否定：保留结点的各支不是原各支的折叠的行 (相对坐标)；不满足四行的第 0 层折叠；目标层只有 0 或 1 的片段。
- **探针是否在链上：** 在，相对于上面三条规则。目标 `r*` 与探针坐标 `coordᴸ α` 的守卫都是闭的相关证明。`coordᴸ α` 是经 `o-keep` 的 "一切带守卫的坐标" 进来的，不是内部链点。
- **前提的实例：**
  - `oracle-honest`：`Locate` 下 `Honest` 处处成立。
  - `rows⁰`：上一轮的 `Φ⁰` 在 `Dom⁰` 上满足四行 (`top` 给 `T₃ᵐ`，最左叶在三层极限下是 1)。
  - `rowsˢ`, `outˢ`, `guardˢ`：骨架值 `valˢ` 给出含 `B₂ 1` 的实例。它不是折叠，只说明前提不空。
  - `premises-model : Locate → WeakEq`：全部前提同时填上。
- **机制：** 与 `fixed→wlpo` 相同 (极限层号的字面相等)，不是 `top-branch→lpo` 的搜索型。没有核对它是不是 `Barrier.barrier` 的实例。

##### G5 相对坐标 (`YiGenNegRel`)

| 名字 | 白话 | 档 |
|---|---|---|
| `BranchKeep` | "各支诚实" 在树 `top` 上的陈述 (`TopBranch.branch-keep` 固定目标、去掉 `Link`) | 定义 |
| `row₃-root-kept` | 规范实例 `row₃` 根保留 (转述已有的 `rowᴿ-kept`；合法性是已有的 `rowᴿ-legal`) | 定理 |
| `row₃-branch-lim`, `row₃-branch-not-kept`, `row₃-not-branch-keep` | `row₃` 的第 1 支是 ℕ 极限，而 `top` 的第 1 支的根层号 0 在目标层 2 的位置上：不满足 `BranchKeep` | 定理 |
| `cheap-root`, `cheap-lgl`, `cheap-not-branch` | 在 `(r*, P₁)` 上只在根上诚实的输出便宜地存在，它的分支族处处不诚实 | 定理 |

结论：相对坐标的行作为 `Raw` 的结点合法，分支定义域仍是一切带守卫的坐标，根上诚实；各支不诚实。两路的分歧落在 "保留结点的各支要不要是原来各支的折叠" 上。`P₁` 上没有现成的相对坐标的行可测 (`rowᴿ` 只对 `top` 定义)。

##### G6 挑战 (`YiGenNegNorm` 及上面各条)

- **反例一侧：**
  - `points-NB`, `asked-norm`, `lpo-target-off-chain`, `fixed-target-off-chain` (定理)：归一把上一轮两个探针目标挡在链外。
  - `zero-point-level` (定理)：第 0 点片段对一切 n 不碰墙。
  - `under-r₁` (定理)：第 1 个链点沿最左叶只到层号 1。
- **支持一侧：** 第 2 个链点上 `r₁` 的推进确实遇到别的支上的结点，对一切坐标 (`a-all`, `N₂-branch`)，并进而问到含极限层号位置的目标 (`b-own`)。
- **判断 (纸面，未编译)：** 归一之后有限层号对归一目标的 `At` 是可判定的 (部分和使每个有限层号最终出现)，所以搜索型的 LPO 编码在归一链上找不到；剩下的只有极限层号的字面相等。

#### 4 正面结果 (对构造路有利)

- `zero-point-level`, `zero-point-honest`：只取第 0 点，一切链点上派发不需要判定。
- `r₁-dec`, `under-r₁`, `under-r₁-kept`：目标层 1 上可判定；第 1 个链点沿最左叶没有新目标。
- `asked-norm`, `rᴺ-norm`：链上目标都在归一坐标的支里；上一轮的 LPO 探针不适用。
- `premises-model`, `oracle-honest`：结论都不是矛盾。
- `weak-eq→half`：无函数外延时 `WeakEq` 只给一半。

#### 5 没写成的条目与第一个障碍

1. **无函数外延的 WLPO 或 LPO。** 缺 `(∀ n → α n ≡ false) → nrm (one +ʳ dense α) ≡ nrm ω′`，不借 `FunextR` 得不到 (两边是逐点相等的两个函数的 `G.lim`)。LPO 型编码试过纸面构造：归一的第 n 块的层号字面带前缀 `psum G (n-1)`，探针层号无法在不知道见证下标时与它字面相等。没有写成定理。
2. **`WeakEq` 在无函数外延时推出什么：** 没有判定。
3. **`y` 的其余叶、根以外结点的后续链点、非零层结点的后续链点：** 没有进 `Ask`，问到什么没有判定。
4. **第 1 个链点上有没有含极限层号位置的目标：** 只证了最左叶路径上没有。判断：其余叶上会有，但其下没有 `Φˢ⁺ top` 的像，只遇到路径相连的结点。
5. **"有限层号对归一目标可判定"：** 没写，只是判断。
6. **链点守卫 `Gd zero raw1 (plus zero one y)`：** 作为显式前提，没有从四行推出 (四行不含输出合法)。`Rows.r-node` 对一切结点陈述，实际只用到层号 0 的槽位。
7. **保留行是否必须取标准写法：** 没有判定。本轮的定理对否认 `o-keep` 的折叠不说话。

没有检查器拒绝后放弃的写法。

#### 6 偏离与事故

- **对共用接口的增补，都在自己的文件里，`YiGenIf` 没有动：** `Asked`, `LeftOne`, `C₃`, `E`, `constF` (Ask)；`Rows`, `Desc`, `Out⁰`, `valˢ`, `Outˢ` (Left)；`HonestAt`, `KeepRowAt`, `Weak`, `WeakEq`, `Eqᴸ`, `Fᵒ` (Wall)；`Lz`, `Under` (One)；`NP`, `NB` (Norm)；`BranchKeep` (Rel)。
- **超出简报的：** `YiGenNegLeft` (前提的依据与实例)、`YiGenNegOne` (第 1 个链点的对照)、`YiGenNegNorm` 里对 `q_f` 的一条。
- **中途改过一次定义：** `z-next` 的加法先写成 `_+ʳ_`，后改成 `plus zero`，以与 `YiOmFold.NodeRow.next-row` 字面一致；五个文件随之改了前提的类型，全部重编通过。
- **改文件的方式：** 对自己前缀的文件用脚本做了若干次字符串替换。
- **编译：** 类型错误三次，都已修——临时目录两次 (`γ a*` 的守卫类型用错；把 `thru` 用在 `topᴬ P₁` 上)，仓库文件一次 (`YiGenNegRel` 的 `cheap-not-branch` 隐式参数未解，退出码 42，改成直接写)。没有堆耗尽。全程同时只跑一个 agda，没用 `--ignore-interfaces`，只按字面路径删过自己八个模块的接口 (两轮)。
- **没有做的：** 没有读也没有依赖 `YiGenFold*`, `YiBtVal*`；没有改任何已有文件；没有提交、推送、`pkill`、装包。
- **临时目录：** `<实验目录>/agents/genneg/t/` 里有四个纯 `.agda` 试验 (`T1` 到 `T4`)、一个 `genneg.agda-lib` 与 agda 生成的 `_build`，不是成果。
- **文字预算：** 各文件文首 3 到 4 行。
