# A 路：当前主线的数学审核（先读定义，后读结论）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-16 12:05 至 12:20 |
| 工具调用 / agda 编译 (粗数) | 34 / 1 |
| token (usage 字段，按消息去重) | 输出 84137；新写入缓存的输入 318063；读缓存的输入 3962158；其余输入 54 |
| 写过的仓库文件 | 无 |
| 主审复核后的一句结论 | 主审核对：封存件 SHA 一致；AuditASync 主审冷编退出 0；k1-value、k2 的证法（BTBO 加站间单调）、eboᵍ、SlotLaw 与 SlotValue 恒等互推、¬Mono 属记号一侧项序，均属实；对位调整在台账与日志里未见先例 |

## 简报原文

你在 Agda 研究仓库 `<仓库>` 上做一次独立的数学路线审核。全程用中文。这是作者 2026-11-16 的指令："派一路或多路Fable 5.2做全量路线审核, 包括近期外部模型的所有工作, 以及外部模型之前的工作整体的延续过程"。主审把它拆成三路，范围互不重叠；你是 A 路：**当前主线的数学审核，先读定义，后读结论**。另两路分别审近期外部模型工作的过程（B）与 11-01 以来的整体延续（C），你不用管它们的范围。

#### 先读
- `AGENTS.md`（全文：纲领、目标、最佳实践、Agda 规则、结论的写法）。
- 不要先读 `probes/README.md`、`probes/LOG.md`、`probes/RESULTS.md`、`probes/Survey/RouteReview3.md`、`probes/Survey/IdeaLedger.md`、`probes/Survey/GoalOdds.md` 与 `probes/Survey/Reports-*`，直到第 1 步封存之后。

#### 问题
项目的终点是 EBO = ψ₀(Λ)（Λ 是 x ↦ Ω_x 的第一个不动点），要一个序数值 ≥ EBO 的编译定理。现在的主线把终点归结为对一切 n 的 "站值下界"，第 0 到 2 站已成立，第 3 站卡住；第 3 站拆出一个里程碑 ψ₀(Ω_{Ω₂})，又在一个 "干净对象"（没有回灌链与继承底的试验层号）上先攻它的基本列。你的任务：独立判断这条攻法对不对、缺口到底在哪里、这些定义能不能走到 EBO、下一步最该做什么。

#### 第 1 步：只读定义，写自己的判断并封存
只读这些定义（用 `grep`/`sed` 查签名，不整篇读大文件）：
- 块与层号：`probes/OCF/Lean/YiRWBlock.lagda.md`（`L`、`Tr`、`tw`、`_⊕_`、`↑`）、`YiRWOps`（`Ωt`、`Tr⁺`、`limc⁺`、`cum`）、`YiRWPath`（`Ok`、路径构造子 `inc`/`inu`/`ink`）、`YiRWFold`（`Base`、`B₀`、`Keep`）。
- 折叠与表：`YiTBRow`（`ψ`、`mono`）、`YiMTTab`（最小比较表 `rbᶻ`、`ψ₀ᶻ`、`twᶻ`）。
- 终点与站：`YiS1Accept`（`Kᴱ`、`ebo-from-stations`）、`YiFRStep`（`Step n`、`FirstMissing`）、`YiGIInst`（`keelᴱ`）。
- 第 3 站的内层：`YiE4Base`（`Ctx`、`collapse`）、`YiE4Inner`（`Inner`：`g`、`feed`、`out`、`chain`、`row`）。
- 干净对象：`YiUTTwo`。
- 参照一侧：`probes/OCF/Align/EboLeanDef`（记号与基本列 `fsn`、`fsT`）、`OCF/Align/Value`（`≼`）、`YiKVRel`（`readRW`、`M⁰`）、`YiAZLocal`（`S`）。
写一页以内的判断：折叠在干净对象与第 3 站上做什么；里程碑 ψ₀(Ω_{Ω₂}) 的基本列第 0、1 项要哪些关于折叠的性质；你认为最难的一步在哪里，它是数学上难还是工程上难；这套定义有没有可能在某处掉值（若有，在哪一步）。把这一页写进 `<实验目录>/audit/A/plan.md`，用 `shasum -a 256` 算出哈希，记下 UTC 时间，回报里给出。封存后不再改它。

#### 第 2 步：对照已编译的结果并挑战
读 `probes/RESULTS.md` 末尾约 15 行、`probes/Survey/RouteReview3.md` 末尾约 60 行、`probes/LOG.md` 从 "2026-11-15: YiM2, YiOL, YiIR 的代码复核" 起到文末。关键模块（都在 `probes/OCF/Lean/`）：
- 里程碑与干净对象：`YiAZLocal`、`YiM2Chain`、`YiOLBoost`、`YiOLMilestone`、`YiUTTwoLocal`、`YiC0Accept`、`YiC0Reduce`、`YiC0Connect`、`YiC0Next`。
- 第 1 项的分解：`YiC1Slot`（`BranchNeed`）、`YiRXOmegaHead`、`YiNIIface`、`YiNISuff`、`YiBVSmall`、`YiQLRead`（`Step`）、`YiSQNat`、`YiSQOmega`、`YiSQPremise`、`YiFPFrames`、`YiFPFinite`、`YiFPReadback`、`YiOPCountable`、`YiKWObjects`。
- 刚回来、主审还在冷编的第六十九批：前缀 `YiGC`（精确对应到 `Align.Level` 的沿帧主引理，`YiGCBridge.Narrow` 未造）、`YiDN`（`YiDNNoOmega`：没有 Ω 结点的偏移与 "读回不低于 slot" 不能同时成立）、`YiWY`（`kept` 同一性第三次 8G 堆墙）、`YiOG`（摆脱侧，树侧比较的第 1 前缀）。
挑战主审的判断：(1) "第 1 项的缺口是 `BranchNeed`，再压到 '可数层号上的 Leaf，目标第 1 层'"；(2) "更深颈结点的律" 是不是第二个缺口，`YiDNNoOmega` 对它意味着什么；(3) 在干净对象上先攻是否值得，结论能否搬回第 3 站的实际对象；(4) 从里程碑到 T[0]、第 3 站、一切站，路还有多长，这些缺口是不是同一条引理的反复出现，是否应当换成一条整体的引理（AGENTS 最佳实践 "同类引理以不同名字第二次出现时, 合并成一条并写进接口"）。

#### 第 3 步（可选）：编译一个判定件
若某个判断能用一个小文件判定（一个下界、一个上界或一个否定），写成纯 `.agda` 放在你的临时目录 `<实验目录>/audit/A/`，选项行 `{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}`。编译（仓库根目录）：
`agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes -i <你的临时目录> <文件> > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
退出码 0 通过，42 类型错误（先看日志首行是不是 `LibraryError`），251 堆耗尽，124 超时。同时只跑一个 agda，堆上限 8G。不许 `postulate`、洞、`TERMINATING`、K。

#### 规则
- 只在你的临时目录里写文件。不改仓库里任何文件（包括 README、LOG、台账、留档），不删 `.agdai`，不用 `--ignore-interfaces`，不 `rm`/`pkill`，不装包，不提交。
- 区分三档：编译定理、有限测试、判断或纸面分析。判断路线走不通必须指明依据（编译否定的名字与陈述）；没有就写 "未走通" 或 "存疑"。
- 不用比喻和 "只差"、"自然"、"严格更弱" 一类形容；说哪个定理、哪个前提。

#### 回报（最后一条消息就是回报，主审会原样留档）
0. 对纲领与目标意味着什么（几句）。
1. 第 1 步的封存：哈希、UTC、计划全文。
2. 对照之后：你的判断与主审判断的异同，逐条（上面 4 问）。
3. 缺口清单：每个缺口精确到引理名或陈述，标档。
4. 推荐的下一步（按优先级，最多 4 条），每条说清目的、为何比其他的好、预计难点；若认为当前攻法应当整体改变，明说并给依据。
5. 你编译过的文件（若有）：路径、退出码、陈述。
6. 没有读、只凭转述引用的东西。

## 回报原文

### A 路回报: 当前主线的数学审核 (先读定义, 后读结论)

档位约定: 【定理】= 仓库里已编译并且我读过陈述的; 【本路编译】= 我在临时目录编过的; 【判断】= 纸面分析, 未编译. 下文凡未标【定理】的都是判断.

#### 0. 对纲领与目标意味着什么

- 纲领四条没有被触犯; 我没有发现需要改树、折叠、合法性定义的依据, 也没有发现定义在 EBO 以下掉值的编译证据.
- 对目标 "让树自足": 第 61 到 69 批在具体链点上逐项展开, 是 "按阶段定制支配论证" 的形态, 与进展判据 "闭包定理与阶段无关" 相反. 这九批里同一条引理以至少七个名字出现, 应按 AGENTS "同类引理第二次出现就合并进接口" 处理.
- 对终点: 现主线折叠上, 编译过的值仍在 BTBO = ψ₀(Ω_Ω) 这一档加小增量. "第 0 到 2 站已成立" 里的第 2 站不是 `tw 2` 的折叠做出来的, 而是 `twᶻ 1` 的值加站间单调 (见 2.0). 孩子来自不可数层的 Ω 形状层号上, 折叠自己产生的值至今没有一条超过 BTBO 的定理.
- 我的结论: 逐项攻法应当停工 (不是否定), 改成一条对读回域一般的树侧引理加一次对位调整. 依据是判断加两条编译事实, 不是否定定理.

#### 1. 第 1 步的封存

- 文件: `<实验目录>/audit/A/plan.md`
- SHA-256: `ff7752147b2ef09c5abb623e7bc4432e3bf44a6930a19b8d3683a63367b74ab1`
- UTC: 2026-11-16T12:11:41Z; 封存后未改, 回报前重算哈希一致.
- 封存前除简报列的定义外, 还读了 `OCF/Align/EBO.lagda.md` 的 `fsT`/`γT`/`ΩTower`/`cofψ0` 与 `YiAZStart` 的 `T`/`P` 签名 (为读懂参照一侧).

计划全文:

```
# A 路第 1 步: 只读定义后的判断 (封存件)

范围: 只读了简报列出的定义 (YiRWBlock/Ops/Path/Fold, YiTBRow, YiMTTab, YiS1Accept, YiFRStep, YiGIInst, YiE4Base/Inner, YiUTTwo, EboLeanDef, EBO 的 fsT/γT/ΩTower, YiAZLocal, YiKVRel 的签名). 以下除标明外都是纸面判断, 未编译.

## 1. 折叠在干净对象与第 3 站上做什么
- 层号读法: `Tr a` 是 Ω_{a+1} 以下的树, `Ωt a` 是 Ω_a (Ω_0 = 1). 干净对象 ℓ₂ = nd (sΩ one) a, a d = 2 + d + 1 (d ∈ Tr one), 层号值 Ω₂; `Ωt ℓ₂` = Ω 结点 d ↦ upz d (Ωt (a d)).
- `output` 在顶结点处 `kp = nothing` (目标 zero 无槽位), 所以 = limc⁺ (out (chain n)); chain 0 = 0, chain (n+1) = feed (chain n) ∈ Tr one. 展开一层: feed d = (层 a d, 目标 one, 路径 kh d = inu…(inc tt self), 底 Ωt one) 折 Ωt (a d); out d = (层 a d, 目标 zero, 路径 z≤) 折 Ωt (a d). 即 chain (n+1) "=" ψ₁(Ω_{2+chain n+1}), out d "=" ψ₀(Ω_{2+d+1}).
- a d 是后继形状, Ωt (a d) 是在 Tr (two ⊕ ↑ one d) 上分支的 Ω 结点, 对目标 one 与 zero 都不保留, 又是一条内链 z₀ = 0, z_{m+1} = next⁺ (自身目标折 z_m), 取 G z = next⁺ (折 z). 所以树的 feed d 永远是 ℕ 极限 (部分和), 其中每个部分和是 Ω 结点 (x + Ω p g = Ω p (x + g)).
- 第 3 站 (`Step 2`): 同一形状, k = tw 2, 孩子 tw 2 ⊕ ↑ c, 但底是继承底 baseᴱ 3 / betaᴱ 3 (Λ 上对 pre 3 的折叠), 链在 Tr (tw 2) 里.

## 2. 里程碑 S 2 = ψ₀(Ω_{Ω₂}) 的基本列要什么
记号: S2[n] = ψ₀(Ω_{γ_n}), γ₀ = Ω₁, γ_{k+1} = ψ₁(Ω_{γ_k}) (规则 6, μ = 1).
- 第 0 项 ψ₀(Ω_{Ω₁}): out (chain 0) = "ψ₀(Ω₃)" 不够, 至少要 q = 1. 要 (P0a) chain 1 的读回层号 ↑ one (chain 1) 里字面找到一个 Ω₁ 形的子层号 (sΩ zero 结点, 带前缀偏移); (P0b) 下标保持到目标 zero: 记号下标 γ 与树下标 d 有下界关系时, ψ₀(Ω_γ) 的树 ≼ out d. Ω₁ 形下标处是对角链 e_{m+1} = 折 (Ω_{A ⊕ ↑(e_m+1)}) 对 γ′_{m+1} = ψ₀(Ω_{γ′_m}), 归纳步是 "可数下标 e 上的 Ωt, 目标 zero" 的保持.
- 第 1 项 ψ₀(Ω_{ψ₁(Ω_{Ω₁})}): 另要 (P1a) 同一条保持在目标 one: 关系 (Ω₁, d) ⇒ 关系 (ψ₁(Ω_{Ω₁}), feed d). 记号一侧 ψ₁(Ω_{Ω₁}) 共尾 Ω₁ (规则 5Ω 穿透), 树一侧 feed d 是 ℕ 极限: 两边基本列形状不同, 关系必须是下界关系 (对树一侧向上封闭), 不能逐项对齐; 要对每个可数 η 给 ψ₁(Ω_η) ≼ 某个部分和, 即 "可数下标上的 Ωt, 目标 one". (P1b) 再把 (ψ₁(Ω_{Ω₁}), chain 2) 喂回 (P0b), 这时树下标 chain 2 是 ℕ 极限套部分和套 Ω 结点, ↑ 之后是 sL → sΩ zero → ⊕ 的嵌套层号, 每一层形状都要一条保持行.

## 3. 最难的一步
一条引理的各种实例: **下标保持** —— 对读回层号 A ⊕ ↑ k d, d 只通过与记号下标 γ 的下界关系给出, 对三种目标 (低于、同层保留、自身) 有 折_j (Ωt (A ⊕ ↑ d)) ⊵ ψ_j(Ω_{A+γ}). 判断它是数学上难, 不只是工程: (i) `Lt` 是第一位置序, `mono` 只管 ◃, Ω 结点处只知道第 0 分支在下面, 非保留结点的值只采样链点, 所以 "c ≤ 链点 ⇒ G c ≤ G 链点" 不是 `mono` 的推论, 是跨层的单调, 只能对带证据的域证; (ii) 树的回灌输出与记号下标共尾度不同, 关系要设计成不逐项的下界关系, 且要对 ↑ 的每种形状 (sS, sL, sΩ) 与每种目标各有一行. 工程难 (堆墙) 是第二位的. 判断: 第 0 项的 q、第 1 项、T[0]、第 3 站的 Tail、一切站的 Tail 都是这一条引理, 应当写成一条对 (A, k, 目标, 底) 一般的定理, 不按项拆.

## 4. 会不会掉值
- 回退行 (`YiTBRow.ψ` 末行 `dW … nothing` ⇒ `ψ x ⊞ ψ₀(y)`): sΩ 形层号, 目标经指定孩子 c′, 嵌入在孩子 c, 表 `rbᶻ` 只在字面 zero 时有条目. 它在 (a) 上折 `Up` 产生的孩子内槽位 (`mv`) 回灌时, (b) `inu` 行给孩子传继承底 B′ = 折 x 且 x 含别的孩子的嵌入时 触发. 这里相对理想值掉值 (把别的孩子的 Ω_{h c} 折到可数再加). 判断: 纯 Ω 嵌套的参照项 (EBOψ n 及其基本列, 没有和) 的下界可以只走 x = zero 的行与链的第 1 个点 (z₁ ≥ β), 不经回退行, 所以回退行不必然挡住 EBO 下界; 但任何需要内链第 2 点以后的精确值的论证会碰到它.
- 站的对位有一层余量 (纸面): tw 1 的层号值 Ω₁, tw 2 是 sup_{c ∈ Tr (tw 1)} = Ω_{Ω₁+1}, 所以语义上 twc 1 已是 ψ₀(Ω_{Ω₁}) (对角链 c ↦ ψ₀(Ω_c) 与 row 2 的 γ-链逐项同形), twc 2 ≥ row 3. 现行 Kᴱ n 用 tw n 对 row n, 松一层. 这不是掉值, 但说明第 3 站缺的不是强度, 是证明手段; 也给出一个更贴的对位 (row (n+1) 对 twc n) 可试.
- 真正可能掉值的地方我判断只有回退行与继承底; 封存时不能排除 sL 形层号上 `way`/`emb` 行对部分和下标的行为有问题 (未查).

## 5. 能否到 EBO
判断 "存疑, 偏可行": 定义本身 (EBOᶻ) 语义上不低于 EBO 的理由是上面的纯嵌套路线不经回退行; 没有编译依据. 到 EBO 的证明量取决于下标保持能否写成一条与站无关的定理; 若只能按站、按项、按颈结点形状逐条做, 则走不完 (每站新增形状).
```

#### 2. 对照之后: 与主审判断的异同

##### 2.0 先说两条对照后确认的事实

**(a) 站的对位松一层, 且已被现有定理证实 (n = 1).** 【定理】`YiPCKeel.k1-value : (h : E.HC (E.EBOψ 2)) → Rt h ≼ readRW (twᶻ 1)` —— 第 1 站的对象已不低于第 2 站的参照. 【定理, 读代码】`YiFRStations.k2` 的证明是 `row₂-btbo`, `btbo-br1ᶻ`, `rr≼ (brᶻ 1)`, `station-step 1` 的传递: 第 2 站 = 第 1 支的 BTBO 下界加站间单调, `tw 2` 的折叠没有贡献新值. 龙骨读法 `kt n` 把 `tw 1` 读作 1 (`YiCNKeel.LeafAt`), 而 `YiCNTw1` 文首写明 `tw 1` 可读到 Ω₁. 【判断】语义上 `twᶻ 2` 已不低于第 3 站的参照 ψ₀(Ω_{Ω_Ω}); 第 3 站缺的是证明手段, 不是定义的强度.

**(b) 整体引理的条件定理早已存在, 主线第 46 批以后离开了它.** 【定理】`YiGIEnd.eboᵍ : Leaf → Lift → LowKeep → ExitCondition → toL EBO-tree′ ≼ readRW EBOᶻ`; `YiNLKeel` 文首: 龙骨的 Leaf/Lift 已实填, `ebo-from-low` 只剩 `LowRest`. 所以终点前的唯一数学缺口是 "第 3 站起的 `LowAt n`", 展开后就是读回域上 (链点孩子层号, 不只是龙骨) 的 Leaf 加 LowKeep. 第 61 到 69 批的 `BranchNeed`, `Step`, `Need`, `Narrow`, `NextSlot`, `SlotLaw`, `Lift₁/Lift₂`, `MinimalGoal`, `FirstRow`, `RowOneAtTwo` 都是它在具体对象上的实例或半成品.

##### 2.1 问 (1): "第 1 项的缺口是 BranchNeed, 再压到 '可数层号上的 Leaf, 目标第 1 层'"

**同意前半, 对后半有三点异议.**

- 同意: `YiC1Slot.BranchNeed = ∀ η d → K.M⁰ η d → H.M 1 (E.fsT N.slot η) (branch d)` 正是封存计划里的 (P1a); 压到 "可数层号 `two ⊕ ↑ zero (suc d)` 上的 Ω 树折到第 1 层" 也对 (`YiBVSmall.child`).
- 异议一, `Step` 的归纳形状不对 (判断): `YiQLRead.Step` 从 `Need (pred η) d` (折叠后的结论) 推 `Need η (suc d)`. 后继层号的证明要用的是折叠前的源关系 (孩子层号上的 Leaf), 归纳假设用不上; `YiSQPremise`, `YiOPCountable.no-omega-seed` 的受阻与此相符. 正确的归纳是对 `Rd` / `Corr` (层号读法) 归纳并携带 Leaf. `YiGCChosen.all-lower`【定理】在 `Align.Level` 参照下就是这样对一切 d 做成的, 所以这条引理的数学内容已有, 剩下的是参照不同.
- 异议二, `Narrow` 不是 "与第 0 层语义反射同类" (判断, 存疑): `YiGCBridge.Narrow` 要从 Level 参照的 `R.Rel K.one` 加 `M⁰ η d` 得到 `H.M 1 (Q.Target η) …`. 第 0 层没有 Ω 结点, 值序与结构关系可互推 (`CS.sem→M⁰`). 第 1 层有 Ω 结点: `M` 的放宽只沿第一位置序 (`Weak` 用 `◃`, Ω 结点处只有第 0 分支), 值序 `YiVWVal._≼_` 的 `≼Ω z` 对任意分支. 从值到 `M 1` 的反射在 Ω 结点处没有现成的规则, 而且 "任意分支放宽" 对折到第 0 层不可靠 (见 2.3 的反例构造). 所以 `Narrow` 的难度不低于 `BranchNeed` 本身; 它是两套参照并存造成的缺口, 不是数学必需的缺口.
- 异议三, 量化域: `BranchNeed` 对一切可数 (η, d) 陈述, 是对的一般性; 但它只是目标第 1 层、偏移 `two`、孩子来自第 0 层这一格. 同一条引理在第 1 项的后半 (目标第 0 层, 偏移含 Ω 结点) 与第 3 站 (偏移 `tw 2`, 继承底) 还要再证. 应写成对 (偏移 A, 下标层 k, 目标 j, 底) 一般的一条.

##### 2.2 问 (2): "更深颈结点的律" 是不是第二个缺口, `YiDNNoOmega` 意味着什么

**不是第二条独立的缺口, 是同一条引理的下一个实例; `YiDNNoOmega` 是基数上的平凡事实.**

- `YiDNNoOmega.no-offset-slot : ∀ k → VR.NoΩ k → GR.Rd k N.slot → ⊥`【定理】只说: 没有 Ω 形状的层号读法低于 Ω₁ (`YiCNTw1.rdC-bound`), 而 slot = ψ₁(Ω_Ω) ≥ Ω₁. 它排除的是一个本来就不该有的简化 (把 chain 2 的读回当作 NoΩ 层号), 不提供新信息, 也不否定目标. 主审读作 "只否定证法前提" 是对的.
- 【定理, 读代码】`YiDNRequests.value→law d r v _ = v`, `law→value d r law = law tt`: `SlotLaw` 与 `SlotValue` (即要证的值界本身) 互推是恒等. `YiNIIface.Law` 对单个请求没有归约内容, "精确写出更深颈结点的律" 等于把目标换了个名字.
- 第 1 项后半真正要的 (判断): `NextSlot` (= `H.M 1 slot (chain 2)`) ⇒ Lift (`Rd (↑ one (chain 2)) slot`) ⇒ 层号 `two ⊕ ↑ one (suc (chain 2))` 上的 Leaf ⇒ 折到第 0 层的 LowKeep. 那个层号是 sL 套部分和套 `sΩ zero` 的嵌套; 仍是 "读回域上的 Leaf 加 LowKeep", 只是形状从 NoΩ 换成含 `sΩ zero`.

##### 2.3 问 (3): 在干净对象上先攻是否值得, 结论能否搬回第 3 站

**作为方法的试验台值得; 作为垫脚石不成立, 现在搬不回去.**

- `ℓ₂ = two ⊕ ↑ two (Ωt two)` 不是任何 `tw n` 在链点处的孩子 (判断: `tw 2` 的孩子是 `tw 1 ⊕ ↑ c`, 前缀是 `tw 1` 不是 `two`; 对应的 c 也不是链点). 把干净对象的值界搬到主线, 需要两条都没有的树侧引理: (i) 折叠对底的单调 (标准底换继承底); (ii) 折叠对层号下标的单调.
- (ii) 以值序为前提的全称版本不成立 (判断, 纸面反例, 未编译): 取 Ω 结点 g′, `g′ (suc c) = suc c`, `g′ (lim …) = 1`, `g′ zero = 1`. 它在 `YiVWVal` 的值序里与 `Ωt one` 互相 ≼ (值都是 Ω₁), 但对角链 e₁ = ε₀ (ℕ 极限), e₂ = 折 (g′ e₁) = 折 1 = e₁, 停住, 输出约 ε₀·ω; 而 `Ωt one` 作下标给 ψ₀(Ω_Ω). 所以 `YiM2Chain.i` (链点的树侧值不低于 Ω₂)【定理】本身推不出任何折叠值, 主审把它记作 "分解的前一半已证" 偏乐观: 后一半不能以值序为前提陈述, 只能以字面路径 (`⊑`, 由 `◃→⊑` 生成) 或关系为前提.
- 干净对象第 0 项 (`YiC0Accept.first-row`【定理】) 经旧块对应与 BTBO 得出, 值仍在 ψ₀(Ω_Ω) 档; 主审第二十四份已自行折半, 我同意.
- 更合适的干净对象见第 4 节推荐 2: `L* = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`. 它逐字是 `tw 2` 的孩子, 形状是 `sΩ zero`, 且 `Ωt (tw 1)` 严格低于 `tw 2` 的第 1 个链点 (纸面: 链点 1 是保留的 Ω 结点, 第 0 分支是 `next⁺ β`, β = `Ωt (tw 1)`), 所以有字面路径接回主线.

##### 2.4 问 (4): 路还有多长, 是否同一条引理反复出现, 是否该换成整体引理

**是同一条引理; 应当换.**

- 按现攻法的路 (判断): 里程碑第 1 项 → 里程碑一切项 (要 `BranchNeed` 与后半都是变量形式, 否则逐项) → T[0] → 第 3 站的 `Tail` (参照项 ψ₀(Ω_{Ω_{γ_m}}), γ_m 跑遍一条可数链, 下标层号的形状跑遍一切可数读回形状) → 一切站. 第 3 站本身就要求 "下标读回为任意可数序数的层号上的 Leaf 加 LowKeep", 即一般定理; 逐项永远到不了.
- 反复出现的证据 (读 LOG 与代码): 第 62 批 "孩子来自不可数层的 Ω 结点折到第 0 层值不掉"; 63 `NeckLow`; 64 `BranchNeed`, `Law`; 65 `MinimalGoal`; 66 `Need`/`Step`; 67 `SecondMissing`, `MissingReferenceBridge`; 68 `LFNode`, `MS`; 69 `Narrow`, `SlotLaw`, `ActualMissing`. 九批约 35 路, 主线已证的值从 ψ₀(Ω_Ω+ψ₁(Ω_ω)) 到同式加 1 (`YiOLBoost.strict-output`).
- 整体引理的形状在抽象接口里已经写好 (`YiAbsGIface` 的 `Leaf`, `Lift`, `LowKeep`, 量化域 `Doms`). 缺的是 (i) 量化域从龙骨扩到链点读回域; (ii) 关系 `R` 要容得下 ℕ 极限层号上 Ω 树是部分和这一事实 (`no-omega-seed`【定理】否定的是精确标签版); (iii) 不同步对 (`YiASIface.LowKeepAsync`, 有限层号上已证 `lowKeepAsyncᶠ`【定理】) 推到非有限层号.

#### 3. 缺口清单

| # | 缺口 | 精确陈述或名字 | 档 |
|---|---|---|---|
| G1 | 终点唯一的数学缺口 | `YiNLKeel` 的 `LowRest` (第 3 站起的 `YiCNKeel.LowAt n`); 等价于 `∀ n → Kᴱ n` (`YiS1Accept.ebo-from-stations`) | 未证; 条件定理已编译 |
| G2 | G1 展开后的一般引理 | 读回域上的 Leaf 加 LowKeep: 对层号 A ⊕ ↑ k d (d 带读回证据), 一切出现的目标 j 与底, `R j (ψ_j(…Ω_ν)) (ψ … (Ωt (A ⊕ ↑ k d)))`. 现有实例: 有限层号 (`YiASProofLow.lowKeepᶠ`, `YiTBFam.sΩ-LF`), NoΩ 层号在 Level 参照下 (`YiGCChosen.all-lower`), 龙骨 Leaf/Lift | 未证; 判断 "这是唯一的一条" |
| G3 | 树侧: 折叠对底与对字面路径的单调 | 对 `◃→⊑` 生成的路径 ℓ ⊑ ℓ′ 与逐点不低的底, `readRW (ψ₀ᶻ-折 (Ωt ℓ)) ≼ readRW (… (Ωt ℓ′))`. 现有: `YiOGFirst.prefix-one` (前缀 1); n ≥ 2 即 `YiOFLocal.ActualMissing` 未构造 | 未证 |
| G4 | 第 1 项前半 | `YiC1Slot.BranchNeed`; 现归到 `YiGCBridge.Narrow` (未构造) 或 `YiQLRead.Step` (未构造; 判断: 归纳形状不对) | 未证 |
| G5 | 第 1 项后半 | `YiC0Next.RowOneAtTwo`, 经 `NextSlot`; `YiDNRequests.SlotValue` (与 `SlotLaw` 恒等互推) | 未证 |
| G6 | 接线的工程墙 | `kept` 同一性 8G 耗尽三次 (`YiC1Slot`, `YiWXCheck`, `YiWYCut`) | 工程; 若 G2 以变量形式证则不需要 |
| G7 | 值序不能作下标单调的前提 | 2.3 的 g′ 反例 | 判断 (纸面, 未编译); 旧系统上同型定理 `Align.Value.ψ⁰-not-cong` |
| G8 | 回退行的掉值范围 | `YiTBRow.ψ` 末行 `dW … nothing ⇒ ψ x ⊞ ψ₀ y`; 我判断纯嵌套参照项的下界不经它 | 判断, 没有上界也没有否定 |
| G9 | `Narrow` 是否可证 | Level 参照的第 1 层关系到 `H.M 1` 的反射 | 存疑 (判断) |

没有任何一条我认为 "走不通"; 都写作未证或存疑.

#### 4. 推荐的下一步 (按优先级)

**推荐 1 (整体改法): 停掉具体链点上的逐项与接线 (停工, 不是否定), 把 G2 写成一条定理并只用变量形式证.**
- 目的: 一次得到 `BranchNeed`, 更深颈结点, T[0], 第 3 站 `Tail` 的共同来源; 接到已有的 `YiGIEnd.eboᵍ`.
- 做法: 对层号读法 (`Rd`, 或 YiGC 的 `Corr` 推广到含 `sΩ zero` 的形状) 归纳, 归纳携带源关系 (Leaf), 不携带折叠后的结论; 三个目标 (低于, 同层保留, 自身) 各一条, 写进 `YiAbsGIface` 的 `Doms` (量化域取链点读回域).
- 为何优先: G4, G5, G6 都是它的实例; 逐项攻九批没有越过第 1 项; 变量形式顺带消掉 `kept` 的堆墙.
- 难点: 关系 `R` 在 sL 层号上要接受 "Ω 树是部分和" (避开 `no-omega-seed` 的精确标签前提); 不同步对推到非有限层号; 参照只能留一套 (见推荐 3).

**推荐 2 (对位调整, 可与 1 并行): 把第 3 站改在同步的对象上证.**
- 对象: `L* = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`. 【本路编译】`AuditASync`: `is-child : L* ≡ FR.Step.child 1 c*`, `shape : L* ≡ nd (sΩ zero) a*`, `row* : collapse (L*, …) (Ωt zero) ≡ limc⁺ (λ n → In.out (In.chain n))`, 其中 `In.chain : ℕ → Tr zero`.
- 含义: `L*` 的 Ω 树折到第 0 层是第 0 层上的对角链, 与 row 3 = ψ₀(Ω_{Ω_Ω}) 的 γ-链 (γ_{m+1} = ψ₀(Ω_{Ω_{γ_m}}), 可数) 同步; 没有继承底, 没有不可数层上的回灌链. 现行 `Step 2` 在 `tw 3` 上, 链在 `Tr (tw 2)`, 对着可数的 γ-链是不同步对, 多一层展开.
- 目标陈述 (判断): `∀ γ e → M⁰ γ e → ψ₀(Ω_{Ω_γ}) 的树 ≼ readRW (折 (Ωt (a* e)))`; γ = 2 的实例就是里程碑 (前缀 `tw 1` 代替 `two`). 再用推荐 4 的路径单调接到 `twᶻ 2`, 由 `station-step` 到一切更高的站. 一般地试 `Kᴱ′ n : row (n+1) ≼ twᶻ n`; n = 1 已是定理 `k1-value`.
- 为何好: 把 "第 3 站" 的顶层从不同步对换成与第 2 站同型的颈结点 (孩子来自第 0 层), 那一型已有两次成功 (`k1-value`, `YiC0Accept`).
- 难点: 孩子层号 `a* e` 对后继 e 是 `sΩ (↑e′)` 形状, 内部仍要 G2; 这一步不省 G2, 只省一层与继承底. 我没有查主线是否已考虑过这个对位 (见第 6 节).

**推荐 3: 参照只留一套, 不造 `Narrow`.**
- 二选一: (a) 在 EboLean 的 `M` 族里直接重做 YiGC 的沿帧主引理 (`YiGCFold` 的 `MS` 换参照); (b) 一次性证 Level 参照与记号树在所需范围内的值比较, 之后验收全用 Level 参照 (AGENTS: "终点先证主线树的序数值不低于 EBO 的参照树").
- 为何: `Narrow` 是第 1 层的语义反射, 第一位置放宽与值序的任意分支不对应 (2.1 异议二); 每升一层都要再造一座.
- 难点: (a) 要重设计 `M` 在 sL 层号上的规则; (b) Level 参照是否够得到 EBO 我没有查.

**推荐 4 (摆脱侧, 与 1 配对): 把 YiOG 这条线升成一般定理, 并配对否定.**
- 构造: G3 (对 `◃→⊑` 路径与底的单调), 对路径归纳, 不读记号; 目前只有前缀 1.
- 否定: 把 2.3 的 g′ 反例编成定理 (值序前提下下标单调不成立), 划定量化域必须是字面路径或关系, 不是值序. 这同时回答 `YiM2Chain.i` 一类树侧值下界能不能用.
- 难点: 对底的单调需要内链上 G 的单调, 是互递归; 高层要用 `YiVWVal` 的值序陈述, 可能撞堆.

#### 5. 我编译过的文件

- 路径: `<实验目录>/audit/A/AuditASync.agda` (SHA-256 `3aa302950dddaddeb1925db9c910527cda2debb13c30ff3de4ee0440dffb3e90`); 日志同目录 `AuditASync.agda.log`.
- 退出码: 0 (8G, 仓库根目录, 简报给的命令; 日志只有本文件的 Checking 行, 没有重编仓库模块). 无 postulate、洞、TERMINATING、K.
- 陈述:
  - `is-child : L* ≡ FR.Step.child 1 c*` (c* = `proj₁ (Ωt (tw 1))`, L* = `tw 1 ⊕ ↑ (tw 1) c*`);
  - `shape : L* ≡ nd (sΩ zero) a*`, `a* e = tw 1 ⊕ (zero ⊕ ↑ (zero ⊕ ↑ zero e) (proj₁ (Ωt (zero ⊕ ↑ zero e))))`;
  - `o* : Ok L*` (= `proj₂ (Ok-tw 2) c*`);
  - `row* : Q.collapse (L* , o* , rbᶻ L* , B₀ L*) (Ωt zero) ≡ limc⁺ (λ n → In.out (In.chain n))`, `In = YiE4Inner.Inner zero a* o* (rbᶻ L*) (B₀ L*) (Ωt zero)`.
- 这是形状事实 (三条 `refl` 加一次已有引理的实例化), 不是值界; 它支持推荐 2 的 "同步" 说法, 不支持任何强度结论.

#### 6. 没有读、只凭转述引用的东西

- 回报原文 (`Reports-*`), `IdeaLedger.md`, `GoalOdds.md` 全未读. `RouteReview3.md` 只读了末尾 60 行 (内容是第 6 节与较早的裁决记录, 没有第 61 批以后的行). `RESULTS.md` 末尾 15 行是工具说明, 没有结果行. `README.md` 只读了 "当前阶段" 一段的前 2KB.
- LOG 中 Codex 统筹的条目 (第 62 到 69 批的 "作者验收…启动") 未读, 只读了主审的复核条目.
- 只读文首或签名, 没有读证明的: `YiGCFold`, `YiGCChosen`, `YiGCRel`, `YiGCSlots`, `YiGCFrames`, `YiGCCorr`, `YiGCOmega`, `YiFPFrames`, `YiFPFinite`, `YiFPReadback`, `YiSQNat`, `YiSQOmega`, `YiSQPremise`, `YiOPCountable`, `YiKWObjects`, `YiWYCut`, `YiOGFirst` (YiOG 其余九件未开), `YiNIIface`, `YiNISuff`, `YiRXOmegaHead`, `YiQLRead`, `YiC0Accept`, `YiC0Reduce`, `YiC0Connect`, `YiOLBoost`, `YiOLMilestone`, `YiUTTwoLocal`, `YiM2Chain`, `YiTBFam`, `YiNLKeel`, `YiCNKeel`, `YiASProofLow`, `YiLSFold`, `YiAbsGSuff`, `YiExSuff`. 凡引用它们的定理, 依据是文首判决、签名检索与主审 LOG 的 "读过的陈述", 我没有重编.
- 第六十九批四路是否冷编通过, 依 LOG 末条 (22 件退出 0), 我没有复核.
- `YiCompatDlLPO.lpo-tw`, `YiLLLeafNeg.noLeaf`, `YiMXNote.¬Mono`: 读了陈述与文首. `¬Mono` 否定的是记号一侧非标准形项的项序单调, 不是树侧折叠的跨层单调; 主审第六十三批派前核对把它记作 "一般跨层单调的否定", 这个归类按 AGENTS "归到已知的墙要逐条核机制" 应更正. `lpo-tw` 针对旧折叠的 `Compat` 接口, 不针对 `YiTBRow.ψ`.
- 2.0(a) 的 "语义上 `twᶻ 2` 不低于 row 3"、2.3 的反例、推荐 2 里 "`Ωt (tw 1)` 严格低于 `tw 2` 的链点 1" 都是纸面推演, 没有编译.
- 推荐 2 的对位是否已在台账或更早批次里被试过或搁下, 我没有查 (台账未读); 请主审查重后再派.
