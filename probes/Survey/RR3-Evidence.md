# RR3-Evidence: 证据与投入审计 (2026-11-01 至 11-08)

> 独立审查, 2026-11-08, Fable 5.1, 本路名 RR3-Evidence. 与 RR3-Design, RR3-Backward 互不看结论.
> **固定的东西只有 AGENTS 纲领四条与终点** (布劳威尔树写出 ψ₀Λ 的合法闭项, 有 FGH, 序数值至少 EBO). 其余一切 (目标 "让树自足", 最佳实践, 1513 标杆, 验收档位, 作者历次决定, 封存, 各审查结论) 本文都当数据.
>
> **档位.** [定理] = 编译过的陈述 (本文抽查的四件在本次重新编译, 退出码 0: `SkelDxGen`, `TotalValueHighOmega`, `TotalValueNegStrictAudit`, `Review2Blind`, `StallDxBdec`); [统计] = 从 git 与文件计数得到的数字, 脚本见文末; [判断] = 纸面. 穷尽一律是判断. 强度写 ψ₀(Ω_x), x 用 Ω 的算术.
>
> **读了什么.** `AGENTS.md`; `probes/README.md`, `RESULTS.md` (成果表、翻译账、否定索引), `LOG.md` (全部标题, 11-04 至 11-08 的作者裁定与收尾条目), `HANDOFF-2026-11-07.md` (接手起止与作者两次纠偏); `Survey/` 的 `ResearchHistory`, `RouteReview`, `RouteReview2`, `RouteSeal`, `StallDiagnosis`, `SkeletonAudit`, `ClosedTermReview`, `Stage-2026-11-06`, `EBOEndgame`, `EBOHandbook` §6-§8; 主会话记忆里作者决定的 11 个文件; `git log` 23 个提交的 numstat; 本文 §4 列出的否定定理与 §5 列出的值定理的 Agda 陈述原文.

## 0 结论先行

1. **[统计] 树侧序数值的前沿自 11-04 起没有动.** 编译过、无条件、树侧 (定义与证书不引用记号) 的最高值定理是 `EmbVVInstO2.vv-ω²` (ψ₀(Ω_{Ω·ω²}), 11-04 提交 a5b202c). 之后四天 (a5b202c → 5a5846e) 新增约 43 万行、2500 余个文件, 没有一条树侧值定理超过它. 11-05 以后新交的值定理全在它之下: `SumOneAccept.step-T₁` (严格高于 ψ₀(Ω_Ω), 11-04), `GridBaseTowerAccept.epsilon-in-grid` (ε₀), 11-07 新候选的 ψ₀(Ω_ω) 与 ψ₀(Ω₂) 下界, `TotalValueHighOmega.omega-lower` (ψ₀(Ω_Ω)+ω). 这就是 "打转" 的可核对形式: **投入曲线在涨, 值曲线是平的**.
2. **[判断] 打转的位置不是某一条路线, 而是三个被反复改名的障碍**, 每个都有定理把它钉住, 但派发时都没把定理当设计约束: (W) 对不带公共上界的下标判等或判序 ⇒ LPO/WLPO 一族; (V) 折叠不是值的函数, 所以值证明只能模拟真实轨道; (C) 把高层信息坍缩到固定类型或有损读回, 使读法封顶. 详见 §2.
3. **[判断] 打转的原因主要是方法, 不是数学.** (a) 闭项用 "合法性由形状给出" 便宜地写出, 值证明昂贵且被推迟, 于是 "读法" 成了通货; (b) 11-04 以翻译成本的估计 (这类估计历史上偏低 3-5 倍或从未写出, 手册 §7) 封存了唯一有高值定理的族, 之后的候选都从更低的站重算第 4 层; (c) 1513 标杆与 "让树自足" 都不与值挂钩, 却被当作停投与选路的依据; (d) 构造否定配对与一天百余路的并行, 产出大量 "接口未被否定"; (e) 11-06/07 的接手没有先查前沿, 作者两次纠偏.
4. **应当停止的** (§6): 没有值下界的新闭项; 1513 压缩; 以 "读法" 命名的站; 接口否定作为交付; 裸下标世界的新架构; 共享未证引理的多路并行.
5. **有前进证据的** (§6): 带高度族 (EmbVV/LadderOrd/CrossM) 的值阶梯与它的下一站 ψ₀(Ω_{Ω²}) (T⊤ 的读法, 尚无定理); 差树 `SumOne` 的上界问题 (检验新定义风格能否做第 4 层的最便宜实验); `TotalValue` 的轨道模拟机制 (作为方法, 不作为对象); 终点接口 `TerminalFoldAccept`. 继续投入的判据只有一条可核对的: **每轮报告树侧候选的 max x 使 ψ₀(Ω_x) ≼ 候选 是编译过的无条件定理; 不超过上一轮的路线暂停.**

## 1 按时间整理的方向族

### 1.1 总量

[统计] 2026-11-01 至 11-08: 23 个提交; `probes/` 下 3041 个 `.lagda.md` (Align 2448, Lean 474, Free 79, 其余 40), agda 代码块非空非注释行 393,122 (原始行 569,660). 按提交: a5b202c (11-04) +203,039 行 788 文件; 0546568 (11-06) +171,030 行 990 文件; 5a5846e (11-08) +59,155 行 788 文件. `LOG.md` 以 "## 2026-11-dd" 开头的条目: 11-03 15, 11-04 67, 11-05 136, 11-06 30, 11-07 43 (11-06 起另有大量不按路命名的滚动条目). 判决词统计: PARTIAL 115, 未走通 43, 暂停 32, HOLDS 17, BLOCKED 2. 名含 `Neg` 的文件 351 (以 `Neg` 开头 213).

### 1.2 方向族表

每行: 时段; 投入 (文件/代码行, [统计], 按文件名前缀聚合, 有误差); 产出 (只计编译过的); 终止方式. 读法一律不计入产出.

| # | 方向族 (前缀) | 时段 | 投入 | 编译过的产出 | 终止方式 |
|---|---|---|---|---|---|
| 1 | 壁垒与 BTBO 校准 (`Barrier`, `BTBOVal`, `BTBOFull`, `Cumsum`, `NoCum`) | 11-01 至 11-04 | B 23/3366, No 40/5670, Cum 37/7267 | `Barrier.barrier` (Ω-Extension → LPO); `BTBOFull.BTBO≈` (成品 BTBO 经 tr₀ 与 ψ₀(Ω_Ω) 参照互相 ≼, 无条件); `Cumsum.overshoot` | 完成; 成为基座 |
| 2 | 标签阶梯 (`Uniform*`, `Stage2`, `Scaf`, `Omega*`, `Standard`, `Pending`, `Verdict`, `OCFSpec`) | 11-02 至 11-03 | Uniform 112/25597, Uniform2-5 47/9811, Scaf 70/21984, 其余约 8000 | 标签 (`Lab`) 定理到 ψ₀(Ω_{Ω·2}), ψ₀(Ω_{Ω+1}); `Value.ψ⁰-not-cong`; `Lab≅tree` (11-03) | 作者 11-03 转向记号无关; `Lab≅tree` 说过 `Lab` 的树 ≅ 记号翻译 |
| 3 | I 层 / 奇异下标 (`Inacc*`) | 11-02 至 11-03 | 46/6098 | `Trich₂→WLPO`, `noBT`, `allReg→WLPO` (条件 FE) | Fable 11-03 审核 "未否定, 不值得继续" |
| 4 | 记号无关证书 (`OCF/Free`, `Level*`, `LevelFix`, `LevelNoK`, `Lv*`) | 11-03 | Free 79 文件; Level 35/7621; Lv 90/12603 | `Free.Closed` ψ₀(Ω_{Ω·2}) 的干净证书; `LF` 含一切层号到 Λ 的类型 (无序数闭项) | `LevelFix` 封存 (第一个障碍在 ψ₀(Ω_Ω) 的证书); Free 成为资产 |
| 5 | 不带高度的树 (`Guard*`, `WeakBridge`, `Tight*`, `TreeJudge`, `ValueJudge`) | 11-03 至 11-04 | Guard 44/9201, Weak 14/1923, Tight 9/1001, Tree/Value 约 60/7000 | `WeakBridgeMain.Good-θ` (一切 Ω+θ); 判据的盲定理 (`rows-blind`, `reg-blind`) | 封存 (11-04); 判据 "能验收不能写出" |
| 6 | **带高度的树** (`LadderNF/Mono/Inf/Ord`, `CrossM`, `CrossNext`, `OrdLab`, `ValLab`, `EmbVV`, `TLOne/Code/Ops`) | 11-03 至 11-04 | Ladder 276/65375, Ord 62/9570, Emb 50/10122, Cross 25/2316, T 73/8769; 其中克隆脚本生成占大半 | 闭包定理对一切 `HtB`/`Node` 一步; 闭项 `T⊤`, `T-feed` 带 FGH; 标签到 ψ₀(Ω_{Ω·ω}) (`OrdLabAccept`); **`EmbVVInstO2.vv-ω²`: ψ₀(Ω_{Ω·ω²}) 序数值验收 (树侧最高)**; `same-M₂`/`no-lab-M₂` (树有自己的基本列) | **作者 11-04 封存** (理由: 翻译形态; `CrossNext` α≥1 估计 1 万行). 不是定理否定 |
| 7 | 累加之争 (`CumRead/Up/Val/Ht`, `Om1Cum/Hn`, `WorldTH`, `NoCumHn/Node`, `CtxMono`, `AddClo`) | 11-04 | Cum 37/7267, Om1 13/1250, World 11/2627 (部分), Add 10/1299 | `NoCumNodeMain.G₁` ψ₀(Ω_{Ω+1}) 无累加证书; `Om1CumGrow.step-Ω+1`; `no-clo-·2`, `no-clo-+1` | 封存 (11-04); 作者先 "全去", 后 "看综合账"; Ω+1 上界未走通 |
| 8 | **差树** (`TLRule`, `SumOne`, `SumHt/Climb/Var`, `DVal`, `L1Val`, `Cv*`, `LayerTr`, `BrwMid/High`) | 11-04 | Sum 24/3750, D 8/1028, Cv 10/975, Brw 25/1968, Layer 7/532 | `TLRuleAccept.T≈` (ψ₀(Ω_Ω)); **`SumOneAccept.step-T₁` (严格 > BTBO)**; `Lg-sum` (合法由形状); `SupBlk` | 主线 (作者 11-04 定); 坐标写法封存; Ω+1 上界卡在 "跨树互模拟" (估计三次未写) |
| 9 | **高度树** (`HtFeed`, `HtOut`, `HtTotal`, `HtCross/V`, `KVal*`, `EndLow*`, `MonoPort1-9`, `KNest`, `MainView`, `BrwView/Wf/HW`) | 11-04 至 11-05 | Ht 58/5266, Mono 49/5572, K 25/1911, End 7/450, Main 6/820 | `HtFeedGrow.Sup`, `HtOut.Fb` (高度由输出生成), `no-glob`, `no-world-top`, `drop-lim/suc`; `MonoPort9Cov.allBelow` (限定域); `MainViewZero` 第 0 层 View | **零值定理** (RouteReview2 R5); `EndLowT` 未走通后 "作者定不改定义"; MonoStep 未证未否 |
| 10 | 下标塔类型层 (`HtTower/F/N`, `LFRe`, `CohW/2`, `DiagK1-4`, `TelW`, `ChainZ`, `UniTr`) | 11-05 | Ht (含上行) + Coh 11/931 + Diag 14/729 + 约 20 文件 | `cmpB` 对一切 S; `Lg-Λᵁ`; `no-retract`, `no-naive-diag`, `no-wmatch`; `upd→wdec`, `raise-Lc→WLPO` (FE); `Tdg₂` 闭项 | 六路 "未走通" → `StallDiagnosis` (裸下标律); `StallDxBdec.bdec` 反例穷尽判断 |
| 11 | 配对派发第一批 (`AdmW/Ev`, `EvW`, `ColimA/W`, `LocUip`, `FamFold`, `EvFold`, `LvFb`, `StrRel1-19`, `TpMono/Port`) | 11-05 | Str 108/8715, Adm 16/1570, Colim 17/1676, Fam 12/1348, Ev 14/1789, Tp 35/3686 | `FamFold` 全 n 闭项; `EvFold` 闭项; `ColimARaise.raiseA′`; 拷贝墙 `AdmWNeg`; `no-valmonoT⁺` | 多为 PARTIAL/接口未被否定; 无值定理 |
| 12 | 骨架塔 (`LvRd/Top/Kt`, `KcFold`, `DnFold`, `GenFold`, `NewTwr`, `RaiseC`, `KindLv`, `StratTw`, `Slot`, `RsOwn`, `SLFb`) | 11-05 (一天) | Lv (含上行), Kc 10/655, Dn 14/1141, Gen 21/2411, New 14/879, Raise 12/1094, Kind 16/1241, Strat 10/791, Slot 10/749, Rs 11/1033 | 八个闭项全部 `≡ T⁺ h`, h : Ht (`SkelDxGen.fac-*`, refl, 本次重编 0); `ht-coords` | `SkeletonAudit`: 类型封顶 ψ₀(Ω_{Ω₃}) 量级 (判断); C6 未解 |
| 13 | 树的语言与标杆 (`TreeLang`, `TL2`, `EboLean1-3`, `WfFsn/TauNF`) | 11-05 | Tree (部分), Ebo 21/2090, Wf 10/1350 | `WfFsn.fgh-EBO` (记号侧 EBO 良基, 第 3 层); `EboLean3` 1513; `TreeLang.least`, `all4`/`blind-final` | 判据 "能验收不能写出" (NegTL2) |
| 14 | **C 线: 带类型折叠与压缩** (`Fab3Typed`, `TySup`, `LeanT/Fb/Lv`, `Fab4LOm`, `LamIso`, `PathOut`, `X1Up`, `X2`, `CRw`, `RecB`, `LHRec`, `Third`, `Fab6`, `Fold1`, `NoAcc`, `SameV`, `ValC/X/W`) | 11-05 至 11-06 | Lean 38/3895, Val(Lean) 36/3682, Third 30/2775, Same 16/1541, Fab6 10/1396, C 11/1332, Rec 9/914, L 10/702, Fold1 11/1010, X1/X2 22/1933, Path 11/1104, Lam 15/1170 | 闭项 `RecB.Tω`, `Third.TΛ` 合法带 FGH; `SameV.goal` (条件 Funext); 否定 `shape-bound`, `tu-block`, `acc-not-mono≤` | `Stage-2026-11-06`: "所有读法没有值定理" (C 线); 读法每升一档行数上涨 (402→504→696→817→1049) |
| 15 | 独立接手第一段 (`World*`, `Tower*`, `Lambda*`, `Sup*`, `Frozen*`) | 11-06 至 11-07 | World 11/2627 (部分), Tower/Lambda/Sup/Frozen 约 50 文件 | 值为 ω 的闭项; `ω²≤T`; `LambdaCollapseNoTypeBound` | 作者 11-07 纠偏 "从 BTBO 继续, 不重建低基线" |
| 16 | 独立接手第二段 (`General*`, `Bounded*`, `Countable*`, `Higher*`, `Rebase*`) | 11-07 | General 206/8551 (Align+Lean), Bounded 197/8910, Higher 31/1609, Rebase 20/1158 | 新候选 ψ₀(Ω_ω) 下界, 后 ψ₀(Ω₂) 下界 (验收含记号); Γ 的同形保持 | 作者 11-07 第二次纠偏 "先调查旧高结果"; 停止新构造, 转历史整理 |
| 17 | 接续前沿的局部修复 (`ThirdRichLeg`, `EventReturn/Generated`, `UniformCore`, `Circuit*`) | 11-07 | Event 35/1635, Uniform (新) 17 文件, Circuit 13/627, Third (新) 12 文件 | `Full` 输出域; `no-generic-transport`, `no-floor`; `UniformCore` 结构定理 | "没有新增具名强度" (README) |
| 18 | 作者指定双路 (`TLambdaAudit`, `OutputDriven`, `Grid*`) | 11-07 | Output 10 文件, Grid 8 文件 | `OutputDriven.closed/closedGrid` 合法带 FGH; `no-rank-upper`; `epsilon-in-grid` (ε₀) | 暂停扩建, 转值审查; 无 BTBO 下界 |
| 19 | 定向简化 (`DirectedView*`, `DirectedPrefix*`, `TreeEmit*`) | 11-07 | Directed 11 文件, Tree (新) 7 文件 | `full-EBO` (记号侧改写保值, 切片 1500→1420); `closed-value` (TreeEmit 保 ψ₀(Ω_{Ω·ω²}), 依赖 +132); `NegReverse`, `NegMono` | 记号侧改写不是树侧; TreeEmit 不计压缩 |
| 20 | **改值简化** (`TotalOrbit*`, `Radical*`, `TotalValue*` 98 件) | 11-07 至 11-08 | Total 103/5719 + Radical/Orbit 约 15 文件 | `RadicalValueNativeFinal.closed` (切片 1418, 带第一位置 View, FGH); **`omega-lower`: ψ₀(Ω_Ω)+ω ≼ closed; `not-btbo-upper`** (本次重编 0) | 当前阶段; 准确值、旧 ψ₀(Ω_{Ω·ω²}) 下界、上界均未证 |

### 1.3 从这张表能读出什么 [判断]

- **值的阶梯只有四级, 全部在 11-04 当天或之前写成**: ψ₀(Ω_Ω) (BTBOFull), 严格高于它 (SumOne), 标签 ψ₀(Ω_{Ω·ω}) (OrdLabAccept), ψ₀(Ω_{Ω·ω²}) (EmbVV). 11-05 以后的 15 个方向族 (#10 至 #20, 约 2000 个文件) 对这架阶梯的贡献是零级. 11-07 的 `CrossMHighSeedAccept` 是旧定理串接, 11-07/08 的 `TotalValue` 回到了 EmbVV 的实例, 但把值从 ψ₀(Ω_{Ω·ω²}) 的定理降到了 ψ₀(Ω_Ω)+ω 的定理.
- **终止方式里 "定理否定" 几乎没有.** 20 族里没有一族是被编译过的否定定理关闭的 (符合规则); 关闭靠作者决定 (#6, #7, #8 坐标写法, #15, #16) 或换方向 (#10, #12, #14). 换方向的触发器都是 "读法到不了" 或 "行数接近标杆", 两者都不是定理.
- **投入最大的三族 (#6 Ladder 系 6.5 万行, #2 标签阶梯 5 万行, #16 独立接手 1.7 万行)** 里, 只有 #6 产出了值定理. #6 恰好是被封存的那一族.

## 2 同一障碍换名反复出现

### 2.1 障碍 W: 对不带公共上界的下标判等或判序

**定理形式.** `Barrier.barrier : Ω-Extension → LPO` (下标类型以 `Ordᴰ` 为精确初始段、含 Ω-共尾元、有有界三歧). 影子一族 (前提更弱, 结论更弱, 互不蕴含, `ClosedTermReview` §1.3): `Symbolic.Toy.loop`, `Uniform5Wall.¬tri`, `Stage2.dec→WLPO`, `InaccScout.Trich₂→WLPO` (11-02); `LvIRNeg.no-read`, `GuardReadNeg.no-cut`, `no-lim-cmp` (11-03); `LadderOrdNeg.no-tri-code`, `all-Ord→LPO`, `viewE→LPO`, `HtFeedNeg.no-glob`, `no-world-top`, `CumUpClean.dec⊲→LPO`, `TLCodeNeg.exact→LPO` (11-04); `DiagKLev.upd→wdec`, `CohWUpd.upd→wdec`, `CohW2Need.raise-Lc→WLPO` (FE), `ClosedReview1.find→dec`, `TelW.occ-find→dec`, `seeExact-sep`/`exact→WLPO` (FE) (11-05); `pos-dec→LPO`, `bd-dec→LPO`, `no-wash`, `upd→WLPO` (11-06); `BrwViewNeg.strict→LPO` (11-05). 约 25 条, 分布在每一天.

**每次绕它的办法与结果.** 11-01 交替路线 (对象层对角, 回灌作下标): 对; 11-04 高度树把比较限制在世界内 (`cmpH` 要字面公共上界): 对; 11-05 塔层 `cmpB` 对一切 S: 对. 但 11-05 六路把 "世界更新" 的律写在裸下标上, 重证六次 (`StallDiagnosis` §1); `StallDxBdec.bdec` [定理, 本次重编 0] 说在公共上界之下相等可判定, 所以各否定杀的只是 "对不可入下标也要律". 11-05 作者采纳 "律带公共上界" 后, 问题以拷贝墙 (`AdmWNeg`, `CohWNeg.no-cross`) 的形式回来: 同一坐标的两个证据给两个分量.

**性质 [判断].** 裸形式是数学障碍 (壁垒本身). 六路重证是方法问题: 已知的出路 (字面公共上界) 只用在了比较上, 没用在更新上; 且每路换律的形状不换律的定义域. 11-05 之后的拷贝墙是真障碍, 但只有一路 (`CohW`) 碰到并写成定理; 之后的骨架塔 (#12) 用基世界 `w0` 绕开它, 代价是 C6 (回灌进不了闭项) — 障碍 C 由此产生.

### 2.2 障碍 V: 折叠不是值的函数

**定理形式.** `Value.ψ⁰-not-cong : Ω₁ ≈ᵛ Ω₁′ × ¬ (ψ⁰ Ω₁ ≼ ψ⁰ Ω₁′)` (11-02). 同族: `Cumsum.ψᴱ-not-mono`, `Certified.ψ-not-⊑mono` (11-01/02); `OCFSpecNeg.Good-not-value-fragment`, `spec-blind` (11-03); `L1ValShape.¬Bis-mono`, `L1ValSup.¬mono-on-Mono`, `L1ValKappa.¬toB-mono-κ`, `DValNeg.¬assoc`, `¬κ-refl`, `LayerTrNeg.no-round`, `BTBOValAbsorb.ordᴰ-not-cong` (11-04); `TpPort2Tab.no-valmonoT⁺` (无条件), `Review2Blind.blindᴬ` (11-05, 本次重编 0); `acc-not-mono≤`, `col-acc`, `thr-not-mono`, `shape-bound` (11-06); `DirectedPrefixNegMono.no-unary-mono`, `no-unary-congruence`, `NegReverse.no-prefix-reverse`, `RadicalNegTotal.no-same-value`, `no-old-lower`, `TreeEmitNegValue.no-value-upper` (11-07). 约 20 条.

**每次绕它的办法与结果.** 11-02 值侦察 (`value-equality-verdict`) 已写明: ψ⁰ 对高层参数不尊重值, 值证明要替身与轨道, 第 4 层不降. 11-04 `CtxMono` 把 Ω+1 上界化成两个前提 (`Up`), 未证; 11-05 `HtCross`/`DVal`/`KVal`/`EndLow` 三路等同一条 `MonoStep` (RouteReview2 R2), 未证未否; `SameV` 以 Funext/UIP 为条件证 `TX+1 ≤ TU1`; `MonoPort1-9` 在限定域上证严格增长 (`allBelow`); 11-07 `TotalValue` 用 98 个模块做真实轨道模拟, 得到 ψ₀(Ω_Ω)+ω.

**性质 [判断].** 数学障碍, 而且是决定成本结构的那一个: 它意味着树侧第 4 层没有 "一般单调引理" 可用, 每个值定理都是对具体轨道的模拟. 已有证据: `LadderOrd` 第 4 层 21,490 行 (README 口径); `TotalValue` 98 件只得 BTBO+ω. 方法问题在于: 11-02 就有定理, 11-04 至 11-05 仍派三路去等 `MonoStep`; 11-07 又在新解释器上从 BTBO 重做一遍模拟. 没有一路把 "值证明对阶段参数化" (像 `GᴺTᵠ` 对 `HtB` 那样) 当作目标.

### 2.3 障碍 C: 坍缩到固定类型与有损读回

**定理形式 (refl 级的类型事实).** `SkelDxGen.fac-TG … fac-TΩ` (八个闭项 ≡ `T⁺ h`, h : Ht), `KcFoldTower.ht-coords`, `nc-old-drop`, `encH-bot`, `top-bot`, `dnG-hl-const`, `TG-lim-const` (11-05, 本次重编 0); `NegDnFoldRet.no-faithful` (到 Ht 的下降无左逆); `HtTowerNRead.toD₁` 值不忠实 (作者自注); `FamFoldOne.cast` 极限坐标给 0; `ThirdSan` 的 `er-drop`, `leg-const`, `slot-zero` (11-06); 11-07 `Consume` 把所有 Ω 统送 Cd (HANDOFF 复盘); `GenFoldK.evB` 落回 Ht; `GridValueIndex.index-step` (多轮更新只是追加固定增量).

**每次绕它的办法与结果.** `SkeletonAudit` §2 说类型条件 C1-C5, C7-C9 今天就能同时满足 (`SkelDxGen.TXΛ`), 只剩 C6 (世界不是基世界). 之后 `NewTwr`/`RaiseC`/`KindLv`/`StratTw`/`Slot` 攻 C6, 全部 PARTIAL; 11-06 C 线改带类型折叠, 读法到 ψ₀(Ω_{Ω·ω}) 止 (`Third` 三处损失); 11-07 `OutputDriven` 让输出更新整底世界, 但 `Er` 洗法与代表坐标仍在, 值只校准到 ε₀.

**性质 [判断].** 自我施加: 每条有损行都是某一路为了让程序全函数化、过停机检查、或 "接口定稿后只增不改" 而写下的类型决定, 下游继承. 没有定理说坍缩必须有损; 有定理说有损之后值不保 (`no-faithful`, `no-value-upper`). 它与 V 合起来解释了为什么 11-05 以后读法再高也没有值定理: 值定理要模拟轨道, 而轨道在有损行处断掉.

### 2.4 一个非障碍: "翻译 vs 自足"

`AccTreeLab.Lab≅tree : Lab X t → (h : Acc t) → X ≅ tree t h` [定理] 说过基本列验收的树 ≅ 记号的机械翻译. 这是对**验收规则**的定理, 不是对树的定理; 11-04 据此把序数值验收升主档是对的. 但之后 "翻译形态" 继续作为封存与换方向的理由 (#6, #8 坐标写法, `SumClimb` 判 "加深"), 而判据 (RouteReview §4.1 的 (a)-(f)) 没有一条可以编译. `TreeLang`/`TL2` [定理] 又证明现有树侧判据只能验收不能生成 (`all4`, `blind-final`). 所以 "自足" 在当前只有否定性内容. [判断] 它不是障碍, 是一个尚无可核对判据的目标, 被当成了选路的硬约束.

## 3 纲领之外的约束与决定逐条审计

每条: 带来什么; 付出什么; 是否把研究锁进死路 (判断); 引用事件.

| 约束/决定 | 带来 | 付出 | 锁死? [判断] |
|---|---|---|---|
| **交替路线** (11-01) | 与壁垒一致的唯一已知上行方式; 字面公共上界成为全部比较的纪律 (`cmpH`, `cmpB`, `bdec`) | 无明显代价 | 否. 保留 |
| **让树自足** (11-03 定名) | 促成 `OCF/Free` 的干净证书; 促成 "阶段无关" 的一步定理 (`GᴺTᵠ`, `Gν`, `Sup`) | 三条判据中 "不看记号写出下一步" 不可核对; 成为封存 #6 的理由; 1:1 交替让一半派发进 "摆脱侧" (`StrRel1-19` 108 文件, `MonoPort1-9`, `TreeLang`), 无值定理 | 部分锁死: 它让有值定理的族停投, 让无值定理的族以 "摆脱" 名义继续 |
| **1513 标杆** (11-05) | 第一次有了记号侧同口径的完整成本 (`EboLean3`, 含良基) | RouteReview2 R6: 比的是两种保证 (记号侧第 3 层含良基, 树侧第 3 层只含合法性); 作者 11-05 "逼近标杆则闭项意义不大" 直接导致六路都不交闭项 (`StallDiagnosis` §4.3); 11-07/08 "7351→1418" 以值从 ψ₀(Ω_{Ω·ω²}) 定理降到 BTBO+ω 定理为代价 | 是: 它把优化目标从值换成了行数, 而行数在没有值的层上没有意义 |
| **律带公共上界** (11-05) | 直接消解六路重证 (`bdec`) | 无 | 否. 保留; 但要推广到 "值比较也只在字面轨道上陈述" |
| **构造否定配对** (11-05) | 否定都有前提可满足的见证; 盲定理让判据地位清楚 | 351 个 Neg 文件; 11-05 以后的配对否定结论多为 "接口未被否定" (`NegLvRd`, `NegLvKt`, `NegKcFold`, `NegDnFold`, `NegGenFold`, `NegNewTwr`, `NegKindLv`, `NegStratTw`, `NegRsOwn`, `NegTySup`, `NegPathOut`, `NegX1Up`, `NegX2`, `NegCRw`, `NegNoAcc`, `NegFold1`, `NegTreeLang`); 否定一半消耗一半智能体, 产出信息低 | 部分: 否定对准接口, 没对准值; 路线仍靠读法关闭 |
| **攀爬与摆脱 1:1** (11-04) | 翻译账的纪律 (RESULTS 翻译账 40 行, 大多自报诚实) | 每开一攀爬路要先有摆脱侧编译结果, 实际满足方式是 "一条 no-* 定理" (如 `EndLowH.no-top`), 形式化地过关; 摆脱侧结果没有一条是值 | 部分 |
| **第 4 层不改前 3 层** (11-05) | 防止为验收定制树 | `EndLowT` 未走通 → "作者定不改定义" → 高度树一族至今零值定理; R1 "先不改 H" 与 `no-top` 冲突 (RouteReview2 §4.2); 作者 11-05 后澄清范围只管验收 | 曾经锁死一天; 已澄清 |
| **不开 Funext/K** | 与纲领 2 一致; 33 个文件把 FE/UIP 作显式参数, 结论标 "条件", 没混进成品 | `SameV`, `HtCross` 的正面结果只能是条件; `raise-Lc→WLPO` 的条件在引用中被丢 (StallDiagnosis) | 否. 保留 |
| **序数值验收主档** (11-04) | 松开 `Lab≅tree` 的钉子; `EmbVV`, `BTBOFull`, `SumOneAccept` 全在此档 | `Review2Blind.blindᴬ` [定理]: 值相等的合法 A, FGH 8 对 2048; 终点 "序数 ≥ EBO" 与 "算出 EBO 的大数" 至今未由作者分开定 (RouteReview2 P4) | 否; 但终点陈述未定会在最后一步再付一次 |
| **中间站给界** (11-05) | 规则上允许粗界 | 实践为空: 11-05 以后新站没有一站交出 ≥ 上一站的界; 新交的界 (ε₀, ψ₀(Ω_ω), ψ₀(Ω₂), BTBO+ω) 都在 11-04 前沿之下 | 规则没错, 没有被当作门槛 |
| **封存带高度族** (11-04) | 停止 `Lab` 克隆与 `tH` 攀爬 (这两点有定理支撑: `Lab≅tree`, 翻译账) | 停投了唯一有值阶梯的族; 依据是 `CrossNext` α≥1 "约 1 万行" 的估计, 这类跨结构估计历史上偏低 3-5 倍或从未写出 (手册 §7); 11-07 的简化工作又回到了这一族的实例 (`TreeEmit`, `TotalOrbit`) | 是 (就值而言) |
| **改值简化** (11-07 作者授权) | 1418 行语法切片的候选带 View 与 FGH | 值定理从 ψ₀(Ω_{Ω·ω²}) 退到 ψ₀(Ω_Ω)+ω, 98 件证明; 准确值未证 | 风险: 又一次从低站重算第 4 层 |
| **独立接手 11-06/07** | 大量结构定理 (General/Bounded 400 文件) | 作者两次纠偏: 从 ψ₀(Ω_ω) 重建基线; 未查 `RouteSeal` §1 已列的最高值 | 是 (两天) |
| **用记号验收** (保留 `Lab` 为探路) | 参照树 `WfFsn.EBO-tree`, `TerminalFoldAccept.all-branches` 给了终点形状 | 无 | 否. 保留 |

## 4 否定定理的范围抽查

每条: 陈述原文 (文件); 它否定的范围; 被引用时的范围; 评价 (夸大/低估/准确).

| 定理 | 陈述 | 实际范围 | 引用中的范围 | 评价 |
|---|---|---|---|---|
| `Barrier.barrier` | `Ω-Extension → LPO`; 前提记录含 `Ordᴰ` 精确初始段 (`u-exact`, `v-exact`), Ω-共尾元 `top`, 有界三歧 `dec` | 三个字段同时成立的整包 | AGENTS 第 3 条写法准确; 但 "影子" (W 族) 常被当作它的推论来关路 | 准确; 影子族应单列, 不借壁垒之名 |
| `AccTreeLab.Lab≅tree` | `Lab X t → (h : Acc t) → X ≅ tree t h` | 过 `Lab` 的树 | "现在的定义是翻译形态" (RouteReview §0.2) | 低估了一层: 它只说验收会钉死形态; 封存 #6 的 "翻译" 判断没有定理 |
| `EndLowH.no-top` | `¬ Σ H (λ Λ → ∀ h → hs h ≤ᴴ Λ)` (证明是 `irrᴴ`) | H 里没有最大元 (一行反自返) | RouteReview2 R1 "H 到不了 EBO 需要的高度" | 夸大: 第 3 级需 Λ ≥ Ω_Ω 是判断 (`EndLowAccept` §5 自述) |
| `DiagKLev.upd→wdec` | 对任意 I, F 的积世界, 有 `at`/`off` 律的 `upd` ⇒ `∀ i i′ → ¬(i≡i′) ⊎ ¬¬(i≡i′)` | 对一切 (含不可入) 下标有律的接口 | 六路当作 "世界更新要判定" | 夸大 (StallDiagnosis 已指出); `bdec` 是反例 |
| `CohW2Need.raise-Lc→WLPO` | `FE → (Wo : World) → (∀ c → RaiseAt Wo (Lc c)) → WLPO` | 条件 FE; 对一切极限坐标的层号 | 引用时丢 FE | 夸大 |
| `DiagK3One.noNew-emb` | `∀ h → NoNew (embL (hs hz) h)` (一行, `up-noNew`) | 一种具体增量不造新种类节点 | "读法跌到 ψ₀Λ 之下", 用于不交 `Fold₊` | 夸大 (形状定理被当值定理) |
| `HtTowerNStage.no-wmatch` | 对 `U′`→`L′ 2` 的任何 `wm′`, 两条保界律不能同时成立 (一个 `()`) | 裸积上的世界对应 | 逼出相干世界 | 准确, 信息量高 |
| `HtTowerNeg.no-retract` | `∀ κ e d → ¬ (∀ x → d (e x) ≡ x)` (HB S ↔ E S κ) | 种类坐标不能收缩自身高度 (Cantor 型) | 用于 C4; 又以 `no-faithful` 形式用于 "下降到 Ht 无左逆" | 准确; 但 "无左逆" ≠ "值丢失", `SkeletonAudit` §1.3 自己已标 |
| `Review2Blind.blindᴬ` | 两个 `Lg` 的 A 互相 `≤`, `FGH (ord ·) 2` 是 8 与 2048 | 值验收不管 FGH | 终点陈述 | 低估: 定理在, 决定没做 |
| `HtOutNeg.no-total` | 与 `alim` 交换且严格步进的 `g : A → H` 不能处处 `LgH` | 一种形状 | `HtTotal` 改夹法 | 准确 |
| `GuardBridgeNeg.T₀-too-high` | `tgt₁ ≲ᶻ freeTree → ⊥` | 一条桥 | 早期 README "BLOCKED" | 曾夸大, RouteReview 已纠 |
| `Value.ψ⁰-not-cong` | `Ω₁ ≈ᵛ Ω₁′ × ¬ (ψ⁰ Ω₁ ≼ ψ⁰ Ω₁′)` | 折叠对高层参数不尊重值 | 11-02 记为 "值相等不省代价"; 之后三路仍等 `MonoStep` | **低估**: 它应当改变第 4 层的方法 (只做轨道模拟, 并对阶段参数化), 没有被这样用 |
| `EvFoldLim.no-coh-ev` | `¬ Coh` (该文件指定的相干证据族) | 一个证据族 | 旧 LOG "一切级版本被否定" | 夸大 (ResearchHistory 勘误 10 已纠) |
| `CircuitBoundaryGd.no-generic-transport` | `¬ GenericGdTransport` | 任意旧 Gd 原样搬运 | 文件自述不否定路线 B | 准确 |
| `TLambdaAuditRank.no-rank-upper` | `¬ (TN one tt zero ≤ᵛ rk one tt 1 (fl 1))` | 秩投影不能作上界 | 审计 | 准确 |
| `RadicalNegTotal.no-old-lower` | `¬ OldLower` (全裸 Z) | 全裸程序的保值律 | 自述不否定 Ω̇ 生成域 | 准确 |
| `BrwViewNeg.strict→LPO` | `BrwView … → Enc → LPO` (ℕ-极限按值严格递增) | 严格 View | 改纲领第 1 条解释 | 准确 |
| `TpPort2Tab.no-valmonoT⁺` | `¬ ValMono T⁺ Lg-T⁺ _≤ᴴ_` | `T⁺` 对通常值序不单调, 无条件 | 加强旧条件反例 | 准确 |

**小结 [判断].** 18 条里 6 条在引用中被夸大 (多为 "形状定理当值定理" 或 "条件被丢"), 2 条被低估 (`ψ⁰-not-cong`, `blindᴬ`: 都是关于值与方法的, 没有被用到方法上), 其余准确. 规律: 否定写得窄是对的; 问题在于**派发者用判断补穷尽**, 以及**正面定理 (值不尊重、FGH 不随值) 没有被当成设计输入**.

## 5 哪些方向有前进证据

### 5.1 可核对的进展 (只计编译过的值或结构定理)

| 方向 | 证据 | 类型 |
|---|---|---|
| BTBO 基座 | `BTBOFull.BTBO≈ : tr₀ BTBO ≈ᵛ BTBOᴵ` | 值 ψ₀(Ω_Ω) |
| 差树 | `SumOneAccept.step-T₁ : suc BTBOᴵ ≼ trA T₁`; `T₀≈` | 值 (严格 > BTBO; 精确 ψ₀(Ω_{Ω+1}) 无) |
| 带高度族 | `OrdLabAccept.nf-main/mono-main` (ψ₀(Ω_{Ω·ω}) 标签贴到主线); `EmbVVInstO2.vv-ω² : VV (V end zero) tω²` (ψ₀(Ω_{Ω·ω²})) | 值, 树侧最高 |
| 记号侧 | `WfFsn.fgh-EBO`; `DirectedViewDirectClosed.full-EBO` (保值改写, 1420) | 记号侧, 不进成品 |
| 终点接口 | `TerminalFoldAccept.all-branches : (∀ k → referenceBranch k ≤ᵛ T) → reference ≤ᵛ T`; `sampled` | 结构 (条件) |
| 改值候选 | `TotalValueHighOmega.omega-lower : plus-omega BTBOᴵ ≼ read Final.closed`; `not-btbo-upper` | 值 ψ₀(Ω_Ω)+ω |
| 类型层 | `HtTowerTy.cmpB` 对一切 S; `LFRe.Lg-Λ`; `SkelDxGen.TXΛ` (类型条件齐) | 结构, 无值 |
| 方法 | `StallDxBdec.bdec` (公共界下判等可判定); `TotalValue` 的轨道模拟 (Trace/Embedding/Cumulative) | 方法 |

### 5.2 没有可核对进展的 (投入 ≥ 1000 行而无值定理且无被后续消费的结构定理)

`StrRel1-19` (8715 行), `MonoPort1-9` (5572 行, 限定域结果未接到任何闭项), 骨架塔 #12 (约 1 万行, 读法封顶), C 线 #14 (约 1.5 万行, 读法止于 ψ₀(Ω_{Ω·ω}) 且无值), 独立接手 #15/#16 (约 2 万行, 下界 ≤ ψ₀(Ω₂)), `Inacc` (6098), `Guard`/`Weak` (1.1 万), 标签阶梯 #2 的克隆部分. [判断] 它们不是白做: 多数否定与盲定理来自这里; 但按 "值" 口径它们是零.

### 5.3 有限测试掩盖机制的实例 [统计/自述]

`HtOutTest`: 深度 12 分不开 Ω² 与 Ω³ (文件自述); `Fab6`: 深度 4 结点数相同而机制不同 (Stage §2); `RecBCmp` 有限测试不能传给 `RecB` (ResearchHistory §2.1); `CumUp` 的 G(2) 单路径数字不能推 FGH. 四例都是 "测试通过, 值未证, 读法上升". 测试档在这个项目里对值没有分辨力, 不应再作为站名上升的依据.

## 6 建议: 停止什么, 继续什么, 判据是什么

全部 [判断]; 不否定任何路线 (没有定理), 只谈投入.

### 6.1 停止

1. **没有值下界就不再新开闭项.** 11-05 以后每一个新闭项 (Tdg₂, TG, RecB.Tω, Third.TΛ, closedGrid, Final.closed) 都在交付后才发现值不可证或低于前沿. 改为: 新闭项与它的值下界 (≥ 当前前沿 ψ₀(Ω_{Ω·ω²})) 同一路交付, 缺后者不算交付. 这与作者 11-05 "交付 = 闭项 + 值定理" 一致, 但要把它变成门槛而不是两条平行义务.
2. **停止以 1513 为目标的压缩**, 直到有候选在值上超过 ψ₀(Ω_{Ω·ω²}). 行数只在同保证层比较 (RouteReview2 P6). 已有数据说明压缩会掉值 (7351→1418 对应 ψ₀(Ω_{Ω·ω²}) → BTBO+ω).
3. **停止用读法命名站.** 现状表里 ψ₀(Ω_x) 只准出现在有定理的行; 读法放单独一列 "判断". 否则 R5 的无定理链会继续制造 "就差一点" 的印象 (Stage §9).
4. **停止把接口否定当交付.** 配对否定若只得 "接口未被否定", 不计工作量; 否定一路改为对同一对象写值上界或值反例.
5. **停止在裸下标上写世界更新或比较律** (W 族已 25 条); 停止把高层信息送进固定类型再折叠 (C 族). 接口定稿前过 `SkeletonAudit` §4 的封顶清单.
6. **停止共享未证引理的多路并行.** 11-05 一天 136 条, 三路等 `MonoStep`, 六路重证 W. 同一时刻攻同一对象的路不超过两条 (一构造一值), 第三路必须攻不同对象.
7. **停止从低站重算基线.** 任何新解释器/新候选先证 "不低于 ψ₀(Ω_{Ω·ω²}) 的参照" 或说明为何不能, 再扩建. 11-07 的两次纠偏与 11-07/08 的 BTBO+ω 都是这一条的代价.

### 6.2 继续 (按证据强弱)

1. **带高度族作为值基座, 显式解除 "停投" (封存政策的 B 类改为现役).** 理由: 它是唯一有值阶梯的族, 11-07/08 的工作事实上已回到它的实例. 第一件事不是攀爬, 是把它的**下一站读法变成定理或反例**: `CrossMClosed.T⊤` 读 ψ₀(Ω_{Ω²}) (判断). 用 `EmbVVMain.V-≃` 的工具证 `T⊤` 的序数值 (上下界各一条), 或证它不到. 这是当前最小的、能移动值前沿的可核对目标. 翻译账照记, 但翻译账不再是停投理由, 值才是.
2. **差树 `SumOne` 的上界** (`T₁ ≼` ψ₀(Ω_{Ω+1}) 参照): 这是检验 "新定义风格能否做第 4 层" 的最便宜实验 (估计三次未写, 应当写或证明写不出). 若在有界投入 (建议: 一路, 两天) 内做不出, 差树一线在值上没有路径, 应当如实停.
3. **`TotalValue` 的机制当方法保留, 不当对象继续.** 98 件得 BTBO+ω 说明逐站模拟不可扩展; 下一步只做一件事: 把 `Cumulative`/`Embedding` 这组证明对 `HtB`/行号参数化, 使 ω² 端行的值定理成为同一定理的实例. 做不到就不再在这个候选上加站.
4. **终点接口** (`TerminalFoldAccept`, `WfFsn`) 保留; 并请作者定终点陈述是 "序数 ≥ EBO" 还是 "大数" (`blindᴬ` 说两者不同), 因为它决定第 4 层做到哪一档.
5. **类型层资产** (`cmpB`, `LFRe`, `SkelDxGen` 的类型条件) 保留为将来 Ω-塔的载体, 但在值前沿越过 ψ₀(Ω_{Ω²}) 之前不再扩建.

### 6.3 继续投入必须满足的可核对判据

1. **值阶梯.** 每轮汇报一个数: 树侧候选上编译过、无条件 (无 Funext/UIP 前提)、定义与证书导入闭包记号禁用 0 的最大 x, 使 ψ₀(Ω_x) ≼ 候选. 当前 x = Ω·ω² (`EmbVVInstO2.vv-ω²`). 连续两轮 x 不升的路线暂停.
2. **阶段无关的值证明.** 站 k+1 的值定理必须是站 k 的值定理的实例 (同一模块, 换参数), 判据: 每升一站不新增证明模块. `GᴺTᵠ` 对合法性已做到, 对值一次也没做到; 这才是 "树自足" 目前唯一可核对的替身.
3. **封顶清单.** 任何新接口定稿前列出 `SkeletonAudit` §1.2 的七类封顶处并给出上界或 "不适用"; 有 `→ Ht`、`→ HB S₀` 一类固定值域的接口不得定稿.
4. **否定的用法.** 新否定只在它改变了某个接口的定义域或字段时计入; 同族第 n 条 (n ≥ 3) 不再派路, 改为引用.
5. **估计的用法.** 跨结构桥的估计一律乘 3 后再比较; 估计三次仍未写的东西视为未知, 不得作封存依据.
6. **接手.** 任何接手先交 "当前值前沿与最高闭项" 一表 (本文 §5.1 可直接用), 作者核对后再派路.

## 7 附: 统计方法与复核

- [统计] 文件与行数: 脚本对 `probes/` 下全部 `.lagda.md` (不含 `_build`) 统计 agda 代码块的非空非注释行, 按文件名首个大写单词聚合为 "族", 首次入库日期取 `git log --diff-filter=A`. 聚合有误差 (如 `T`, `S`, `L`, `K`, `No` 这类短前缀混入多族), 本文只用它判数量级.
- [统计] 提交增量: `git show --numstat` 限 `probes/`.
- [定理] 本次重新编译 (从仓库根, 库文件为当前 stdlib 与 cubical 的两行, `+RTS -M6G -RTS`, 退出码不经管道): `OCF/Align/SkelDxGen` 0; `OCF/Align/TotalValueHighOmega` 0; `OCF/Align/TotalValueNegStrictAudit` 0; `OCF/Align/Review2Blind` 0; `OCF/Align/StallDxBdec` 0. 其余定理只核对了陈述原文, 没有重编.
- 本文不改任何已有文件, 不提交.
