# 2026-11-11 各路回报的留档

> 接 [2026-11-10 的留档](../Reports-2026-11-10/README.md); 做法与读法同那里的文首. 每一路一个文件: 派发时的简报原文, 中途消息, 交回的回报原文与运行数字. 回报里的判断不是主审的结论; 结论以 `probes/LOG.md` 为准. 生成脚本 `probes/Survey/scripts/agentreport.py`.

## 1 总表

时间是转录里的时间戳 (UTC). 这一轮是作者 2026-11-11 定的: 主攻 "把折叠写在第 K 层的树上", 配一路否定; 同时给上一轮有限层号一站的闭项补值的下界定理.

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 写在第 K 层的树上, 构造 | [YiRawFold](YiRawFold.md) | Fable 5.2, xhigh | 2026-11-10 23:59 至 00:40 | 244876 | 接口记录有实例, 派发处处完全; `tw 3` 的闭项 `T₃ᵐ` 合法, 无前提; 极限层号上的 `top` 在保留模式下取部分和; 没有值定理 |
| 写在第 K 层的树上, 否定 | [YiRawNeg](YiRawNeg.md) | Fable 5.2, xhigh | 2026-11-10 23:59 至 00:40 | 256769 | 接口记录偏弱 (有便宜的模型); 根链的判据与限制形式; 部分和与归一值不降, 可升高; 公共上界含 Ω 结点时只有路径相连的位置对可比 |
| 有限层号闭项的值下界 | [YiLvVal](YiLvVal.md) | Opus 5.5, high | 2026-11-10 23:59 至 00:43 | 269627 | 上一轮的折叠的闭项: n ≤ 3 的下界是定理, 一切有限 n 与 ω 是条件定理; 没有发现掉值 |

共用接口 (主审写, 已编译, 定稿后只增不改): [YiRawIf](../../OCF/Align/YiRawIf.lagda.md).

### 同一天的第二批 (作者定: 四项全派; 设计题用 Fable 5.2, 值定理用 Opus 5.5)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 第 4 步第一站, 构造 | [YiOmFold](YiOmFold.md) | Fable 5.2, xhigh | 2026-11-11 05:21 至 06:18 | 339559 | 没有过去; 闭项 `T⁺` 合法无前提但用了替代行, 读法未定; 三处障碍的约化与闭实例; 两条绕过障碍的行没有接进闭项 |
| 第 4 步第一站, 否定 | [YiOmNeg](YiOmNeg.md) | Fable 5.2, xhigh | 2026-11-11 05:21 至 05:55 | 207730 | 保留行的障碍来自块的写法 (推出凭无关证据取数据); 目标在某一支里而树是 `top` 时保留律推出 LPO; 两种块变体的试验见[附件](attachments/README.md) |
| 累加能否去掉 | [YiPsum](YiPsum.md) | Fable 5.2, xhigh | 2026-11-11 05:21 至 06:17 | 343666 | 能去掉, 带定义域 (证书一致, 极限处路径取第 0 支, 槽位取规范位置); `tw 3` 的闭项各支里没有部分和, 根的坐标上仍有归一 |
| 新折叠的值下界 | [YiRawVal](YiRawVal.md) | Opus 5.5, high | 2026-11-11 05:21 至 05:38 | 106479 | 新折叠的闭项 n ≤ 3 的下界是定理; `T₃ᵐ` 不低于 ψ₀(Ω₃) 的参照; 没有发现掉值 |
| 旧折叠的值下界补到一切有限 n | [YiLvAll](YiLvAll.md) | Opus 5.5, high | 2026-11-11 05:21 至 05:50 | 182426 | 一切有限 n 与 ω 的下界是无条件的定理; 证明对层号一致 |

第 4 步第一站的共用接口 (主审写, 已编译): [YiOmIf](../../OCF/Align/YiOmIf.lagda.md).

### 同一天的第三批 (作者定: 判定题, 值到 BTBO, 独立审查; 模型沿用)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 判定题, 构造 | [YiGenFold](YiGenFold.md) | Fable 5.2, xhigh | 2026-11-11 06:43 至 07:44 | 371467 | 截断链上的闭项 `Tᶜ` 合法, 调用闭包上派发完全, 无前提, 用了替代行, 没有值; 归一链上派发全部完全是条件定理, 缺口是一个函数字面相等的实例 |
| 判定题, 否定 | [YiGenNeg](YiGenNeg.md) | Fable 5.2, xhigh | 2026-11-11 06:43 至 07:35 | 301164 | 条件的: LPO 型的墙不在链上; 标准保留行下第 2 个链点问到极限层号字面相等的弱判定 (加函数外延才是 WLPO); 分歧落在保留结点的各支要不要是原各支的折叠 |
| 把值做到与 BTBO 持平 | [YiBtVal](YiBtVal.md) | Opus 5.5, high | 2026-11-11 06:43 至 07:40 | 347321 | 新折叠的值下界到一切有限 n, ω, ω+n; `T₃ᵐ` ≥ ψ₀(Ω_ω); 与 BTBO 持平归约到一条未证的单调性 `MonoT` |
| 第六次独立审查 | [Review6](Review6.md) | Fable 5.2, xhigh | 2026-11-11 06:43 至 07:12 | 160968 | 整理成 [RR6-Uncountable](../RR6-Uncountable.md): LPO 定理的范围; 三种写法不互斥; 建议先试受支配的域; 主审接受五条更正 |

判定题的共用接口 (主审写, 已编译): [YiGenIf](../../OCF/Align/YiGenIf.lagda.md).

### 同一天的第四批 (作者定: 四路全派, 全部 Opus 5.5; 第 4 步的验收改成以值下界为主)

同日稍后作者纠正了派发顺序: 尾部行实验与量值两路对参照的下界都要那条未证的单调性, 先停下, 等单调性闭合后再从 BTBO 往上做. 见 LOG 的 "作者纠正派发顺序" 一节.

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 压缩: 从头重写到塔的第 3 项 | [YiLean](YiLean.md) | Opus 5.5, high | 2026-11-11 08:02 至 08:41 | 235296 | 前三层 112 / 335 / 351 (旧 297 / 1251 / 1373); 块重新设计过; 塔与 Λ 合法; 值下界到 ψ₀(Ω₂); 与旧闭项不是同一棵树 |
| 实验: 尾部行掉不掉值 | [YiTail](YiTail.md) | Opus 5.5, 未指定 effort | 派出约十几分钟后停下 | 已停 | 作者 2026-11-11 定: 等单调性一路回来再续; 没有留下仓库文件; 文件里只有简报 |
| 证或否定那条单调性 | [YiMono](YiMono.md) | Opus 5.5, high | 2026-11-11 08:02 至 08:38 | 207814 | 没有闭合. 结构可比的证法有编译否定 (`no-L`); 新下界 `T₃ᵐ` ≥ ψ₀(Ω_{ω+1}); BTBO 下界归约到 `EmbT` / `VMᴸ` / `Crux` (未证) |
| 给现成闭项量值 | [YiBaseVal](YiBaseVal.md) | Opus 5.5, 未指定 effort | 派出约十几分钟后停下 | 已停 | 作者 2026-11-11 定: 等单调性一路回来再续; 没有留下仓库文件; 文件里只有简报 |

### 同一天的第五批 (作者定: 主线改用新块; 与 BTBO 持平的两种证法都派; 全部 Opus 5.5)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 值单调, 构造 | [YiVmCon](YiVmCon.md) | Opus 5.5, high | 2026-11-11 08:59 至 09:24 | 144011 | 一般情形没有闭合; 保值嵌入 `XEmb` 使左极限不要一致性; 值单调在定义域 `≼ᵖ` 上是定理 (`VMᵖ`); 这条证法的一般化要 LPO (`tri→LPO`); BTBO 下界归约到 `ChainP` |
| 值单调, 否定 | [YiVmNeg](YiVmNeg.md) | Opus 5.5, high | 2026-11-11 08:59 至 09:29 | 177894 | `VMᴸ` 本身没有否定; 保初始段的嵌入推出 LPO (`embVᴰ→LPO`); 不读推导的写法推出 Markov 原则 (`vm¬¬→MP`); 探针严格; 链上的陈述 `VMᶜʰ` 足以推出 BTBO 下界 |
| 主线块上的值证明, 带前驱结构 | [YiLeanVal](YiLeanVal.md) | Opus 5.5, high | 2026-11-11 08:59 至 09:34 | 206426 | 主线新块上 `lower-any` (一般可数层号), `T₃` ≥ ψ₀(Ω_ω); 与 BTBO 持平是条件定理, 只缺 `ChainP` 的 n ≥ 1; 结构可比在新树上也有编译否定; 验收 715 行 |

构造与否定共用的陈述在已定稿的 [YiMonoVM](../../OCF/Align/YiMonoVM.lagda.md) (`VMᴸ`, `Crux`, `EmbV`).

### 同一天的第六批 (作者定: 派同高度的设计候选; 全部 Opus 5.5)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 设计候选甲: 基本列向参照对齐 | [YiZero](YiZero.md) | Opus 5.5, high | 2026-11-11 09:06 至 09:37 | 195262 | 判据第 1 步不通过, 编译否定对任何累加链成立 (`nz-any`), 与基本列无关; 折叠这一层已对齐 (`readΨ`); 行数 112 / 356 / 374 |
| 设计候选乙: 链不累加 | [YiDiag](YiDiag.md) | Opus 5.5, high | 2026-11-11 09:06 至 09:41 | 185788 | 不累加的闭项合法, 无前提; 第 1 步与参照结构互模拟 (`read-pt1`); 行数 112 / 213 / 437 (计入塔 511); 续做 (约 12 分钟, 一个新文件 `YiDiagAccNeg`) 的结果是否定的: `no-γ₂` (第 2 步不互模拟), `no-termwise` (非零目标层逐项在字面第一位置下不合法); 较弱的对上在 n = 2 未定 |
| 设计候选丙: 独立样本 (一句话的提示) | [YiFree](YiFree.md) | Opus 5.5, 未指定 effort | 2026-11-11 09:06 至 10:29 | 约 51 万 (全是思考) | **失败**: 读完三个允许的文件后, 连续四次回复都把 128000 个输出 token 用在思考上, 没有工具调用, 第四次以输出上限的 API 错误终止; 没有写文件 |

三路共同的判据: 链点的层号与参照对角链在第 1 步结构可比或不可比 (编译事实). 候选丙的简报就是那句 "一句话的提示词", 留档可作以后空白页简报的样本.

### 同一天的第七批 (作者定了短期目标: 读法超过 BTBO, 值定理与 BTBO 持平, 合法性到 Λ, 500 行以下的闭项)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 下一站的闭项, 连同塔的合法性 500 行以内 | [YiNext](YiNext.md) | Opus 5.5, high | 2026-11-11 09:21 至 09:56 | 210120 | `T⁺` 合法, 无前提, 第 0 项是 `T₃`; 连同塔与 Λ 的合法性 475 行; 读法 ψ₀(Ω_{Ω+1}) 未核实 (保守的派发丢掉可保留的位置对); 与 BTBO 持平接上的一环是条件定理 |

### 同一天的第八批 (主审的主线评估之后; 作者定三路都派, 全部 Opus 5.5; 独立样本同时重派)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 主线上证 `ChainP` | [YiChain](YiChain.md) | Opus 5.5, xhigh | 2026-11-11 10:39 至 11:18 | 231090 | n = 1 无条件 (`chainP₁`, 两个方向 `γ₁≈`), 靠结构吸收 (`Abs.ABS`), 不用判定; `T₃-γ₂`; 一般 n 归约到 `P1`, `P2`, 缺上界与两个方向的嵌入 |
| 同一陈述的否定 | [YiChainNeg](YiChainNeg.md) | Opus 5.5, xhigh | 2026-11-11 10:39 至 11:05 | 156466 | 否定写不出来: `lem→chainP` (经典下成立); 归约到链上的局部二分 (`triOn→chainP`, 第 1 项只缺 `n1-from` 的前提); 三条对一切树的捷径推出 LPO |
| 值证明搬到下一站的折叠上 | [YiNextVal](YiNextVal.md) | Opus 5.5, xhigh | 2026-11-11 10:39 至 11:12 | 206360 | 转运定理 (`co≅`, `T₃≅`, `F≅`); 主线的 `ChainP` 推出 `T⁺` ≥ BTBO 的参照 (`btbo⁺-from-main`); `T⁺` ≥ ψ₀(Ω_ω) 无条件 |
| 独立样本重派 | [YiFree2](YiFree2.md) | Opus 5.5, 未指定 effort | 2026-11-11 10:31 至 11:21 (主审停下) | 约 26 万 (思考) | **又失败**: 读完三个允许的文件后两次回复都把输出上限用在思考上, 没有工具调用, 没写文件; 主审停下 |

构造与否定共用的陈述在已定稿的 [YiLeanValFin](../../OCF/Lean/YiLeanValFin.lagda.md) (`ChainP`, `btbo-p`).

### 同一天的第九批 (一般项 `ChainP` 缺的三条引理; 作者定全部 Opus 5.5)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 主线折叠的值的上界 | [YiUB](YiUB.md) | Opus 5.5, xhigh | 2026-11-11 11:26 至 11:57 | 176247 | 第 1 层两向 (`ub₁ˣ`, `lb₁ˣ`); 一般上界的否定 (`no-UB`, 常值极限); 严格的树上 `FOLD2`; 与 BTBO 持平归到 `StrChain` (`btbo-str`), 缺第 2 层以上的一步 |
| 两个方向的嵌入给出的折叠单调 | [YiEmb2](YiEmb2.md) | Opus 5.5, xhigh | 2026-11-11 11:26 至 11:38 | 75045 | 参照一侧无条件解决 (`VMˣ`, `p1₂`); 与 BTBO 持平只剩主线一侧的两向陈述 `P2₂` (`btbo-cond₂`); `P2₂ 0` 是定理 |
| 第 1 层以上吸收的两条结构事实 | [YiFlat](YiFlat.md) | Opus 5.5, xhigh | 2026-11-11 11:26 至 11:50 | 146884 | 两条结构假设成了定理; 第 1 层以上的吸收两个方向无条件 (`absΩ`, `absΩR`); `κ≺`; `P2₂` 归到主线折叠值的两向界 `FoldB` |

### 同一天的第十批 (第 2 层以上的一步与测量; 作者定全部 Opus 5.5)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 第 2 层以上主线折叠与参照两向对上 | [YiSuc](YiSuc.md) | Opus 5.5, xhigh | 2026-11-11 12:12 至 13:22 | 398377 | 链上最早的实例定义域版两向 (`chainPt-top-1`); `btbo⁺-str` (条件); 第 2 项起与第 3 层以上没走通 |
| 测主线折叠是否超过参照 | [YiOver](YiOver.md) | Opus 5.5, xhigh | 2026-11-11 12:12 至 13:00 | 302235 | 不超过: 第 2 层值相等 (`≈₂`), 链上最早的实例值相等 (`over-pt`, `low-pt`); 严格超过的否定; 值序版, 不是定义域版 |

共用陈述在已定稿的 [YiUBRed](../../OCF/Lean/YiUBRed.lagda.md).

### 同一天的第十一批 (作者: "只要证明 BTBO 是下界即可"; 两路只用下界, Opus 5.5)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 严格的树上的值单调 | [YiLow](YiLow.md) | Opus 5.5, xhigh | 2026-11-11 13:47 至 14:30 | 263737 | 这条证法被否定: 严格树上值序推出前驱嵌入推出 LPO (`embVˢ→LPO`, 连带 `embV→LPO`); ω² 以下成立; 只在链上的值单调推出 BTBO 下界 (条件) |
| 沿链造前驱嵌入 | [YiPE](YiPE.md) | Opus 5.5, xhigh | 2026-11-11 13:47 至 14:25 | 232711 | 没有闭合; 归约到 `FUNC`, `KEYsuc`, `SpineT` (`btbo-FS⁺`); 新工具阶梯粘接 (`Stair.stair`), 平移嵌入 |

### 同一天的第十二批 (第七次独立审查与 `FUNC`; 作者定全部 Opus 5.5)

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 参照一侧的函子性 `FUNC` | [YiFunc](YiFunc.md) | Opus 5.5, xhigh | 2026-11-11 14:37 至 15:23 | 281326 | 第 1 步的实例是定理; 一般的归约到 `CRUX`, `NEXT` (条件), 未走通; 对 BTBO 下界已不需要 |
| 第七次独立审查: 更省的整体证法 | [Review7](Review7.md) | Opus 5.5, xhigh | 2026-11-11 14:37 至 15:23 | 281924 | **BTBO 是下界, 无前提**: 主审移入 `YiBtboV2`, `YiBtboLower` 并冷编复核; 整理成 [RR7-BtboLower](../RR7-BtboLower.md), 七条更正都接受; 预览 [Review7-preview.txt](Review7-preview.txt) |

## 2 回头接着做, 从哪里入手

每条先写编译过的事实, 再写执行方对下一步的判断 (未验证).

**写在第 K 层的树上, 构造 (`YiRawFold*`).** 核心 `YiRawFold` (`Ψ`, `Φᵐ`, `Φ`, `rawFold`); 依赖序 `YiRawFoldBase`, `YiRawFold`, `YiRawFoldInst`, `YiRawFoldUp`, `YiRawFoldNoLim`, `YiRawFoldTw3`.
- 做成的: 接口实例 `rawFold`; 派发五种来源都完全 (`complete-*`); `closedᵐ-legal` (一切 `Plain` 且 `Legal` 的 K); `Φ-below`; `T₃ᵐ-legal` 与根上的行.
- 两种放法的区别要记住: `Φᵐ` 无前提, 极限层号上 `top` 取部分和; `Φ` 在目标第 0 层逐项, 合法性要 `CohP`. 保留模式下 (链的推进里) 两者都取部分和.
- 没做成的或没做的: 值定理; 与上一轮 `foldᶠ` (n ≥ 1), `T₃` 的比较; `Φᵐ-below` 对极限处取第 n ≥ 1 支的路径; `OutCoh` (执行方估计上千行, 且证出来也去不掉部分和); 规范槽位派发下极限层号的 `top` 能否逐项 (缺的那条 `Cp` 的类型在回报 §6 (a)).
- 公共上界 `tw 2` 不是 `Plain` 的, 不在这一轮的片段里: 这是第 4 步的入口.

**写在第 K 层的树上, 否定 (`YiRawNeg*`).** 没有入口文件; 依赖序 `YiRawNegModel`, 然后 `YiRawNegChain`, `YiRawNegLift`, `YiRawNegNorm`; `YiRawNegOmega` 独立.
- 可以直接导入的正面部件: `wrap` 一组 (沿路径的提升); `toRaw`, `fromRaw`; `Root`, `CohRoot`, `NormRoot` (根链的判据); `Bridge.cross`, `Bridge.top-legal`; 第 0 层的值序与 `cum-above`, `lim≼psum`; `plain-fix`; `Link`, `compare-link`.
- 对接口的意见: 保留律不约束保留结点的内容与槽位; 建议增补 `SlotFree`. 接口定稿后不改, 要补就另写增补文件.
- 第 4 步的界: `no-compare-tw2`, `dec-at→lpo`, `keep-fold→wlpo`; 律的定义域取 `Link`. 没有判定的: 第 4 步的规范构造会不会走到不满足 `Link` 的位置对.
- 没写成的各带缺的引理, 在回报 §5.

**有限层号闭项的值下界 (`YiLvVal*`).** 入口 `YiLvValFin`; `YiLvVal3` 冷编要 6G 的堆上限 (执行方记的常驻峰值 6.59G).
- 定下的: `lower₀` 到 `lower₃`, `Ω₃≼fold-Ωω`; 分解 `FromInterface.theorem`; `interface₀`, `interface₁`, `interface₂`.
- 条件: `AllLevels.lower-fin`, `AllLevels.lower-ω`, 前提 `∀ M → Interface M`.
- 接着做要先解决的 (执行方的探针, 回报 §5): 变量层号上 `wayᵇ` 不化简成字面的 `keep`; 变量槽位上 `Low (fin N) r` 不能当作 `Raw (lev (fin N) r)`; 缺对 M 一致的关系族. 否定路的 `toRaw`, `fromRaw` 可能用得上 (主审的判断, 未验证).
- 注意对象: 验收的是上一轮写在 `LF` 上的折叠, 不是本轮写在 `Raw K` 上的折叠.

**新折叠的值下界 (`YiRawVal*`).** 依赖序 `YiRawValBase`, `YiRawVal2`, `YiRawVal3Base`, `YiRawVal3`, `YiRawValTw3`; 各 2G 以下.
- 定下的: `lower₀` 到 `lower₃` 及带 ᵐ 的各条 (新折叠的 `closed (fin n)`, `closedᵐ (fin n)`); `T₃ᵐ-Ω₁`, `T₃ᵐ-Ω₂`, `T₃ᵐ-Ω₃`; `one≼`.
- 条件: `FromInterface.theorem`, `theoremᵐ`, 前提 `Interface M`, 实例到 M = 2.
- 接着做 (执行方的判断): 一切有限 n 缺 `∀ M → Interface M`, 新派发是对位置的规范比较, 变量层号上要另写化简引理; `T₃ᵐ` 往上要 "第 1 项第 0 支的第 n 支等于 `closedᵐ (fin (n+2))`" 的命题等式, 合起来可到 ψ₀(Ω_ω); 再往上要极限层号以上闭项的值定理, 会用到部分和一行.
- 依赖部分和一行的只有 `T₃ᵐ-Ω₂`, `T₃ᵐ-Ω₃` (若那一行被换掉, 这两条要改一步).

**旧折叠的值下界补到一切有限 n (`YiLvAll*`).** 入口 `YiLvAll`; 依赖序 `YiLvAllRel`, `YiLvAllTree`, `YiLvAllAdd`, `YiLvAllFold`, `YiLvAll`; 各 2G 以下 (入口只加载 `YiLvVal3` 的接口).
- 定下的: `lower-all`, `lower-Ωω` (无条件); `interfaceᴬ`; 对层号一致的 `Rel`, `FOLD`, `ABSORB`, `ADDg`, `SUCC`, `TRC-all`; 变量层号上的 `TREE-KEEP`, `TREE-FOLD`.
- 接着做的方向 (主审的判断, 未验证): 把同样的一致版本搬到写在 `Raw K` 上的新折叠 (`YiRawVal*` 那边只到 n ≤ 3, 缺 `∀ M → Interface M`); 含极限的层号上的值 (参照一侧的层号不再是 `natᴵ`).
- 没有的: 上界与同值.

**第 4 步第一站, 否定 (`YiOmNeg*`).** 没有入口文件; 依赖序 `YiOmNegSlot`, `YiOmNegTop`, 然后 `YiOmNegTrunk` 与 `YiOmNegBranch`; `YiOmNegBranchFixed` 独立 (条件, 前提 `FunextR`).
- 定下的: `slot-irr→irr-search` 一组与 `top-keep→irr-search` 一组 (保留行在现在的块里拿不到数据); `top-branch→lpo` (目标在某一支里而树是 `top`, 保留律推出 LPO, 只对 `Link` 的对要求也一样); `no-trunk`; 模型 `data→top-keep`, `oracle-branch`.
- 可以直接导入的正面部件: `lev-legal₂`, `node₂-copy`, `rel-branch-node`, `trunk-plus`, `trunk-read`, `at-one-dec`.
- 试验文件 (不是成果): [附件](attachments/README.md) 里的变体甲与变体乙. 甲不解决问题 (搜索挪到同支比较); 乙在骨架级同时得到槽位与同支比较, 代价是 ℕ 极限上换证明就换树.
- 没有判定的, 也是下一步最该定的: 规范的链是否必然碰到 `top-branch→lpo` 管的那一行 (执行方走查的判断是第二个链点就碰到); 闭项的值是否需要那一行上的派发完全 (执行方未验证的想法: Ω₁ 长的分支族的极限只看尾部).
- 没写成的各带缺的引理, 在回报 §6.

**累加能否去掉 (`YiPsum*`).** 依赖序 `YiPsumBase`, `YiPsumFold`, `YiPsumZp`, `YiPsumInst`, `YiPsumTw3`, `YiPsumOrig` (条件), `YiPsumVal`.
- 定下的: 变体折叠 `Ψᵗ` 与 `Ψᵗ-legal`, `belowᵗ`; `rawFoldᵗ : RawFoldOn Domᵗ`; `closedᵗ-legal`; `T₃ᵗ-legal`; 结构规范化 `pre` 及 `pre-complete`, `pre-sound`, `preCoh`; 值: `lim≼psumᵖ`, `psum-flat`, `absorb-suc`, ω 与 ω·2 上互相 ≼, `const-inflates`.
- 三个 `tw 3` 的闭项要分清: `T₃ᵐ` (上一轮; 根不改行, 各支取部分和; 值下界验收的是它), `T₃ᶜ` (上一轮; 根的坐标归一), `T₃ᵗ` (本轮; 各支逐项, 根的坐标归一). 它们之间的关系没有比.
- 没做的 (各带缺的引理, 回报 §5): 域 `ZpL` 之外 (极限处取第 n ≥ 1 支的路径, 缺对一般路径的 `cs-restrict`, `unshift-restrict`); 根不改行而各支逐项的 `tw 3` 版本 (缺 "输出证书一致且 `ZC`" 的引理, 类型在回报 §5 (c)); 一般目标层上的值序; 加法在 `x + top` 极限层号处的逐项累加没有动.

**第 4 步第一站, 构造 (`YiOmFold*`).** 依赖序 `YiOmFoldBase`, `YiOmFold`, `YiOmFoldGap`, `YiOmFoldNorm`, `YiOmFoldRel`, `YiOmFoldChain`; `YiOmFoldTop` 只依赖前两个.
- 做成的: `plusΩ` 一组; `Φ⁰` (目标层 0, 不含分支槽位结点的树), `Φˢ` 与 `Φˢ⁺` (目标为 `tw 2` 自己); 闭项 `T⁺`, `T⁺-legal`, 行都是 `refl`.
- 三处障碍: O1 `keep→irr-search`; O2 `moved-undirected`, `moved-not-first`; O3 目标层 0 在分支槽位结点上的行 (缺的 `own` 的类型在回报 §5 (3); `BranchRow.branch-row-legal` 是条件定理).
- 绕过 O1, O2 的行, 没有接进闭项: `topᴺ` (归一坐标, `norm-keep`), `rowᴿ` (相对坐标, `rel-compare`).
- 四条替代行要分清 (回报 §4): `topᴬ` (加法里的 `x + top`), `topˢ` (闭项 `T⁺` 用的), `topᴺ`, `rowᴿ`.
- 接着做的方向 (执行方的判断): 把折叠写在生成数据上并配合相对坐标, 使 "同一支" 与路径由结构给出; 先定 "规范的链是否必然要求分支目标下对别的支上结点的派发".

**第六次独立审查.** 文档在 [RR6-Uncountable](../RR6-Uncountable.md) (审查者原文加主审的说明); 临时试验 `R6Strict`, `R6Tail`, `R6Diag` 与 "读结论之前的看法" 在[附件](attachments/README.md).
- 回头看时先读 RR6 的 "主审的说明" (接受的五条更正), 再读正文的问题 1 (那条 LPO 定理的范围) 与 §3 的对照表.
- 审查者建议的下一个实验 (判断): 目标层 1 上完全行与尾部行折到第 0 层后的值的比较; 陈述的草稿在正文问题 5.
- 审查者没有读的与只凭转述引用的, 列在正文 §5.

**判定题, 否定 (`YiGenNeg*`).** 依赖序 `YiGenNegShape`, `YiGenNegAsk`, `YiGenNegLeft`, `YiGenNegWall`, `YiGenNegWallWlpo` (条件); `YiGenNegOne`, `YiGenNegNorm`, `YiGenNegRel`.
- 定下的 (正面): `zero-point-level` (第 0 点片段不需要判定), `asked-norm`, `lpo-target-off-chain`, `fixed-target-off-chain` (上一轮的 LPO 与 WLPO 探针不在链上), `r₁-dec`, `under-r₁`.
- 定下的 (否定, 带前提): `chain→weak-eq` (标准保留行下第 2 个链点的弱判定), `weak-eq→half`, `chain→wlpo` (条件, `FunextR`); `row₃-not-branch-keep` (相对坐标的行各支不诚实).
- 可复用: 链点的形状等式 (`point₁-root`, `point₂-root`, `N₂-branch` 等); 问到的对的归纳谓词 `Asked.Ask`.
- 留下的问题 (回报 §5): 无函数外延时 `WeakEq` 推出什么; 其余叶与后续链点上问到什么; 保留行是否必须取标准写法 (值是否需要它).

**把值做到与 BTBO 持平 (`YiBtVal*`).** 依赖序 `YiBtValRel`, `YiBtValAdd`, `YiBtValFold`, `YiBtValAdm`, `YiBtValFin`, `YiBtValTw3`, `YiBtValBT`; 各 2G 以下.
- 定下的: `lower-allᵐ` (一切有限 n), `lower-any` (一般的合法 `Plain` 层号, 前提 `Corr`, `Zs`), `lower-ωᵐ`, `lower-ω+ᵐ`, `Ωω+1-lower`; `T₃ᵐ-Ωω`, `T₃ᵐ-own`; 一般的 `FOLD` (前提: 外部派发完全).
- 条件: `FromMono.btbo : BTBOᴵ ≼ read T₃ᵐ`, 前提 `MonoT` (类型在回报 §3). `mono₀`, `mono-⊑` 是它已证的两种情形.
- 接着做: 证或否定 `MonoT` (ψ⁰∘Ω 对层号的值单调). 执行方的判断: 结构可比的路线在第 1 步之后断开, 要值层面的论证; 关系族若放宽到 "值不高于", 两侧派发会不一致, 需要新的构造子 (未试).
- 参照取的是 Level 框架里不累加的对角线 (`Diagonal` 取 `Uniform`), 不是 `src` 的 BTBO.
- 多数定理经过极限层号处的部分和一行与加法里的累加; 哪些经过列在回报 §4 末.

**判定题, 构造 (`YiGenFold*`).** 依赖序 `YiGenFold`, `YiGenFoldDom`, `YiGenFoldFin`; 然后 `YiGenFoldSteps`, `YiGenFoldGap`.
- 定下的: 对派发与定义域参数化的折叠 (`Fold.Ψᶠ`, 合法性对任何派发成立); 对坐标谓词的一步定理 (`Spine.wayS-complete`, `honestᴰ`); 截断链的闭项 `Tᶜ`, `Tᶜ-legal`, `chain-honest`; 归一链的闭项 `Tᴾ-legal` 与部分完全 (`keptᴾ-trunk`, `keptᴾ-fin`).
- 条件: `Canon.honestᴺ` (前提 `AskDec`, 类型在回报 §3).
- 缺口的定位: `asked₁`, `at→fe`, `fe→at`, `weak-fe`, `complete-there→`; `same-at`, `same-folds`.
- 可复用: 调用闭包 `Ask`; 模块 `Spine` 对任何可判定的坐标谓词与路径给出派发; `TopRow.Row.rowᶠ`.
- 接着做 (回报 §5, §6): 把诚实的定义域从有限坐标推广到单一闭坐标的支里的全部位置 (要槽位映射由坐标的语法形状给出); 把折叠写在生成数据上能否去掉同一支里那一对, 没有做; 三个闭项 `Tᶜ`, `Tᴾ`, `Tᴺ` 与上一轮 `T⁺` 的关系没有比; 都没有值.
- 同口径行数 (主审量): `Tᶜ` 前三层 2471 / 2493.

**第三批四路都已返回.** 合读在 [RouteReview3](../RouteReview3.md) §5.12 末与 LOG 同日的 "第三批的合读".

**证或否定那条单调性 (`YiMono*`).** `YiMonoBreak`, `YiMonoEmb`, `YiMonoVM` 互不依赖; `YiMonoOne` 依赖 `YiMonoEmb`. 各 1.4G 以下.
- 定下的: 结构可比的证法不通 (`no-L`, `no-mono-⊑`, 机制 `noω`, `inv-nz`, `sω-L1`); 前驱嵌入的工具 (`PEmb-suc`, `PEmb-limˡ`); 新下界 `T₃ᵐ-Ωω+1`; 树一侧的一半 (`HS-read`, `lvl≅`).
- 条件: `btbo-dom` (前提 `DomT`), `emb→dom` (`EmbT`), `btbo-vm` (`VMᴸ`), `crux→vm` (`Crux`), `embV→vm` (`EmbV`). 类型在回报 §3.
- 接着做, 两条不同的路: (一) 与树有关: 证 `EmbT`, 即把 `YiBtVal` 的值证明底关系从值换成前驱嵌入重做 (回报 §5 列了缺的四条引理; 先 n = 1). (二) 与树无关: 证 `Crux` / `VMᴸ` (Level 族上的值单调), 或证它推出某条全知原则 (回报 §4 (甲) 说了左极限一致性的困难与 "保初始段" 修法的嫌疑).
- 没有做的: 换成累加的参照 (`BTBOFull` 的机制, 回报 §4 (乙)); `BTBOFull` 用的 `BTBOᴵ` 与 `Diagonal Uniform` 的是否同一个没有核对.

**压缩 (`YiLean*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiLeanCore`, `YiLeanFold`, `YiLeanLegal`, `YiLeanTw3`; `YiLeanTower` 只依赖 Core; 验收 `YiLeanAccFin`, `YiLeanAccTest`. 接口在 `probes/_build/2.8.0.2/agda/OCF/Lean/`.
- 定下的: 新块; 折叠与各行; `Ψ-lgl`, `Ψ-cp` (对任意派发); 闭项 `T₃`, `T₃-legal`, `F-up`; `Legal-tw`, `Legal-Λ`; 值 `lower₁`, `lower₂`, `T₃-Ω₂`.
- 量行数: `agda --html` 后跑主审临时目录里的切片脚本, 根取 `YiLeanCore` 的 `tw`, `plus`; `YiLeanTw3` 的 `T₃`; 再加 `T₃-legal`.
- 接着做 (回报 §6, §7 与主审的复核): 一切有限 n 与 ψ₀(Ω_ω) 的下界 (要对层号一致的关系族, 执行方估约 800 行, 是估计); 与旧 `T₃ᵐ` 的比较; 派发完全性的一般定理; 公共上界含 Ω 结点时的折叠 (新块没有守卫, 旧块上第 4 步的障碍是否还在没有判定; 位置带相关的合法性证明会带来 "两份证明两个位置").
- 最占行的是 `YiLeanLegal` (131): 加法的三条引理按三种层号形状分情况; 执行方判断再省要改归纳—递归的结构, 没有试.

**值单调, 构造 (`YiVmCon*`).** 依赖序 `YiVmConExact`; 然后 `YiVmConLPO`, `YiVmConInst`, `YiVmConChain`. 各 1.5G 以下.
- 定下的: `XEmb`, `XEmb-limˡ`, `XEmb-suc`, `≈→≅`; 定义域 `≼ˣ`, `≼ᵖ` 与其上的 `embᵖ`, `VMᵖ`, `Cruxᵖ`; `VMᵇ`; 四个闭实例.
- 证法的否定: `tri→LPO`, `cplˣ→LPO`, `cplᵖ→LPO`.
- 条件: `btbo-p` (前提 `ChainP`, 类型在回报 §3); `tri→vm`, `cpl→vm`.
- 接着做: 对最终选定的树证 `ChainP` 的 n ≥ 1 (允许错开下标); 回报 §5 说了累加的链上难在左加平移不保值. 链不累加的设计候选若做成, 这一步可能可以对 n 归纳 (主审的判断).
- 可复用: `XEmb` 一套对任何 "由推导造嵌入" 的地方都能用; `≼ᵖ` 是值单调目前已知的最宽的无条件定义域.

**值单调, 否定 (`YiVmNeg*`).** 依赖序 `YiVmNegBase`; `YiVmNegSeg`, `YiVmNegIrr`; `YiVmNegBound` (依赖 Seg); `YiVmNegChain` (依赖 Bound). 各 1.5G 以下.
- 定下的 (否定): `embVᴰ→LPO`, `embVᴰˢ→LPO`, `segTop→LPO`, `seg↔LPO`; `vm¬¬→MP`, `vmⁱ→MPⁱ`.
- 定下的 (正面): `probe-emb`, `probe-vm`, `emb-rel`, `vm-rel`; `bound-⊑`, `emb-fin`; `ch→btbo` (条件).
- 没有定的: `VMᴸ` 本身; 一般的 `EmbV`. 回报 §5 有第一个障碍的纸面例子与一条证明思路 (严格的树里借下一项的推导给前一段的像定界), 都没有编译.
- 与构造路 (`YiVmCon`) 的关系: 两路互不看对方; "保值" 与 "保初始段" 是同一种按值对齐的嵌入, 两边都得到 LPO.

**主线块上的值证明 (`YiLeanVal*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiLeanValRel`, `YiLeanValAdd`, `YiLeanValFold`, `YiLeanValFin`; `YiLeanValBreak` 依赖 Fin. 各 1.6G 以下. 回报是英文 (原文留档).
- 定下的: `lower-any`, `FOLD`, `CMP`; `lower-fin`, `lower-ω`; `T₃-own`, `T₃-Ωω`; `no-L` (新树上结构可比不成立).
- 条件: `btbo-p` (前提 `ChainP = ∀ n → Σ m → D.γ n ≼ᵖ read (co (pts m))`), `btbo-vm` (前提 `VMᴸ`).
- 接着做: `ChainP` 的 n = 1 再一般的 n (回报 §5: 卡在后继处值恰好相等, 树一侧要吸收律; 判断里给了两种够用的引理). 或换成链的形状不同的设计候选 (见第六批), 再把这里的值证明搬过去 (`FOLD` 是对折叠 `Ψ` 证的, 候选若改了折叠里的规则要重证相应的情形).
- 中途主审发过一条消息 (允许导入 `YiVmConExact`, 首选证 `ChainP`), 在留档的 "协调消息" 里.

**设计候选乙 (`YiDiag*`) 与甲 (`YiZero*`), 都在 `probes/OCF/Lean/`.** 两路是对照: 都把 ω 倍改成从零起, 只差链累加不累加.
- 乙定下的: 不累加的合法闭项 (`T₃-legal`, `root-mono`, `Ψ-low`, `Ψ-cp`, `top-mono`); 第 1 步 `read-pt1 : read (pt 1) ≅ D.γ 1`. 改了五处 (回报 §2), 其中 ω 倍从零起是照参照调的.
- 甲定下的: 累加的链上结构可比的否定, 对任何步进函数 (`nz-any`); 折叠层的对齐 (`readΨ`, `sω-F1`); 较弱判据的条件定理 (`c2′`, 前提 `Tr`).
- 乙接着做 (已续派): n ≥ 2. 障碍是非零目标层上极限层号的顶取部分和 (回报 §6).
- 甲的回报 §1 末有两条纸面判断, 其中 "外层链的累加是合法性逼出来的" 已被乙的编译结果推翻.
- 行数: 乙 112 / 213 / 437, 计入塔 511; 甲 112 / 356 / 374.

**候选乙的续做.** 留档里有两次回报与主审中途的两条消息 (加一条较弱的判据; 续派). 续做只交否定一侧: `no-γ₂`, `psum-row`, `no-termwise`. 回头接着做的两个方向都没有开: 放宽第一位置 (回报 §3 给了要加的子句的大致类型, 归作者定; 台账 B7); 部分和穿过折叠的吸收 (台账 C8).

**台账.** 2026-11-11 起, 各路的候选设计, 试过而放下的办法, 纸面判断都逐条记在 [IdeaLedger](../IdeaLedger.md).

**下一站的闭项 (`YiNext*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiNextCore`, `YiNextBase`, `YiNextFold`, `YiNextTop`; `YiNextTower` 只依赖 Core; `YiNextBaseline` 依赖 Top; 验收 `YiNextAcc`, `YiNextAccTest`.
- 定下的: `T⁺-legal`, `T⁺-term₀`, `T₃⊑T⁺`, `K⁺-form`; `Legal-K⁺`; `T₃+1≼T⁺`; `FromBTBO.btbo⁺` (条件); 行数 475.
- 没有定的: 读法; 被丢掉的位置对是否影响值; Ω 结点层号上完全的比较 (回报 §6 写了要的函数的类型).
- 接着做: 把只管 `tw 2` 的那个情形换成一般的 (位置带到公共上界的路径, 即旧块上的 "受支配的域"); 塔的第 4 项 (回报 §6 的判断: 保留时的分支族要对带结点的下标单调).
- 量行数的根: `YiNextTop` 的 `T⁺`, `T⁺-legal`; `YiNextTower` 的 `Legal-Λ`, `Legal-tw`.

**设计候选丙 (`YiFree`) 第一次失败; 同日重派 (简报只加过程要求, 回来后本文件与 [YiFree](YiFree.md) 重新生成).** 没有仓库文件. 留档里只有简报 (转录里没有回报). 经过与读法见 LOG 的 "独立样本一路失败". 读过的文件都在允许的范围内. 若重派, 简报要加过程上的要求 (先写块并编译; 写一个编译一个), 不加设计提示.

**`ChainP` 的否定 (`YiChainNeg*`, 在 `probes/OCF/Lean/`).** `YiChainNegLEM`, `YiChainNegAdd` (后者只用前者的 `val₁`).
- 定下的: `lem→chainP`, `no-negP`, `no-N1`; `triOn→chainP`, `n1-from`, `val₁`; `add1-strict`, `+ˣ`; 三条证法的否定 `add1→LPO`, `addω→LPO`, `cplˣS→LPO`; `vmʳ↔`.
- 接着做 (构造路): `TriOn (D.γ 1) (read (co (pts 1)))`, 再一切 n; 回报 §5 的纸面分析指出判定落在哪一支, 以及可以借 Cantor 范式一类的编码判定 (只在验收文件里).

**值证明搬到下一站 (`YiNextVal*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiNextValRel`, `YiNextValPath`, `YiNextValLgl`, `YiNextValFin`.
- 定下的: 转运 `co≅`, `T₃≅`, `F≅`; `≼ᵖ-≅`; `chainP-transfer`, `chainP-back`; `btbo⁺-from-main` (条件, 前提是主线的 `ChainP`); 下一站上的 `lower-anyⁿ`, `T₃-Ωωⁿ`, `T⁺-Ωω`.
- 可复用: 跨模块转运的写法 (树关系加合法性证明的路径对应); 以后再改折叠时照此搬值定理 (台账 V19).

**主线上证 `ChainP` (`YiChain*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiChainBase`; `YiChainOne`; `YiChainCond`, `YiChainBack`; `YiChainFlat`.
- 定下的: `chainP₁`, `γ₁≈`, `T₃-γ₂`; 工具 `transˣ`, `Abs.ABS`, `Abs.VABS`, `step`, `Phi.PHI`, `ψ⁰-flat`.
- 条件: `chain-cond`, `btbo-cond` (前提 `P1`, `P2`, 类型在回报 §3).
- 接着做 (回报 §5), 三条互不依赖: 主线折叠的值的上界 (反向的关系族; `P2` 要); 两个方向的嵌入给出定义域版的折叠单调 (`P1` 要; 只谈参照框架); 第 1 层以上吸收的两条结构事实 (`ABSΩ` 的假设; 只谈参照框架).
- 中途主审转告了否定路的归约 (局部二分), 执行方没有用到.

**两个方向的嵌入 (`YiEmb2*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiEmb2Le`, `YiEmb2`.
- 定下的: `VMˣ₂`, `VMˣ`, `p1₂`, `p1-one`; 归约 `btbo-cond₂`, `chain-cond₂`, `γ₂-cond`; `p2₂-0`.
- 接着做: `P2₂` 的 n ≥ 1 (只谈主线; 上界与吸收两路在做).

**第 1 层以上吸收的结构事实 (`YiFlat*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiFlatObs`, `YiFlatWit`, `YiFlatAbs`, `YiFlatChain`.
- 定下的: `HS-flat`, `HS-flatΩ`, `flatΩ-≺`, `absΩ`, `absΩR`, `X≺`, `κ≺`, `absorb₁`.
- 条件: `p2-from-fold` (前提 `FoldB`, 类型在回报 §3).
- `YiFlatObs` 是 `Uniform` §1–§7 的副本加一种观测; 若以后要精简, 这里是第一处.

**主线折叠的值的上界 (`YiUB*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiUBOne`, `YiUBRed`, `YiUBNeg`, `YiUBP2`.
- 定下的: `ub₁ˣ`, `lb₁ˣ`, `ub₁`; `no-UB`, `no-str`; `absorb2`, `FOLD2` (带前提 `Str`); `foldB₀`, `sucP₀`, `chainPt₀`.
- 条件: `btbo-str` (前提 `StrChain`), `p2₂-1`, `γ₂-str`.
- 接着做: 第 2 层以上的 `SucP` (回报 §5; 台账 V25). 中途主审发过两条消息 (目标收成 `P2₂`; 再收成 `FoldB` 并可导入 `YiFlat`), 在留档的协调消息里.

**测主线折叠是否超过参照 (`YiOver*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiOverRef`, `YiOverOps`, `YiOverMain`, `YiOverTwo`.
- 定下的: `over₂`, `≈₂`, `no-over₂`, `sucPᵛ`, `over-pt`, `low-pt`, `pt-shift`; 工具 `⊵`, `≤ₚ`, `up⁰`, `Φ-pres`, `+-comp`, `step-γ`, `O2ref`.
- 接着做: 定义域版; 不错开下标的 n ≥ 2 (第 1 层的吸收, ℕ 极限一支); 第 3 层以上 (按层号索引的关系族).

**第 2 层以上主线折叠与参照两向对上 (`YiSuc*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiSucWire`, `YiSucLx`, `YiSucGood`, `YiSucNode`, `YiSucPar`, `YiSucAbs`, `YiSucOne`.
- 定下的: `chainPt-top-1`; 工具 `par` (语境), `NodeTwo.result`, `refabs`, `cong₁`, `good-read`, `strict`.
- 条件: `btbo⁺-str` (前提 `StrChain`).
- 接着做: `BranchP n` (n ≥ 1; 回报 §5), 第 3 层以上, 极限层号. 中途主审转告了测量一路的结果, 执行方没有用到.

**沿链造前驱嵌入 (`YiPE*`, 在 `probes/OCF/Lean/`).** 依赖序 `YiPEBase`, `YiPEStep`, `YiPEStair`, `YiPEKey`.
- 定下的: `emb₁ⁿ`, `PEmb-shift`, `toLevel-+`, `shift-κ`, `Stair.stair`, `ψ⁰Ω-≺`, `key-lim`, `key-suc₀`.
- 条件: `btbo-FS⁺` (前提 `FUNC`, `KEYsuc`, `SpineT`; 类型在回报 §3).
- 接着做: `FUNC` (参照侧), `KEYsuc` 在层号 2, `SpineT` 在 m = 1 (回报 §5).

**严格的树上的值单调 (`YiLow*`, 在 `probes/OCF/Lean/`).** `YiLowBase`; `YiLowNeg`, `YiLowPos`; `YiLowChain`.
- 定下的 (否定): `embVˢ→LPO`, `embV→LPO`, `embX→LPO`. 定下的 (正面): `emb-ω²`, `vm-ω²`; `vmᶜ₀`, `S₀`.
- 条件: `FromVMᶜ.btbo`, `FromVMᶜ.btbo⁺` (前提 `VMᶜ`: 只在链上的值单调).
- 接着做 (判断): 在 ψ⁰ 层直接对链证 `Crux`; 或只对链点的结构嵌入 (见 `YiPE`).

**第七次独立审查 (`YiBtbo*`, 在 `probes/OCF/Lean/`; 审查者的临时文件由主审移入).** `YiBtboV2`; `YiBtboLower`.
- 定下的: `btbo⁺`, `btbo`, `src-btbo⁺` (无前提).
- 接着做 (判断): 同一办法 (规范化层号作中介) 能否给出严格超过 BTBO 的值, 或用到下一站以上.

**参照一侧的函子性 (`YiFunc*`, 在 `probes/OCF/Lean/`).** `YiFuncBase`; `YiFuncLim`; `YiFuncChain`, `YiFuncCrux`.
- 定下的: `func-nat`, `func-sω`, `func-L1`, `func₂`, `crux₂`, `chainStr₀`, `hst₀`; 工具 `BG.emb` (边界粘接).
- 条件: `func-red`, `crux-red`, `func-red₂`, `btbo-CS⁺`, `btbo-NX⁺`. 缺 `NEXT` 与 c ≥ 1 的 `ChainStr`.
