# 2026-11-10 各路回报的留档

> 作者 2026-11-10 要求: 回来的任务完整记录下来, 以后可能要翻回来看. 这里每一路一个文件, 存派发时的简报原文、中途消息、交回的回报原文与运行数字.
>
> **怎么读.** 回报是执行方写的: 其中的编译定理都经主审冷编复核 (见各文件表头指到的 `probes/LOG.md` 一节); 其中标作判断的话、规模估计、"下一步" 的建议, 是执行方的判断, 主审没有验证. 结论以 LOG, [RouteReview3](../RouteReview3.md) §5.12 与 [RESULTS](../../RESULTS.md) 为准, 这里是原始材料.
>
> **怎么生成.** `probes/Survey/scripts/agentreport.py` 从子智能体的转录里取原文; 只把本机路径换成占位符, 把原文的标题降两级, 别的不动. 用法见脚本文首. 以后每一路返回并复核后都照此留档.

## 1 总表

时间是转录里的时间戳 (UTC). token 一栏只列输出 token, 取自转录的 usage 字段并按消息去重; 完整的三项在各文件表头. LOG 里 "七路合计约 287 万 token" 取自各路完成通知里报的总数, 口径不同, 不与这里的数相加或相比.

| 路 | 留档 | 模型, effort | 起止 | 输出 token | 主审复核后的结论 |
|---|---|---|---|---|---|
| 乙线折叠, 构造 | [YiIrrFold](YiIrrFold.md) | Fable 5.2, xhigh | 13:02 至 13:30 | 178788 | 接口 `FoldRows` 已实填, 目标层 0 的完整递归折叠; 值在 ψ₀(Ω₁·ω) 以内互相 ≼ |
| 乙线折叠, 否定 | [YiIrrNeg](YiIrrNeg.md) | Fable 5.2, xhigh | 13:02 至 13:36 | 215798 | 接口未被否定且有模型; 定义域取得太宽时推出凭无关证据取数据的原则; 新块上合法性到 Λ |
| K4, 折叠的单调引理 | [K4Mono](K4Mono.md) | Fable 5.2, xhigh | 13:02 至 13:39 | 235774 | `Level` 族上折叠对单向的逐点关系在一切层单调 (定理); 层号平移与吸收不在关系里 |
| K3, 现成闭项的封顶 | [K3Cap](K3Cap.md) | Fable 5.2, xhigh | 13:02 至 13:31 | 167112 | 五个现成闭项都只得到封顶的编译事实; 没有一条是值上界 |
| 差树 `SumOne` 的 `T₁` 的上界 | [SumOneUp](SumOneUp.md) | Fable 5.2, xhigh | 13:02 至 13:59 | 294330 | 上界未走通, 没有否定; 新增两站的序数值验收 |
| 乙线第一次回灌 | [YiIrrFb](YiIrrFb.md) | Fable 5.2, xhigh | 13:33 至 14:13 | 258141 | 层号字面为 0 或 1 的片段上做成; 闭项 ψ₀(Ω̂ 2) 合法, 值下界 ψ₀(Ω₂) |
| 带高度族闭项 `T⊤` 的值 | [TTopVal](TTopVal.md) | Opus 5.5, high | 14:00 至 14:16 | 84078 | 值未走通, 止损触发; 新增 ψ₀(Ω_{Ω²}) 的带标签参照树与一个等价条件 |
| 乙线第 3 步, 构造 | [YiLvFold](YiLvFold.md) | Fable 5.2, xhigh | 15:40 至 16:36 | 326027 | 对目标层参数化的折叠做成, 有限层号与 ω 上派发完全; 塔的第 3 项只有合法闭项, 读法未定; 合法性对任意派发成立 (2026-11-11 复核) |
| 乙线第 3 步, 否定 | [YiLvNeg](YiLvNeg.md) | Fable 5.2, xhigh | 15:40 至 16:30 | 301295 | 层号的合法性必须作为相关数据到达比较处; 五类写法被编译定理排除; 规范槽位与目标层 0 上的限制形式是正面结果 (2026-11-11 复核) |

七路都没有改已有文件, 没有提交. 值前沿在这七路之后不变, 仍是 ψ₀(Ω_{Ω·ω²}) (`EmbVVInstO2.vv-ω²`).

## 2 回头接着做, 从哪里入手

每条先写编译过的事实, 再写执行方对下一步的判断 (未验证). 细节在各自的留档里.

**乙线折叠, 构造 (`YiIrrFold*`).** 入口 `YiIrrFold`.
- 做成的: `fold-rows`; 定义域 `Only0 × Legal × Seed`; 值的三族互相 ≼ (`YiIrrFoldValue`).
- 没做成的: 定义域取 `Only0 × Legal` (不带 `Seed`) 时的实填, 未走通, 没有否定; 它与 `Unsquash` 等价 (`seed-all→unsquash`, `unsquash→seed-all`). 检查器拒绝的五种写法连报错原文在 `YiIrrFoldSeed` §0. Ω₁² 没有值定理.
- 后续已经接上: 第一次回灌 (`YiIrrFb*`), 再往后是在跑的第 3 步.

**乙线折叠, 否定 (`YiIrrNeg*`).** 入口 `YiIrrNeg`.
- 定下的: 模型 `model`; `wide→irr-search`, `wide→irr-decide` (定义域太宽); `Legal-Ω̂` 到 `Legal-Λ`; `locate→irr-search` (一般目标层的槽位必须是数据).
- 留下的: `Dom = Only0 × Legal` 这一取法只写了未走通, 按规则待独立审核; 对接口字段的两条意见 (`Legal` 缺相关的下界字段; `next` 的 `w`, `b` 可标无关) 没有处理, 因为接口定稿后不改.

**K4 (`K4Mono*`).** 入口 `K4Mono`.
- 定下的: `ψ-⊑`, `ψ⁰-monoᵖ`, `ψ⁰-congᵖ`; 否定 `no-below`, `no-cross-level`, `incomplete`.
- 没做的 (执行方列的): `Wide` 版的传递; 高层上 `⊑ᵖ` 与 `≼` 的关系; 把层号平移纳入的关系; 移植到差树或高度树.
- 用它之前要知道: 它在 `Level` 族上, 那里没有闭包, 没有状态与世界; B 簇的 23 个停点没有一条是它的直接实例 (执行方核对了其中 3 条的陈述, 其余 20 个文件没有逐个核对).

**K3 (`K3Cap*`).** 入口 `K3Cap`.
- 定下的: 类型封顶三个 (`no-Ω₂-top`, `no-ω-bottom`, `no-Ω-height`); 类型不封顶但运行上不派发的两个 (`first-item-rep`, `driven-rep`, `ΦX-const`).
- 没做的: 条件覆盖 (简报里的甲) 一个也没有, 卡在各候选都没有跨站的值比较; `Third` 与 `OutputDriven` 另两处损失在闭项的实际运行里是否到达, 没有验证; `RecB` 的结果只到签名一级.
- 各条否定只否定写明的下标类型形状, 不否定换下标类型或换派发规则后的同族候选.

**`SumOne.T₁` 的上界 (`SumOneUp*`).** 入口 `SumOneUp`. `SumOneUpRed` 编译时常驻约 3.4G.
- 定下的: `Sω-vlab`, `S¹-vlab` (两站的序数值), `low¹-T₁`, `lab-mono`, `runG`, `chain≈`, `T₁≇`.
- 条件定理, 前提未证也未反驳: `upper-lab : StageBelow → Upper`; `fb-upper : CellStep → …`.
- 下一步的精确目标是 `S²-target` (`upper→Open₂` 说明它是必要的). 执行方的判断: 需要第 1 层差树到标准形项的指派, 与 `runG` 的第 1 层版本; 规模与 `DVal`, `KVal` 同量级或更大; K4 不蕴含它.

**第一次回灌 (`YiIrrFb*`).** 入口 `YiIrrFb`.
- 做成的: `fb-rows`; `Ω₂-fold-legal`; `Ω₂-lower`; `feedback-dom`.
- 没做的: 值的上界; `ψ₀ ≡ ψ` 的无条件版 (`agree` 要 Funext, `agree-lim-is-function-equality` 说明原因).
- 执行方对下一步困难的三条判断, 是第 3 步简报的来源之一: 保留行的槽位要与结点的层定义性相等; 候选出路是把目标层的折叠写在读回域 `Raw m` 上; 层号含 `lim` 或 `lc` 时第一次要公共界下的判定型证据.

**`T⊤` 的值 (`TTopVal*`).** 入口 `TTopVal`; 编译它要 14G 的堆上限 (执行方记的常驻峰值约 5.7G), 另两件 6G.
- 定下的: `Y⊤-lab` (参照树); `vv-T⊤-if`, `vv-T⊤-only-if` (等价条件 `Up × Low`); 第 0 项 `e₀`, `up₀`, `low₀`; `no-NF-brᴱ`, `no-NF-brᴸ` (现有标签工具够不到第 n ≥ 1 项).
- 缺的 (执行方的判断): (i) 容纳 ψ₁(a), a ≥ 2 的新标准形族与对应的标签世界克隆; (ii) 链码上一般的码的读法 (现在逐码手写). 规模估计 5 千到 1.5 万行, 执行方自己注明这类估计历史上偏低.
- `T⊤` 读作 ψ₀(Ω_{Ω²}) 仍是判断.

**乙线第 3 步, 构造 (`YiLvFold*`).** 核心是 `YiLvFold` (模块 `Fold`, 以派发 `way` 为参数); 依赖序 `YiLvFoldAdd`, `YiLvFoldBase`, `YiLvFold`, `YiLvFoldFin`, `YiLvFoldLim`, `YiLvFoldTw3`.
- 做成的: 对目标层参数化的折叠, 对任意派发合法 (`ψ-legal`, `ψ-nested`, `ψ-position`); 有限层号上派发完全且不多保留 (`complete-fin`, `sound-fin`); ω 及其下完全 (`complete-ω`, `complete-sub`); 闭项 `foldᶠ`, `fold-Ωω`, `fold-Ωω1`, `T₃` 合法.
- 没做成的: 含极限的一般层号上派发的完全性 (`bare-incomplete`, `branch-complete→lpo`); 所以 `T₃` 的读法未定. 三站都没有值定理. 与 `YiIrrFb` 的字面一致没有证.
- 读的时候注意: 合法性对任意派发成立, 所以 "闭项合法" 本身不说明强度; 要看派发完全性的定理或值定理.
- 执行方对下一步的判断: 相关证书的变体要限制形式的位置保持, 一致的定义域, 每条合法性引理配一条 "与限制交换", 链点带相关守卫; 这一变体没有写代码. 主审派发前建议的 "写在 `Raw K` 上" 这一路没有试 (执行方的理由在回报 §4).
- 可复用的部件: 对层号一般的加法 (`plus`, `Alg`, `add-lgl` 等), 按槽位造保留结点 (`nodeAt`, `node-lgl`), 各层的链 (`Chain`, `ChainLegal`).

**乙线第 3 步, 否定 (`YiLvNeg*`).** 没有入口文件; 六件按依赖序是 `YiLvNegCompare`, `YiLvNegCert`, `YiLvNegKeep`, `YiLvNegCanon`, `YiLvNegRestrict`, `YiLvNegCum`.
- 否定, 都只否定写明的写法: 合法性只无关地给比较 (`compare-irr→irr-search`, `compare-read→irr-decide`); 证书无关且定义域对一切带守卫的分支遗传并有保留律 (`keep→irr-search`); 层号合法性进证书但经无关守卫遗传 (`lv-irr→irr-search`); 派发只读裸层号而处处正确 (`bare-way→lpo`, 结论是 LPO); 位置保持写成两份独立证书且槽位取自 `compare` (`no-by-compare`); 把塔的分支换成累加归一后的读回 (`cum-tower-not-legal`).
- 正面, 以后设计折叠时可以直接导入: 规范比较 `ccompare` 及 `ccompare-slot`, `ccompare-levels`, `ccompare-shift`; 互为延伸的位置的三路 `prefix→tri`; 限制与一致 `restrict`, `restrictDom`, `Coh`, `CohDom`, `ψ-legal-restrict`, `ψ-legal-coh`, `read0-legal-coh`; 链上归一的部件 `cum`, `cum-legal`, `norm-guard`, `norm-directed`, `norm-level-legal`, `tw3-chain-step`.
- 没写成的 (执行方列的, 各带缺的引理): `IrrSearch → CompareIrr`; `ccompare` 的方程分量与证书无关 (缺层号相等证明的唯一性); 见证层号是不是 `tw 3` 的折叠走到的链点; 一般目标层上的限制形式 (当时没有可检验的折叠).
- 读的时候注意: 前三类否定的结论是 "凭无关证据取数据" 的原则或 LPO, 前提在排中律的一个实例下有模型, 所以它们说的是 "这种写法拿不到数据", 不是矛盾.

## 3 同一天外部模型的两路 (作者转发的摘要原文)

这两路由外部模型执行, 完整报告在它们各自的文件里 ([YiWall](../../OCF/Align/YiWall.lagda.md), [YiIntr](../../OCF/Align/YiIntr.lagda.md)); 下面是作者转发给主审的摘要, 原文. 主审的复核与读法在 [第五次路线审查](../RR5-SoftStops.md) §1 与 LOG 的 "2026-11-10 晚: YiIntr 复核; 第五次路线审查与最小实验 RR5Irr" 一节.

第一路 (YiWall):

> 已交付 YiWall (probes/OCF/Align/YiWall.lagda.md)。本轮明确了障碍范围，尚不能据此认定必须 Funext，或关闭只读树路线。
>
> - 编译定理： 极限行加有界位置保持，推出同一合法树列换证书后的整个输出函数相等。范围仍是窄实例；最小接口已有编译闭实例。
> - 条件定理： Funext 加只读树的两个恒分支 gt 检验，推出 WLPO。Funext 仅作前提；最小全域前提另给经典外延模型的纸面可满足性说明。
> - 判断／未证： 未推出一般函数外延；去掉空域相等或 Funext 后，尚未推出 WLPO。完整 FoldRows0 仍未实填。无有限测试。
>
> 冷编均只删自身接口、依赖用缓存，单路 +RTS -M6G -RTS：YiWallLim, YiWallTree, YiWallConditional, YiWall 退出码都是 0。
>
> 导入闭包干净，编译器图一致；切片正对照、源码审计及导航检查通过。README／LOG 已补记，既有数学文件未改，未提交或推送。

第二路 (YiIntr):

> 骨架可通过检查，gt 起点能直接从结点字段取得；但本次 tw 3 不满足原 Legal.irr，尚不能原样采用。
>
> - 编译事实： 6 件均以 6G 删自身接口冷编，退出码全为 0。
> - 编译定理： 第一支条件推出 Below；但内置位置证据可使同一坐标的两份守卫返回不同树。
> - 有限构造： 已到 tw 0..3；Ω̂ 带 Ready 前提，未交全塔或 Λ。
> - 成本估计： 按现有文件粒度约 25 件、4204 行；一致性问题未解决，完成成本暂无可靠上界。
>
> 完整报告、冷编清单与成本账 (probes/OCF/Align/YiIntr.lagda.md) · 骨架原文 (probes/OCF/Align/YiIntrCore.lagda.md)
>
> 只新建 YiIntr*，未改已有文件、迁移整线或写完整 ψ。

(第一路摘要里的冷编结果原文是一张四行的表, 这里并成了一句; 其余逐字.)
