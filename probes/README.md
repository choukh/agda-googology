# probes 接手入口

更新时间：2026-11-07。这里维护**当前状态与阅读顺序**；成果目录、历史原因和逐轮记录分别存放，不再把流水追加到首页。

<a id="current-state"></a>
## 当前任务与目标

最终目标是：在 [AGENTS 纲领](../AGENTS.md) 下，以布劳威尔树写出 ψ₀Λ 的合法闭项，证明序数值至少达到 EBO，再争取同值；树侧前三层的完整成本须小于 1513 行标杆。内部 View、使闭项可执行的证书与必要依赖不能漏算。

四层依次是树的定义、加折叠与 FGH、加使闭项可执行的合法性证书、加强度验收。预算比较前三层；有合法证书不表示已有终点强度。

**当前阶段：证明改值简化闭项的实际值。** [冻结的新完整闭项](OCF/Align/RadicalValueNativeFinal.lagda.md) 仍运行原 HB ω² 完整高源，带字面第一位置的同类型内部 View 与 FGH。现在已正式证明 **ψ₀(Ω_Ω)+ω ≤ 新闭项值**，并排除它不高于 BTBO；另证内部原完整 rowB 在新解释器中与 BTBO 同值，非零参数1的整条跨层反馈回收成立。值证明入口与精确量词见 [TotalValue](OCF/Align/TotalValue.lagda.md)，98件冻结证明已主审单6G从头复编，源码/编译器本地闭包一致。**完整高闭项的准确值、旧 ψ₀(Ω_{Ω·ω²}) 下界及具名上界仍未证明，不宣称达到 EBO，也不算超过历史前沿。** 高域已覆盖原全Ω̇并由原ψ/Ψ完整保持；当前在补它与跨高度下降的观察耦合，未扩建闭项；全部新增证明只在第4层，生产定义不改。执行切片仍为7351→1418（新侧含第一位置View），只是语法近似，非1513完整认证。新旧值义务与证明路径见 [EBOEndgame §13](Survey/EBOEndgame.lagda.md#13-冻结新闭项的值证明)。

**保值对照保留。** [TreeEmit](OCF/Align/TreeEmit.lagda.md) 改写原 EmbVV 的完整高实例，仍过 **ψ₀(Ω_{Ω·ω²}) 双向值验收**：逐原树直接生成底输出，证书沿原实际反馈轨道运输，全部高度／行同形，无函数外延。定义与证书导入闭包记号禁用0。**本例依赖切片增加132行，不计压缩成果**：原高层运行器与原合法性证明仍在；下一优先项是新程序自身的结构证书生产。裸数据下降删除已有正式值反例，实际生成域仍开放。未宣称树自足或达到EBO。范围、切片口径与后续义务见 [EBOEndgame §11](Survey/EBOEndgame.lagda.md#11-转到真正树侧闭项的保值改写)。

**上一轮标杆对照单独保留。** [DirectClosed](OCF/Align/DirectedViewDirectClosed.lagda.md) 是“记号＋良基性→树”的完整EBO标杆改写；它仍依赖记号，不能把它误称为旧树侧闭项简化，其成本不与本例跨口径并列。配套[前缀规则](OCF/Lean/DirectedPrefixBuild.lagda.md) 提供单向值证明经验，见 [§10](Survey/EBOEndgame.lagda.md#10-作者授权从已知值闭项定向改写配套修改值证明)。

**直接构造的对照仍保留。** [OutputDriven](OCF/Lean/OutputDriven.lagda.md) 已交无参数 closed／closedGrid、合法性与 FGH：每塔槽运行完整高源，由真实输出更新整底世界、读取新界后再运行，全部 QL/PH 重建并完成逐底下降，最终输出进入下一外阶段。全方格闭项显式执行所有有限“深度 × 更新轮数”配置，不假设同步对角充分。**新闭项已完整；EBO 读法、内部 View 验收及最终成本尚未完成，也未证明它高于旧 TΛ。** 构造见 [EBOEndgame §8](Survey/EBOEndgame.lagda.md#8-作者指定的双路后继旧闭项估值与新闭项构造)，值审查见 [§9](Survey/EBOEndgame.lagda.md#9-暂停扩建后的实际值审查)。

本轮对同一闭项证明了 [ε₀ 校准下界](OCF/Align/GridBaseTowerAccept.lagda.md)，不作为超过已有前沿的进展。完整零底与种子、轮数无关；最底指标的多轮更新是追加固定增量，不能直接读成反复 c ↦ ψ₀(Ω_c)。但 [全部可数高度上的原洗法保值](OCF/Align/GridCheckCountableSan.lagda.md)，所以也不能用高底的 Er 删根压低零底。BTBO 标尺仍缺完整带前缀回灌链的比较：原零叶给 1、BTBO 给目标 Ω，且 keep 会先重建坐标再读分支。未获 BTBO／EBO 下界或整体上界，没有否定原路线。

旧闭项一路：[TLambdaAudit](OCF/Lean/TLambdaAudit.lagda.md) 给全部底参数的真实高类型反馈链；[TLambdaAuditRank](OCF/Lean/TLambdaAuditRank.lagda.md) 已证原地板的秩投影值全零、原完整第一站非零，精确排除直接用秩值作下降上界。**这不否定旧 ψ₀(Ω_{Ω·ω}) 猜测，但该猜测仍缺对回灌和全部下降的整体值模拟；目前没有更精准的已核准具名值界。**

两路12新数学模块及汇总已主审单6G冷编。OutputDriven 源码闭包47模块／本地35，成功编译器图本地集合一致、记号禁用0。闭项及合法FGH的补别名切片为同步对角1148／全方格1160；未含新增内部View验收，不作为完整1513成品认证。[CircuitGenerated](OCF/Lean/CircuitGenerated.lagda.md) 的给定未来世界重用结果继续保留；新闭项通过各世界重证全源路径，不依赖通用输入迁证。

[UniformCore](OCF/Align/UniformCore.lagda.md) 已给任意种类参数的同世界生成关系、原 Int 保持、有界分派，以及能生成编码并在后继／有覆盖极限处闭合的读回包。主审冷编 12 件、源码与编译器本地闭包均 96 件且干净。**这批是结构信息，没有新强度，也没有接成同一全种类事件程序。** [EventGenerated](OCF/Align/EventGenerated.lagda.md) 的原高源、非零内枝及全未来同步后缀的迁回 Shape 仍保留；更强读回等式和完整 Run／后继反馈闭包仍未证。

终点检查的边界继续有效：[旧 Gd 不能免费随世界搬运](OCF/Lean/CircuitBoundaryGd.lagda.md)，[遗传未来 Stable 不能覆盖原全地板](OCF/Lean/CircuitKernelStableBoundary.lagda.md)。后续[合法源反例](OCF/Lean/CircuitLegalNegGd.lagda.md) 更在原 Sb 1 上补齐输入 LgB；触发坐标仍非法，通用迁移被否定，**实际 Φ 输出域没有被否定**。本轮正面定理只消费真实输出，未把失败合同强加回输入。[TerminalFoldAccept](OCF/Align/TerminalFoldAccept.lagda.md) 的完整参照覆盖仍待候选实填。新增9件连同前批3件已由主审单6G冷编；干净闭包本地44件，源码与编译器集合一致。

此前接手核查已清理手册中的旧“待定／在跑”：1513 标杆与封存维护已有作者后续决定，MonoPort2 等早已返回。证据与隐含约束见 [再次查缺补漏](Survey/ResearchHistory.md#10-再次查缺补漏决定的后继与当前证明的适用域)。接手起点、封存范围和四层验收继续以下文及 AGENTS 为准；没有因文档整理或本批证明而重开封存路线。

原 EvFold 双事件闭项切片约1423也未含新增高层内部View，和当前新闭项分别记账。终点验收接线不进入成品依赖；没有从这些成本数字推出新强度。历史资产仍见 [机制继承图](Survey/ResearchHistory.md#23-机制继承与后继结果第二次接手核查)。

[ThirdRichLeg](OCF/Lean/ThirdRichLeg.lagda.md) 的全种类合法化及合法低坐标覆盖已由主审 6G 冷编复核；本轮又证其保持原当前 Gd。ThirdRunFamily 三件现已补齐主审冷编：真实有界运行族、逐目标局部世界，以及零外补齐推出 WLPO 的限定否定。局部反馈不等于原底世界更新，也未证明 Er 不再洗掉 Ω 分量。**没有新增具名强度，尚无达到 ψ₀Λ 的闭项与值证明。**

旧高路线仍按 [RouteSeal](Survey/RouteSeal.md) 的作者决定封存或承重维护；此次只查阅、盘点和解释，不重开。数学定理有效、当前是否投入、设计是否达到树自足，须分别判断。

## 接手前实际起点（按提交核准）

已直接读 Git 对象：11 月 3 日的 8346f53、11 月 4 日的 a5b202c、11 月 6 日的 0546568（接手前 HEAD）。下表各闭项都有实际定义、最终输出合法性证明和 FGH；**精确高度未验收不等于构造未完成**。这也不代表全部中间层 View 已完成。

| 提交中的实际成果 | 已完成的构造 | 强度与续研边界 |
|---|---|---|
| a5b202c：[SumOne](OCF/Align/SumOneClosed.lagda.md) | T₀、T₁、Lg-T₁、fgh | [SumOneAccept](OCF/Align/SumOneAccept.lagda.md) 已证 T₀ 与 BTBO 同值、T₁ 严格超过 BTBO；ψ₀(Ω_{Ω+1}) 精确读法仍是判断。 |
| a5b202c：[SumHt](OCF/Align/SumHtClosed.lagda.md) | Tω、T²、Lg-T²、fgh | 读到 ψ₀(Ω_{Ω²}) 是判断；坐标写法后来封存作对照，不能把它默认为现役架构。 |
| 0546568：[HtFeed](OCF/Align/HtFeedClosed.lagda.md) → [HtOut](OCF/Align/HtOutFeed.lagda.md) | 对全部合法高度的闭项；高度由原折叠输出生成的 Fb、T-fbω、Lg-T-fbω、fgh | 已实际越过“只给定高度”的组织阶段；高读法与跨实例值关系未验收。HtFeed/HtOut 不属于旧坐标族的封存范围。 |
| 0546568：[HtTowerF](OCF/Align/HtTowerFClosed.lagda.md) → [HtTowerN](OCF/Align/HtTowerNFb.lagda.md) → [DiagK](OCF/Align/DiagKInst.lagda.md) | 双种类闭项、第 2 层输出回灌、无条件 Tdg₂ 及合法性、FGH | Tdg₂ 读 ψ₀(Ω_{Ω₃}) 是判断；实际两族对角与条件于 LevelFold 的全塔接口必须分开。 |
| 0546568：[FamFold](OCF/Align/FamFold.lagda.md) | 真实输出的族读回与世界链；全 n 的 pkg、towerDown、Tlv、T∞、合法性与 FGH | 有限目标的族化实填，不需 UIP；高层最终仍下降到固定 Ht 再由双种类 T⁺ 坍缩。旧高读法已被骨架审查质疑，尚无值界；不能抹去实际回路，也不能冒称任意目标均已解。 |
| 0546568：[EvFold](OCF/Align/EvFold.lagda.md) → [LvFb](OCF/Align/LvFb.lagda.md) | 固定有限外界上的真实输出回灌、事件折叠闭项；后继的增量极限改贴、码上的更新与 T∞c | no-coh-ev 只否定指定证据族；LvFb 的增量极限已不在其前提内。码上更新已实现，ω 槽的运行使用和任意高度目标仍须分别查，不沿用旧障碍作总否定。 |
| 0546568：[CRw](OCF/Lean/CRw.lagda.md) → [RecB](OCF/Lean/RecB.lagda.md) | CRw.TU2；RecB 全 TN/TD 族、Tω、LgB-Tω、fghω | 读法分别 ψ₀(Ω_{Ω·2})、ψ₀(Ω_{Ω·ω})，尚无精确值验收。[SameV](OCF/Lean/SameV.lagda.md) 已给 CRw 的条件值比较，不能凭有限测试传给 RecB。 |
| 0546568：[Third](OCF/Lean/Third.lagda.md) | nodeG、折叠与路径合一、TΛ、LgB-TΛ、fghΛ | 是同期完整合法闭项，读法在 RecB 附近是判断；三处具体损失尚待处理，完整 Λ 折叠未交付。 |

接手应先消化这些实际成果，再评估继承、修正或重写；不能因值定理较少，就重新从最低已验收站攀起，也不能只按最高估计挑路线。提交依据及声明核查见 [研究历程](Survey/ResearchHistory.md#21-接手时点的提交核准)。

表中列主要闭项族，构造之间不默认为有值比较或机制继承。正面工具还包括 [TLRuleSpec](OCF/Align/TLRuleSpec.lagda.md) 的闭包值规格、[TreeLang](OCF/Align/TreeLang.lagda.md) 的最小级集合定理、[TL2](OCF/Align/TL2.lagda.md) 的有界异型族升界，以及 [MonoPort9Cov](OCF/Align/MonoPort9Cov.lagda.md)、[ValNew](OCF/Align/ValNew.lagda.md) 的限定域值定理。它们与各自的限制一起继承。

## 已验收强度与机制参照（不等于重启点）

以下“定理”指既有编译记录及具名声明；本次历史整理核对了来源，未重新编译整个仓库。

| 资产与维护状态 | 已有结果 | 必须保留的边界 |
|---|---|---|
| 作者成品 [BTBO](../src/OCF/BTBO.lagda.md)，源码封存 | [BTBOFull](OCF/Align/BTBOFull.lagda.md) 的 BTBO≈：序数值为 **ψ₀(Ω_Ω)** | 基本列与参照不同；不能从同值推出 FGH 相同。它是结构范本和已知基座。 |
| [Free 闭项](OCF/Free/Closed.lagda.md)，干净定义资产 | ψ₀(Ω_{Ω·2})；[Bridge](OCF/Free/Bridge.lagda.md) 把验收接到主线 | 树与证书记号无引用，不等于定义已由树自身生成。验收模块不进入成品闭包。 |
| LadderNF/Mono，封存族中的可继承机制 | 参数化闭包；[OrdLabAccept](OCF/Align/OrdLabAccept.lagda.md) 的 nf-main、mono-main 已给原主线标签桥，Mono 达 ψ₀(Ω_{Ω·ω}) | 早期 Accept 的“仅克隆”状态已更新；节点文法的记号来源仍须记账。 |
| [EmbVV](OCF/Align/EmbVV.lagda.md)，封存但承重 | [vv-ω²](OCF/Align/EmbVVInstO2.lagda.md)：**ψ₀(Ω_{Ω·ω²}) 的序数值验收**，无未填强度前提 | 这是已有高值定理。码名 ω² 不表示指标 Ω²。 |
| [CrossM](OCF/Align/CrossMClosed.lagda.md)，封存但承重 | 无条件合法闭项与 FGH；原 T⊤ 读 ψ₀(Ω_{Ω²}) | 该精确强度仍是判断。近期高种子验收只是旧结果串接，不是新 EBO 站，也不撤销封存决定。 |
| 差树及带类型折叠，接手前主线成果 | 具体完整闭项见上表；[MainView](OCF/Align/MainView.lagda.md) 补了部分实际类型的内部 View | 续研对象已在 BTBO 上方附近；终点缺口不能抹去这些构造成果。各族合法性、View、读法与值定理分开查。 |
| [EboLean3](OCF/Align/EboLean3.lagda.md)，验收尺与成本标杆 | 完整 EBO 参照树；前三层累计 **1513**，加标签 **1533** | 1513 包含良基、基本列封闭、树和可执行 FGH；不能只数新文件或隐藏导入成本。 |

## 接手阅读顺序

1. [AGENTS](../AGENTS.md)：不可违背的纲领、树自足目标、可修订方法和作者决定的边界。
2. [研究历程与转向原因](Survey/ResearchHistory.md)：先理解为何封存翻译加重的高路线，以及后来主线已经在 BTBO 上方附近完成了什么；附提交核查、经验、勘误和本轮失误。
3. [第一次路线审查](Survey/RouteReview.md) → [封存决定](Survey/RouteSeal.md)：理解哪些机制应继承，哪些架构不能因“已有高结果”自动续建。
4. [成果目录与研究账](RESULTS.md)：查具体族、后续更正、翻译账与否定定理范围；目录中的旧“下一步”不是派发。
5. [2026-11-06 阶段快照](Survey/Stage-2026-11-06.md)：看当时 A/B/C 线、四层困难与成本，不能拿它覆盖全仓库已有高值定理。
6. [开发手册](Survey/EBOHandbook.md)：研究与协作反复出错的模式。需要原始过程时，再检索 [LOG](LOG.md) 和 [本轮接手纪要](HANDOFF-2026-11-07.md)。

历史导读不是所有证明的替代品。选中某机制前还须读实际定义、陈述和前提，核对后继结果；不能停在某篇旧入口的判决。

## 文档分工与更新方式

| 文档 | 回答的问题 | 更新方式 |
|---|---|---|
| 本页 | 现在要做什么、已有基座是什么、先读什么 | 当前任务或作者决定变化时替换摘要，保持简短；不追加逐轮流水。 |
| [研究历程](Survey/ResearchHistory.md) | 为什么走到今天；哪些选择改变过，原因是什么 | 新的重大转向补因果与来源；区分作者决定、定理、测试和判断。 |
| [成果目录](RESULTS.md) | 某族做到了什么、后续谁更新了它、翻译成本在哪 | 在相应族补更新链接；证明档位不代替维护状态。封存分类引用 RouteSeal，不复制另一套名单。 |
| [LOG](LOG.md) | 每轮具体做了什么，编译和复核情况如何 | 按时间追加；历史错误保留，由顶部更正导航指向后继结果。 |
| [接手纪要](HANDOFF-2026-11-07.md) | 本次接手曾作过哪些判断、怎样纠偏 | 保留原顺序，不再充当第二份更新日志。 |
| [RouteSeal](Survey/RouteSeal.md) | 作者封存了什么，怎样维护，何时允许重开 | 沿用原维护政策；依赖、复核和验收串接不自动构成重开。 |
| Stage 与各次审查 | 某时点看到了什么，提出过什么建议 | 保留时间与作用域；后续进展用入口和更正链接覆盖，不改写历史结论。 |

源文件继续原位保存，避免破坏 Agda 模块路径、导入与可复现性。新定义仍按 AGENTS 放 probes；不改 src 和 archive，不为目录整齐批量搬数学文件。

## 翻译账

完整的 [逐族翻译账](RESULTS.md#翻译账) 与历史否定范围保存在成果目录。CrossNested 草稿已停止。ThirdRichLeg 没有新增树节点或按记号阶段分类的字段；额外累加项是为覆盖原分支所选的实现，不是已证唯一形状，Ctx 方法已有 LHRec 前例。局部构造与准入的切片 440 行，加合法坐标覆盖 561；它不含完整闭项、View、折叠和 FGH，不能据此宣称低于 1513 标杆。既有截面更新也不是本轮首次实现，详见 [机制对照](Survey/ResearchHistory.md#23-机制继承与后继结果第二次接手核查)。EventReturn 继承原事件与 Int 双递归机制；EventGenerated 新增实际层对应、双向坐标转换和捕获／同步域的区分，没有新增记号阶段字段，也没有因验收反改旧定义。它们仍是摆脱侧研究，不据此打开新攀爬站。独立关系文件不计作新的完整成品成本；原双事件 1423 的口径及限制见 [实验入口](OCF/Align/EventReturn.lagda.md)。

定向简化账：DirectedView 两版没有新增树节点；共尾视图仍读自记号，NF／InG／GB及记号序良基性仍在，不能列为树自足。第二版从执行切片删除旧基本列及相应转换等式，是删去表示往返；等式保留在验收文件。DirectedPrefix 的单向规则由树构造子推出，没有记号阶段字段；泛反向与全域值单调的失败已编译为否定。此次是作者主动要求在新文件改写既有定义，不是用验收便利反改原前三层；原闭项全部不动。

TreeEmit账：继承原Q形状、非零折叠、cap和世界更新，没有新增记号阶段字段；Pointwise与move只用字面同界、同坐标的实际轨道。不再生成底目标的Run／Ordˢ中间输出，仍通过旧GᴺTᵠ生产新证书，因此完整依赖增加132行。本例提供了保值重写与失败成本诊断，未宣称删掉原翻译形态或提高强度；原封存代码没有反改。

本轮改值简化账：TotalOrbit 不新增记号阶段字段；反馈插入原界、输出部分和均由可调用性与合法性要求决定，值可能改变。旧高源的 Q/地板/世界仍保留，但不再用整套旧 Goodᴺ 生产合法性。末端补齐字面第一位置，弱 Ordᴵ View 不冒充成品。单字段编码只覆盖同层骨架，低坐标仍旧 Q。原封存数学不改；新高值仍须独立验收。


## 检查与专题入口

导航完整性检查：运行 `Survey/scripts/mapcheck.py`。它检查名字和本地链接，不认证数学结论、编译状态或路线选择正确。定义切片与导入闭包另用 `Survey/scripts/depslice.py`、`Survey/scripts/importclosure.py`，不能相互替代。

查文献先看 [记号手册](Survey/OrdinalNotationsGuide.md)，查外部代码先看 [代码手册](Survey/CodeGuide.md)，避免重复调研。11 月 1 日之前的背景从 [归档总说明](../archive/README.md) 查阅；归档只作历史材料，其强度和不可能性判断不能自动升格为今天的定理。
