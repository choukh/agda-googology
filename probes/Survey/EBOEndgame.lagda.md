# 从完整 EBO 终点倒推：接线、候选与投入条件

2026-11-07。接续[研究历程](ResearchHistory.md)和[骨架总审](SkeletonAudit.md)。
本文维护当前端到端方案的证据与未知，不把方案当作定理。作者要求的不是
再增加一站，而是先说明这一步如何进入完整 ψ₀Λ 闭项及其值证明。

```agda
{-# OPTIONS --safe --without-K #-}
module Survey.EBOEndgame where

-- 本汇总含第 4 层验收，不能进入成品的导入闭包。
import OCF.Align.TerminalFoldAccept
import OCF.Lean.CircuitBoundaryGd
import OCF.Lean.CircuitKernelStableIf
import OCF.Lean.CircuitKernelStableBuild
import OCF.Lean.CircuitKernelStableBoundary
import OCF.Lean.CircuitGenerated
import OCF.Lean.OutputDriven
import OCF.Lean.TLambdaAudit
import OCF.Lean.TLambdaAuditRank
import OCF.Lean.GridValueBase
import OCF.Align.GridBaseFirst
import OCF.Align.GridValueIndex
import OCF.Align.GridBaseKeep
import OCF.Align.GridBaseTowerCore
import OCF.Align.GridBaseTowerAccept
import OCF.Align.GridCheckCountableSan
import OCF.Align.GridCheckCountableSanExt
import OCF.Align.DirectedViewIf
import OCF.Align.DirectedViewBuild
import OCF.Align.DirectedViewBuildClosed
import OCF.Align.DirectedViewDirectIf
import OCF.Align.DirectedViewDirectBuild
import OCF.Align.DirectedViewDirectClosed
import OCF.Lean.DirectedPrefixIf
import OCF.Lean.DirectedPrefixBuild
import OCF.Align.DirectedPrefixActual
import OCF.Lean.DirectedPrefixNegReverse
import OCF.Lean.DirectedPrefixNegMono
import OCF.Align.TotalValue
import OCF.Align.TotalOrbitClosed
import OCF.Align.TotalOrbitNativeAccept
import OCF.Align.RadicalValueNativeAccept
import OCF.Align.RadicalValueAccept
import OCF.Align.RadicalNegJoin
import OCF.Align.RadicalNegTotal
import OCF.Align.RadicalBuildKernel
import OCF.Align.RadicalBuildSyntax
```

## 1. 起点、终点与本轮没有得到的东西

起点保留[接手前的实际闭项](../README.md#接手前实际起点按提交核准)：
BTBO 已验收到 ψ₀(Ω_Ω)，SumOne 已严格超过它；HtOut、HtTowerF/N、
FamFold/EvFold、RecB/Third 等也已有闭项、合法性和 FGH。不能把它们缺少
值界误写成尚未构造。旧高路线封存的原因是定义组织与翻译成本，
不是旧定理失效；本轮没有重开它们。

终点有三个独立验收：合法、可计算且记号无引用的树侧闭项；序数值不低于
完整 EBO 参照；前三层的完整依赖成本小于 1513，含内部 View 和必要证书。
当前没有同时满足这三项的候选，也没有因新增结构定理而得到新的 ψ₀(Ω_x)
强度下界。后继已交输出驱动的完整合法闭项（§8），但尚未验收 EBO。

## 2. 终点覆盖已经落到实际参照

[TerminalFoldAccept](../OCF/Align/TerminalFoldAccept.lagda.md) 是第 4 层，
导入记号，只作验收。它把原 EboLean3Tree 的完整参照保零、后继、ℕ-极限
转入现用可数树 Cd，并证明转换保持 FGH，核实接的是同一参照。

它的 `all-branches` 说：对候选最终树 T，若每一个参照分支 Rₖ 都有
Rₖ ≤ᵛ T，则整个 EBO 参照 ≤ᵛ T。`sampled` 允许错位取站：
对每个 k 给某一实际阶段 n，使 Rₖ ≤ᵛ Sₙ，并证明全部 Sₙ ≤ᵛ T。
两者都有原参照自身的实例，但尚未由任何树侧候选实填。

这只是把目标接实，并未解决覆盖。它也不是宣称所有成功证明必须逐站
取样：直接证明完整参照下界仍然可行。单个高闭项、固定事件数、容器
扩大或任意有限次成功反馈，都不实填这里的全 k 量词。

## 3. 必须接在同一个程序中的链

以下是待验证的设计分解，不是已证充分性定理，也不声称穷尽所有架构：

1. 用树侧的结构参数产生种类、坐标类型和源树，已有对象真实使用新增种类。
2. 原折叠的实际输出被读成该种类自己的坐标，不能用预给地板替代。
3. 此坐标进入一个实际扩张世界；源、状态和以后新准入的分支仍有运行证书。
4. 在新世界继续运行，迁回及后续下降后，最终可数树保有需要的值下界。
5. 同一结构定理覆盖后继、可数对角以及输出决定的新结构，而非为每站另配脚手架。
6. 对全部 EBO 参照分支给覆盖，再作完整成本与 View 审计。

高层树同值不能免费穿过折叠：旧 Value 的 `ψ⁰-not-cong` 已给反例。
所以第 4 步不能省成“各中间层看起来同值”。可以直接比较完成全部剩余
下降后的 Cd 观察；不要求中间站精确还原为某个 Ω 算术式。

## 4. 两个候选的实际接线与首个断点

| 候选 | 已有完整程序中的事实 | 首个未填项 | 不能替代它的局部结果 |
|---|---|---|---|
| A：统一种类的数据／事件核 | GenFoldRun 的 κΔ₁、κc₁ 已用真实 Run 输出 Δ₁，经 rd₁ 更新世界、搬状态并再次 Run；EvFold 也已有输出进历史后继续运行。 | 实际 Δ₁ 属于 DataG；新 RenderingReader 消费 HtTowerFTree.D/Wd₂。缺同一载体的完整读回及回路保持。 | ReadLayerLimit 的后继／极限包闭包、UniformGenerated 的 Int 关系、rkT 分派，尚未互相实填。 |
| B：直接高度与逐底下降 | ThirdTm 已有全 n 的 desc、TN、yΛ、TΛ；后继 OutputDriven 已由逐槽完整运行输出产生整底世界，重建 QL/PH 并交完整下降与对角闭项。 | 新闭项的整源回灌值、Er 洗法和单代表坐标读取是否保留足够 Ω 塔，尚需估值；没有 EBO 下界。 | 新闭项合法、世界增长及每格包含本身都不是终点强度。旧给定世界的再运行桥也不能替代此实填。 |

A 还有两个独立损失：GenFoldRd 的旧种类 nc 取当前世界一枝，GenFoldK
的阶段输出仍经 evB 落回固定 Ht。源码因子化是事实；由此猜测的具体
序数上界仍是判断，不能用类型封顶替代值定理。

B 的损失先于新合法化：ThirdFold.pickG 先经 san，ThirdSan 对穿过 Ω
高度的种类删除，并在 Ω 高度的 tpS 取底分量；固定组件世界又限制准入。
这三件事分别处理，不能说修好合法性就一起修好了。

两候选都未被否定；本轮也没有证据证明二者穷尽可能方案。下一轮选路前
仍须挑战这一候选划分。现有代码是实例和反例数据，不是必须保留的架构。

## 5. 先检验未来世界，而不是默认能搬旧证书

[CircuitBoundaryGd](../OCF/Lean/CircuitBoundaryGd.lagda.md) 检验同一个
原 Third 接口。它否定如下免费搬运：合法 w ≤ w′ 时，任意旧 Gd m h
都能原样变成新世界的 Gd m h。

反例的世界、增长、源高度和字面公共界均有合法实例。新世界让一个坐标
可入，于是旧 Gd 尚未约束的分支被激活，暴露另一个不可入分量。
**反例输入没有证明 LgB**，所以它不否定实际合法生成域，不证明原闭项
值下降，也不否定候选 B。它只说明 Pos 的正向增长不足以完成整证书迁移。

给所有分支再加未来稳定条件也不能直接当作答案：这会加强坐标输入所需
证书，而原 topT 的后继分支只收到旧 Gd。此候选加强合同的正反检验另见
[CircuitKernelStableIf](../OCF/Lean/CircuitKernelStableIf.lagda.md)。
该合同只是研究实验，不反过来成为纲领或今后的接口约束。

它的 [Build](../OCF/Lean/CircuitKernelStableBuild.lagda.md) 已证当前证书
投影、未来再基址、加法与 up 闭包，且全部原底 Sb n 的高度 1 非零地板
确能实填。但 [Boundary.no-floor](../OCF/Lean/CircuitKernelStableBoundary.lagda.md)
也已证：一个明确合法高度上的原 topT，对任意底种子均不满足这份 Stable。
证明使用原地板实际接收的旧 AdT 输入，未给该输入伪造 LgB。
因此“沿用旧 Gd 直接搬运”和“给整棵原地板强加此 Stable”这两种精确
接线均已有否定；它们不是候选 B 的全部实现，不能据此关闭 B。
本轮停止扩建此强合同，不继续把它当成通往 EBO 必须攻下的一站。

### 5.1 后继检验：真实输出域与任意合法输入不同

[CircuitGenerated](../OCF/Lean/CircuitGenerated.lagda.md) 检查了上轮反例
未覆盖的合法源域：即使补上源树 LgB，在原 Sb 1 上仍有编译反例否定
通用搬运。其触发坐标有新 Gd，却已证不合法；源树 LgB 不会消除原 AdT
对这种坐标的量化。这仍不是原 Φ 生成输出的反例。

正面结果改为观察原程序的**输出**，没有要求输入或地板满足强证书：
原 Φ 和 ΦX 的全部输出都有 Full，即每个 Ω 根有原位置，且全部裸分支
递归有同一性质。keep 对全部坐标提供旧输入证据；same 的种子只喂入 k，
链输出从 k b 开始；above 用原低高度递归。因此此结论对任意原 San、
源高度、允许目标及种子成立。

Full 足以在任意显式给定的合法未来底世界取得新 Gd。另一方面，已证
原富合法化保持当前 Gd；把这一定理用在**新世界**，就能给实际输出的
正规化结果新证书，并真实再次调用新世界的原 Φ。再次输出仍 Full，
无需被否定的 LegalTransport。原合法反例输入与这条输出接线也有同实例校准。

这没有重开“全部原地板满足 Stable”的失败合同：要求的域、程序位置
不同。它补齐一项实际生成域的证书义务；未来世界必须真正给出，不能把
局部 Wd(step(Tw U t)) 充当 Wd U。原 San/取枝损失、QL/PH 及最终值覆盖
没有因此解决。零目标的 stp-full 可对任意树结构自证，只作原入口校准，
不算 desc 新强度。主审精确冷编本轮9新件及前批3件，单6G退出0。

## 6. 下一次构造的投入条件（判断，非新增纲领）

本轮不再顺着 UniformCore 追加另一站。先做能判别整链的实验：

- A 必须选定一个数据核，让实际高源、非零前缀、实际输出读回、更新后
  再运行及迁回都发生在同一实例；证明覆盖全部反馈长度的生成闭包。
- B 必须同时交目标裸坐标的全定义处理，以及有证合法坐标的原源重入；
  keep、same、above 的整链和剩余逐底下降使用同一个生成不变量。
- 实验的值结论落在最终 Cd 观察上，并说明如何作为全 k 覆盖归纳的一步；
  单个首格、Run n1 或局部 Cover 不算实填。至少要用具体值下界检验
  原高信息是否区别于取底支／常值替代，不把构造子不同当值不同。

这些是选择下一步时的诊断要求，不是终点可达的证明，也不是必要性定理。
若实验只得到更大的类型或更强且无法实填的记录，记录未解处后重新评估，
不把这份记录当作必须长期攻下的唯一缺口。没有覆盖与成本证据前，不宣布
已有 EBO 路线，更不能承诺只需继续重复现有步骤。

## 7. 翻译与成本账

本轮没有新增树／折叠构造子。终点模块读记号，严格留在第 4 层；Gd
世界实验读取原树的准入结构，未读取记号。它们增加的是验收和诊断信息，
不是树自足已经实现的证据。原前三层定义没有因验收方便而更改。

UniformCore 已由主审冷编 12 件、核对源码与编译器的本地导入集合；
其干净闭包只保证未引用记号，不保证设计不受记号启发。旧 EvFold 双事件
闭项切片约 1423，尚不含新增高层 View；不能据此给全种类成品承诺预算。
未来核若采用新证书或环境，须重算完整依赖，不能只数新叶文件。

## 8. 作者指定的双路后继：旧闭项估值与新闭项构造

作者要求先审旧估计，同时继续“输出驱动世界 → 完整下降 → 统一迭代
闭项”；值证明不作为交出新闭项的前置条件。两路均只新增文件。

### 旧 TΛ：原估计尚缺整体值模拟

[TLambdaAudit](../OCF/Lean/TLambdaAudit.lagda.md) 核对了原 TN 的世界参数
c₀ 与 RecB 的附加塔高 m 不同，不能按同名函数或浅节点数配对。原每底
指标节点的完整反馈链已逐字给出：种子是 fl n，输出经 legS 后回灌整份
HB(Sb n)，不是把所有底的指标都当 Cd。旧固定世界秩没有描述这条链。

[TLambdaAuditRank](../OCF/Lean/TLambdaAuditRank.lagda.md) 已证所有原
gtX／地板的秩投影值为零，并以原第一站的实际非零输出排除“直接以此
秩值封顶下降”的合同。它不否定用秩加额外闭包运算的估计，更不证明
旧 ψ₀(Ω_{Ω·ω}) 读法错误。当前精度提高在于明确缺失的两参数整体模拟，
尚不能诚实给出已核准的具名上下界；原 TΛ 是否已保留更高 Ω 塔仍开放。

### 新闭项：世界更新与全部下降已经实填

[OutputDriven](../OCF/Lean/OutputDriven.lagda.md) 不再向旧运行器外给未来
世界。对每个 raw m，把 V=Tw(Sb n)m 当作底，在 V 内合法界 1 下折
完整 XSof V 地板，得到同类型真实输出；m 仅选择类型，不要求其合法。
所有槽一起更新，实际界读取后再次运行。全部底按结构递归产生合法世界，
各站重新建立 own/liftE/QL，完整下降到 Cd，再把最终输出反馈到下一外阶段。

已交 closed、legal-closed、fgh，以及独立枚举所有有限深度／轮数配置的
closedGrid、legal-closedGrid、fghGrid。每格在其实际阶段种子下的完整输出
包含于最终树，不要求深度、轮数或种子的值单调。调度公平本身仍不是 EBO
验收，也未建立新闭项与旧 TΛ 的值比较。

该实现重新证明通用全源路径，因而没有被上轮任意原输入的迁世界反例卡住。
它不需要强行把旧 raw 源或原地板放进 Full/Stable；这些旧结果被当作信息，
没有成为必须保留的接口约束。

### 仍须独立验收的内容

新世界不再把全部组件界冻结为零，但原 Er 洗坐标与旧跨底代表坐标取枝
还在。代表改读当前实际界，尚不能推出整条高信息被保留。因此当前可肉眼
审查一条完整的新运行链，却不能宣布其值为 EBO。

当前闭项及合法 FGH 的语法切片为同步对角 1148／全方格 1160；未含新增
内部 View 的验收，不能据此宣称满足完整 1513 预算。主审逐读并单6G冷编
12新数学模块与汇总，13件全部重新 Checking、退出0；两路定义／证明闭包
均无记号。完整复核与脚本局限记于 LOG。

## 9. 暂停扩建后的实际值审查

作者选定先分析现有闭项，不再追加候选。主对象是全方格 closedGrid，
旧 TΛ 作对照。此处的校准不覆盖接手前已有的 BTBO 以上前沿。

[GridValueBase](../OCF/Lean/GridValueBase.lagda.md) 和
[GridBaseFirst](../OCF/Align/GridBaseFirst.lagda.md) 证明：完整零底下降
first 与外种子、更新轮数无关，并逐字展开原整源反馈链。它没有截断
gtX，也没有把整源换成单个地板。

[GridValueIndex](../OCF/Align/GridValueIndex.lagda.md) 进一步给全部实际
状态的等式：第零底零高度槽的输出恒为 first，指标更新反复执行
`c ↦ hs (c ⊞ Rich.legS 0 first)`。所以该指标的多轮累加不能直接读作
反复作用 `c ↦ ψ₀(Ω_c)`；可能的新增强度须追踪非零槽及最终下降。
这不声称整个世界或全部方格同值。

### 已接上的标尺与没有接上的标尺

[GridBaseTowerCore](../OCF/Align/GridBaseTowerCore.lagda.md) 在实际
first 的第一个回调内找出完整的纯幂塔轨道。比较对全部纯源路径证书和
全部合法 GT 种子量化，不假定证明无关，也不调用 ΦX 的一般值单调性。
[GridBaseTowerAccept](../OCF/Align/GridBaseTowerAccept.lagda.md) 接已有
ε₀ 验收，证明 `epsilon ≤ᵛ first ≤ᵛ closedGrid`。这是同一未知闭项的
下界校准，不是新前沿，也不给任何上界；尚未证明它达到 BTBO 或 EBO。

BTBO 的直接逐项模拟尚未完成：源 ψ 的零输入在目标层给 Ω，原 Φ／ΦX
却一律给 1；原链还有累计前缀和每次回灌的 Rich 完成。要比较的是整条
带前缀的生成链，不能在零项不同处假设逐项对应，更不能因模拟未成就
下调原闭项的实际高度。旧 TΛ 与新 closedGrid 的值比较仍未完成。

### 先分清哪一种损失实际会出现

[GridCheckCountableSan](../OCF/Align/GridCheckCountableSan.lagda.md)
覆盖底 S⊥ 的全部可数高度和全部裸输入：原 sf 总成功，原 san 前后
互相 ≤ᵛ。因此 first 不会经过高底“穿 Ω 高度删根”的分支，不能拿
高底的这项损失作为压低 first 的依据。该定理没有把高层同值穿过折叠。

[GridCheckCountableSanExt](../OCF/Align/GridCheckCountableSanExt.lagda.md)
另给**条件**诊断：以函数外延为显式前提，全部上述 san 均等于恒等函数，
任意分支函数可消费此等式。前提在外延函数等式解释中成立，这里没有
无条件的 Agda 实例。它严格留在验收层，不进定义或证书。
所以 keep 重建坐标造成的无条件相容证明缺口，不能被写成数学上的
实际缩水；专门对生成分支作结构归纳只是可研究的一种无外延证明路径，
不是已经证明必须添加的新证书。

[GridBaseKeep](../OCF/Align/GridBaseKeep.lagda.md) 则在任意合法底上
证明原 component 0 的保留片段值不缩，允许输入含任意底 Ω。它说明
确有高种类未被洗掉；仍缺该片段在完整高源输出中的捕获，以及随后
全部下降的相应比较。局部保留不等于最终可数值已保留。

当前继续投入的是完整链的 BTBO 标尺比较，再追踪非零槽带来的提升。
这是一项诊断选择，不把 BTBO 或纯幂塔校准当作最后一站；最终验收仍是
§2 的完整 EBO 参照覆盖。原闭项及其前三层定义没有因此更改。

## 10. 作者授权：从已知值闭项定向改写，配套修改值证明

作者要求开始执行“简化已有翻译闭项，并建立定义改动与值证明改动的
对应关系”。本轮保留旧文件，在新模块做两个有关联但分工不同的实验。
旧封存族仅作方法来源；没有重开逐码克隆或向旧族再加一站。

### 完整 EBO 实例：融合中间证书树，沿共尾视图运行

[DirectedViewIf](../OCF/Align/DirectedViewIf.lagda.md) 固定实际算法 cached：
原来先由良基证据生成 HC 中间树，再由 tree 生成布劳威尔树；现在沿同一
良基证据直接产生树。内部 ω 分支的递归状态从 fsn t n 改为
fω(vω t e)n，规则 6 沿同一 VΩ 的 fΩ/γ 运行。它使用已有 View 算法，
不是新发明基本列，也不只是给原闭项外面加包装。

这里的 View 仍是记号的共尾视图，不是纲领所要求的最终内部布劳威尔
View 验收。vω 表达式仍在 λn 内，不能说全部 n 只构造一次视图，
没有做性能基准或宣布提速。

[DirectedViewBuild](../OCF/Align/DirectedViewBuild.lagda.md) 实填冻结合同，
对任意可数标准形、任意良基证据、任意旧 HC 证书给出逐构造子 Same。
定义修改到下一记号项时，值证明通过 fω-eq 搬运子证书；整条证明不要求
NF／HC／Acc 的两份证明相等，也不需要 Funext。

[DirectedViewBuildClosed](../OCF/Align/DirectedViewBuildClosed.lagda.md)
的实际闭项直接调用 wf→cached，原 hc-tower 只在比较定理中出现。
full-EBO 给整个新闭项与 §2 原完整 EBO 参照的双向值比较，覆盖全部
Ω 塔；fgh-reference 另给逐点 FGH 相等。这是已有 EBO 的保值内部改写，
不是新强度，也尚未摆脱记号。保逐项结构是本次能得到的结论，不成为
后继定向简化必须逐项相同的规定。

第二步 [DirectedViewDirectIf](../OCF/Align/DirectedViewDirectIf.lagda.md)
直接消费既有 NFω／Ctbl-fω／Tω，去掉第一版证书 View→fsn→View 的
往返；运行定义中不再使用 fω-eq。
[DirectBuild](../OCF/Align/DirectedViewDirectBuild.lagda.md) 仅在验收里
用对应等式搬运旧 HC 子证书，保持任意旧证书的比较。
[DirectClosed](../OCF/Align/DirectedViewDirectClosed.lagda.md) 同样直接
wf→direct，已给整个 EBO 的双向值及 FGH 逐点等式。两版仍保留记号
的项、标准形、比较、共尾视图及良基证明；删掉一层转换不等于树自足。

同口径执行切片已测：原 E.Ord 闭项加 E.FGH 为 1500，第一版融合／缓存
为 1501，第二版直接视图为 1420，净省 80。第二版的运行切片不再到达 HC、
fsn／fsT／γT、fω-eq／fΩ-eq／γ-eq；对应等式仍用于第 4 层验收。
这说明第一版只是换运行组织，直接消费视图证书才真正删掉往返。
切片脚本 [locslice_directed.py](scripts/directed/locslice_directed.py) 与旧法
一样统计到达块、补良基证明的模块别名，库依赖不计。两侧只取实际程序
及 E.FGH，不是 1513 的全层全根重算，不把 1420 当成成品预算认证。
切片为语法近似；新模块导入闭包仍含 EBO，不能以函数不可达冒充记号无引用。

### 前缀改写：真实单向规则与它不能被加强的部分

[DirectedPrefixIf](../OCF/Lean/DirectedPrefixIf.lagda.md) 同时固定两种
程序：point η 的零叶是显式地板 η、ℕ 极限逐项；unary 的零叶固定为 1、
ℕ 极限取部分和，两者都保留原底 Ω 种类。
[DirectedPrefixBuild](../OCF/Lean/DirectedPrefixBuild.lagda.md) 证明：

> 若 η ≤ᵛ unary A，则对所有底种类和全部裸输入 a，
> point η a ≤ᵛ unary(A ⊞ a)。

前提并非空合同：任意 A 都有 A ≤ᵛ unary A。可数域进一步证明旧 point η
的整个反馈轨道被新 unary(A⊞_) 轨道支配；归纳用旧 point 的值单调性，
不假定新 unary 单调。
[DirectedPrefixActual](../OCF/Align/DirectedPrefixActual.lagda.md) 将 unary
与原 component 0 的真实完整输出逐形对应，前缀下界已接入原运行，
保留原世界、公共界、路径和 GT 种子。这仍是保留片段；完整 gtX 的前缀、
same／above 及全部后续下降尚未由此覆盖。

两个否定校准约束的是精确合同：
[NegReverse](../OCF/Lean/DirectedPrefixNegReverse.lagda.md) 用合法常零
极限证明基值相等与合法性仍不给反向值界；
[NegMono](../OCF/Lean/DirectedPrefixNegMono.lagda.md) 证明 unary 不尊重
裸可数树的值单调性／同值。所有反例前提已实填。这不否定受控生成族
的吸收或整个定向简化路线。

### 本轮所得的方法与下一步

| 定义改动 | 配套的证明改动 | 已验收范围 |
|---|---|---|
| 融合 HC 生成与 tree；用共尾视图执行内部反馈 | 显式搬运下一状态的证书，对任意旧证书证明 Same | 完整 EBO，全标准形可数域，无 FE |
| 改为直接使用视图上的封闭性证书，删掉往返 | 对应等式只在验收中搬旧 HC；不改运行器来迁就证明 | 完整 EBO；同口径执行切片净省 80 |
| 显式地板改为固定 1，将地板信息移入源前缀 | 先验 prefix 的输出覆盖地板；逐结构给单向下界 | 全底、全裸分支；原 component 0 实例 |
| 把该替换放入可数反馈 | 用旧算子的单调性接单向模拟，而非新算子单调性 | 全部有限迭代及整条 ℕ 极限 |
| 希望把单向下界升级为等值 | 还须特定生成族的有限和吸收／错位覆盖 | 泛化反向律已有反例，特定生成族仍开放 |

下一次实质简化要在上述完整参照旁选定一个反馈状态，接上真正的前缀
供给，并在同一实例检查后续下降；不能把本轮保留片段直接冒充全 EBO。
缓存实验仍以记号分派，定向下界只从树结构推出，两者分别记账。
成品的记号无引用、内部 View 与完整 1513 成本要求继续有效。

## 11. 转到真正树侧闭项的保值改写

作者追问并澄清后，上一节的工作明确归为“记号侧标杆的编译简化”，
不能冒充旧树侧翻译闭项的简化。作者接受并要求开始的本节对象固定为
原 EmbVV 已验收的树侧完整 ω² 码端行：ψ₀(Ω_{Ω·ω²})。
原闭项的树／折叠／证书不引用记号，其结构仍受记号规则引导。
原文件保持只读，新入口 [TreeEmit](../OCF/Align/TreeEmit.lagda.md)。

### 具体改动与实际反馈范围

[TreeEmitBuild](../OCF/Align/TreeEmitBuild.lagda.md) 的 emit 逐原 Q 构造，
直接生成 Z，融合底目标上的 Run→Ordˢ zero→toZ。它不把已求出的 V
当新输出，也不只改最外层 lim。qi 内的非零目标仍调用原 Run；Ω 两类
仍使用原 chainᵠ、ψᵠ／Ψ、cap 与更新世界，末端输出递归 emit。
因此当前改掉的是底输出层；高层解释器及世界证书生产仍保留。

[OrbitRewriteIf](../OCF/Free/OrbitRewriteIf.lagda.md) 固定 Pointwise：
闭包界 c 相同，程序分支只在同一字面 η/e 处相应。
[OrbitRewriteBuild](../OCF/Free/OrbitRewriteBuild.lagda.md) 的 move
保留原证书的全部 ys/hy/dy，递归构造指定新证书 H，同时给出
forceᴺ old G ≅ forceᴺ new H。它没有声称任意新 H 都产生同一输出，
也不要求任意函数在两个同值层号上相容。此规则与阶段无关。

### 新闭项与原高值的接线

[Closed](../OCF/Align/TreeEmitBuildClosed.lagda.md) 的 Rows 对全部 HtB、
全部高度 m／行 α 给出 raw、good、tree、legal、old-new。实际 closed
逐字取 Rows(HB ω²ᶜ).tree end zero，保留完整旧高实例；不是低首分量。
raw 来自 emit(Ω̇ m α)，good 由原 GᴺTᵠ 经 move 得到，tree 才 force
这份指定新证书。原运行器的结果不是被塞入新 raw 的叶子。

[Accept](../OCF/Align/TreeEmitBuildAccept.lagda.md) 先对全部行给新旧同形，
再以泛型 transport-value 接原 vv-ω²：closed-value 是新闭项在
ψ₀(Ω_{Ω·ω²}) 的双向值验收。FGH 逐点同值另证，不以它代替值界。
定义、证书不导入验收。此次作者明确选择旧树侧实例作有限改写对照，
旧验收仅在本验收文件串接，不恢复逐码克隆或旧架构的继续攀爬。

### 不能省略的生成域条件

尝试把 IsF r η 一律替换成本层 V n η 时，现成 D-val 只到 η=0。
不能据此推出非零反馈也能删除下降。
[NegRaw](../OCF/Align/TreeEmitNegRaw.lagda.md) 与
[NegValue](../OCF/Align/TreeEmitNegValue.lagda.md) 在同一实际有限高度段、
同一界2世界给出完整 Ok/Eh/Ev 和两端 Goodᴺ：omk 的低字段取 q0，
主体取 qs q0，直接解释与先下降再解释读不同字段。前者值包含2，
后者为1，故泛裸数据删除律确实不保值。

反例的两字段没有原 Ω̇ 的生成关联；它没有否定实际生成域。
现行 emit 因而保留原高层回调，不偷偷用尚未证明的非零 D-val。
若进一步改变高层搬运，要在实际反馈域给出两个字段的相容证据，
不能先把任意裸 Q 的律当作已经成立。

### 翻译与成本边界

本轮确在真正的旧树侧高闭项上交出定义与值的配对改写，仍未得到 EBO。
树、折叠、证书导入闭包记号零引用不等于树自足；旧 Q 形状及高层运行
仍受记号引导。尤其 good 仍继承原 GᴺTᵠ，不能把融合输出层说成已删掉
全部环境脚手架。是否压缩完整依赖，须以实际切片检查后单独报告。

成对执行依赖切片已报告：旧侧 V/GV＋合法性与FGH，补实际HB ω²参数，
为7351；新侧closed/closed-legal/fgh为7483，增加132。两侧同计本地
依赖、不计库依赖，补可达模块别名到不动点；opaque仅在切块视图按
等长mutual识别，未修改源程序。脚本
[locslice_treeemit.py](scripts/treeemit/locslice_treeemit.py) 输出显示：
两侧都仍到达原GᴺTᵠ、Goodᴺ、ψ̄ᵠ；新侧再到达sound和move。
这是本例的语法近似成本比较，未含完整内部View认证，不能与上一节
的记号侧标杆执行切片或1513完整标杆直接比较。

因此本例验证了保值改写与实际轨道运输，尚未得到更小的完整树侧定义。
下一步优先研究新程序自身的结构证书生产，减少对旧全上下文合法性
证明的依赖；只继续融合末端输出，没有解决此例已经定位的成本来源。
这是诊断与投入判断，不是否定定向简化或实际生成域路线。

## 12. 允许改值的大幅简化：删除旧证书生产

作者明确“可以不是保值的压缩，只要能证明值就行，请大刀阔斧尝试
简化”。本轮不再要求原轨道不变；旧高闭项及 ψ₀(Ω_{Ω·ω²}) 定理
继续有效，新定义不能继承其标签。

### 主候选：构造合法性，删除整套旧证书生产

[TotalOrbitRun](../OCF/Free/TotalOrbitRun.lagda.md) 对全部 Z 直接运行，
没有 Goodᴺ 参数。ℕ 极限改取部分和；闭包反馈为 ζ₀=c+run(t)，
ζₖ₊₁=c+run(g ζₖ boundₖ)，加法保证原界 c⊑ᴵζₖ；真实观察输出再
取部分和。递归只经原 Z 子树与函数分支，不要求全域三歧。
[TotalOrbitClosed](../OCF/Align/TotalOrbitClosed.lagda.md) 固定完整原
HB ω²ᶜ 的 end/zero 源，以原 ψ̄/toZ 生成输入，改用新语义运行。
没有调用原 V、forceᴺ、GᴺTᵠ 或运输旧 Goodᴺ 生产证书。Q、地板、环境
及非零原折叠仍生成输入；并未全删这些旧结构。
[Source](../OCF/Align/TotalOrbitSource.lagda.md) 与 Run 单独隔离生产
代码，属于本轮原样代码搬移，没有再次改变算法。

直接保留 Ordᴵ 输出的 [表示实验](../OCF/Align/TotalOrbitNativeAccept.lagda.md)
已证 FGH 逐点一致。但 Ordᴵ 的 ⊑ᴵ 是模同形前驱包含，不是字面第一
位置，弱 View 不能算纲领最终验收。
[RadicalValueNativeFinal](../OCF/Align/RadicalValueNativeFinal.lagda.md)
补齐该条件：整个新输出忘到 Cd，经 leg 完成，对象为 Σ Cd LgB。
内部 View 的子对象仍属 Object，极限保留实际相邻 ⊲ 证据，FGH 三条
方程均编译通过。[单向验收](../OCF/Align/RadicalValueNativeAccept.lagda.md)
证明未完成的 TotalOrbitClosed.closed 不高于最终完成树。末端 leg
还可能改值；此定理比较两种新输出，不是旧 EmbVV 高值下界。

### 改值之后，不能免费继承哪些证明

[比较合同](../OCF/Align/TotalOrbitCompareIf.lagda.md) 固定新算法。
[RadicalNegTotal](../OCF/Align/RadicalNegTotal.lagda.md) 正式否定全裸 Z
的保值与旧值下界：常一极限旧值1、新值包含2；另一闭包的旧坐标恒1、
观察值1，新坐标恒2、全部观察值0。全部旧 Goodᴺ 实填。这只否全 raw
合同，没有证明反例属于 Ω̇ 生成域，也没有否定本候选。
[RadicalNegJoin](../OCF/Align/RadicalNegJoin.lagda.md) 另证指定二元
join 不保合法输入的左右前驱包含；未否定值 max、输出合法性或其他
完成算法。

旧 IsF/ClosRow.next 只约束旧 forceᴺ；V-≼ 还需 ⊑ᴵ 且仍是旧语义；
Hd-lvl 仅覆盖同形／去头；Pointwise 仅覆盖同一字面 η/e。它们不能
直接接新轨道。下一具体义务是在原 Ωd/rowC 的实际更新世界中，证明
旧轨道到新轨道的有向嵌入及输出覆盖，允许错位，不索要全 raw 单调。

### 其他大幅删减的实得与边界

单字段线已交 [生成域证明](../OCF/Align/RadicalBuildGenerated.lagda.md)、
[全部原 Ω 行编码](../OCF/Align/RadicalBuildSyntax.lagda.md) 及
[执行核](../OCF/Align/RadicalBuildKernel.lagda.md)：同层 omk 删 body；
ι/ι↓ 对任意输入输出平衡，全部 Ω̇ m α 准入；任意上下文、全部后继
回调与极限分支有精确标记读法。但是低坐标仍旧 Q，qĉ 已有 Z 不在
平衡条件内；移位仍可能重建 ι。尚无整 Program 执行器、自生产证书
或高闭项替换，不能报告净压缩。

[RadicalValueOrbit](../OCF/Lean/RadicalValueOrbit.lagda.md) 完全丢掉
Q/Flr/Env/cap，只对作者原 J(a)=ψ₀(Ω(ordᴰ a)) 作闭包、反馈与对角。
[验收](../OCF/Align/RadicalValueAccept.lagda.md) 已证整个合法闭项
不低于 ψ₀(Ω_Ω)。它是短定义校准，未继承旧高值，不算超过接手前沿；
更高函数闭包层是否增值尚无定理，不由名称推断 EBO。

### 与终点的联系

本轮缩减生产架构，没有新增已核准高强度。优先证明主候选在原高源上
的实际值界，不继续盲叠闭项。若得到与阶段无关的模拟，再检验同一
方法能否承载高种类完整回灌与全 Ω 塔覆盖，最终接完整 EBO 参照下界。
这些连接尚未证明；总解释器本身不提供 EBO。这是待检验路径，不是
穷尽或可达性定理。

### 成本与最后一次依赖清理

先得到旧7351／新Ordᶜ0版本1542的执行切片。直接Ordᴵ表示纯运行
1323，但只有弱View，不作成品数字。第一位置版本起初1926；切片
发现只是导入CRw.leg，就把整塔折叠及路径模块的实例也带入生产。
于是 [LiteralCompletion](../OCF/Free/LiteralCompletion.lagda.md) 只按
原相同方程提供部分和、leg、第一位置合法性与FGH；原CRw只读。
其单向值下界在独立验收中重新归纳，不借接口相等或函数外延。

最终执行定义切片旧7351行／39模块，新1418行／16模块，减少5933。
两侧均取实际高源闭项、合法性和FGH，新侧另外计入内部第一位置View；
库依赖不计。新侧不达Goodᴺ/GᴺTᵠ，仍达原ψ̄生成源。脚本
[locslice_totalfinal.py](scripts/treeemit/locslice_totalfinal.py) 沿用前轮
同一切块器、旧根与别名补根规则，显式补实际run根。数值是定义级语法
近似，不能单凭1418宣称1513完整成品验收通过，更不能推出新高值。
其余版本与逐轮复核见LOG。


## 13. 冻结新闭项的值证明

本轮只验证第4层，不再修改成品定义。对象仍是
[RadicalValueNativeFinal.closed](../OCF/Align/RadicalValueNativeFinal.lagda.md)
的原 HBω² 完整端行，不是把输入换回基底。证明入口是
[TotalValue](../OCF/Align/TotalValue.lagda.md)。

已编译的终项结论已加强为 ψ₀(Ω_Ω)+ω ≤ |closed|：同一真实闭包站
的全部后续输出均正，故第n个部分和至少为种子加n，再取极限。严格性也有明确的
反向界否定：不成立 |closed| ≤ ψ₀(Ω_Ω)，所用值严格序的反自返
对全部Ordᶜ成立，不需另加合法性。证明先取得实际基底闭包的BTBO
下界，再使用原高源内的真实闭包站严格增长，沿两层原链进入端行，
最后使用原末端完成的单向值界。没有把该结论写成
ψ₀(Ω_{Ω+1})，也没有继承旧 ψ₀(Ω_{Ω·ω²}) 标签。

内部基底的结论更精确：全部HtB、所有合法世界和实际环境下，
原完整rowB的新解释值与BTBO互相≼。上界逐个控制真实轨道的
反馈和输出部分和，下界通过有界前驱嵌入和下一次折叠的提升
覆盖整条BTBO列。它不是只算前几个输出；也不是最高端行的上界。

非零参数1已完成全部高度的原ψ/Ψ跨层回收；这允许直接比较实际
下降后的反馈，而非假设裸Q保值。任意η仍需遗传生成域与搬运/折叠
保持。已有域覆盖原全部Ω̇输入、原ι及ι↓，但覆盖输入不等于
运行恢复；含函数分支的marker搬运正在用关系证明，不要求函数外延。

通向终点的验证顺序仍为：先把上述跨层回收推广到真实高阶反馈域，
再用带公共上界的嵌入/吸收证明整高行的值界，最后单独控制末端leg。
完整新闭项的准确值、旧高下界及具名上界目前均未完成，因此这批
是压缩后候选的实证校准与通用比较工具，不是达到EBO或超过历史前沿。
最终98件冻结证明及汇总主审单6G冷编退出0；源码与成功编译器图的逐根
本地闭包一致。验收中使用记号只为标定BTBO，不进入成品依赖。


尾层问题现已进一步分离：[HighGenerated](../OCF/Align/TotalValueTailHighGenerated.lagda.md)
对原全部Q的实际底读取证明输出SV，最高端行亦实填。因此
[HighFinal.final-upper](../OCF/Align/TotalValueTailHighFinal.lagda.md)
只需外部参照y的HS、St及原高输出≤y；再得最终树≤ψ⁰Ω(toLevel y)。
最高原输出的这个具名外部界仍未交付。完整原rowB则各前提全填，
[HighBaseFinal](../OCF/Align/TotalValueTailHighBaseFinal.lagda.md)证明
连末端完成后依旧与BTBO同值。不能把这个局部精确值冒充终项值。


生成域保持现已补齐：RelatedGenPsi与PsiHeight对全部合法环境的
原ψᵠ、Ψ证明生成保持，含keep/same/above的完整反馈；没有外加
未来证书。Marker观察重写也覆盖全部实际参数。仍待证明的是原ι
与跨高度ι↓的受限观察耦合，尤其新关系在真实反馈链中的保持；
旧Rq对任意坐标量化，不能仅改它一个前提就当作这项已经完成。
