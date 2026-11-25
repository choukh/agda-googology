# D7 折叠严格性检验：(b) gt 行在严格合法源上停顿

**交付 (b)。** 平行 LF 上的严格合法源
lc 0 raw1 1 (λ η e → 1)，在零种子1、后继行与 gt 逐点输出规则下，
强制产生 lim constW，其中 W=lim(copies 1) 本身严格合法。
Properˢ W W→⊥，所以输出不满足严格合法性。
该源还满足已有同形 R₂；反例不靠常零 ℕ 源列或零种子。

本轮按主审更正理解历史决定：2026-11-05 只确定目标树自己的第一位置步进，
针对值严格性，不是 Raw 相邻自反必须保留的要求。
旧定义和结论不改，不迁移20件模块，不写完整 ψ 或新的 γ。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFoldReport where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.YiLglFoldIf
import OCF.Align.YiLglFoldPause as P
import OCF.Align.YiLglFoldValue as V

-- 值验收的 paused 确是局部规则观察实例的输出，非另一棵代用树。
observed-output : P.observer P.source ≡ V.paused
observed-output = refl
```

## 三行的结构义务

[YiLglFoldIf](YiLglFoldIf.lagda.md) 只把模板所需的结构引理写成参数接口。
StrictMap go 显式要求合法性保持与 Properˢ 保持；omega-map 给非空实例，
但 Ω̂ 不被冒称为满足 ψ 规则的 go。

| 行 | 编译过的结构定理 | 前提与范围 |
|---|---|---|
| 后继 | copies-step／successor-legal | x 严格合法且语法非零，则 lim(copies x) 严格合法。Ω-nonzero 对任意 Ω 种子给非零证据。 |
| 极限 | limit-legal | 显式 StrictMap go 把严格合法 lim f 送到严格合法 lim(go∘f)。这个前提不是由输入步进自动得到的。 |
| gt | chain-output-legal | 链关系 R 的每步证据、out 把 R 送到 Properˢ、每个 out 合法，三项一起给输出严格合法。chain-instance 是非空实例，不是 ψ／γ 实例。 |
| lt/eq 保留 | keep-legal | StrictMap go 给第一支和全部合法 Ω 坐标的分支输出合法；并通过 CP 保持给第一支界、弱单调性。不能漏查分支内的 ℕ 极限。 |

### 后继行：右递归加法与非零种子

平行 `_+ᴸ_` 与 JiaBase 的加法都递归右参数，
copies x (n+1)=x+copies x n。所需的是 copies x n 到下一项的严格路径，
不是固定左前缀 x 到 x+y 的路径。
copies-step 的 n=0 由 zero-proper 从语法非零 x 给出；
后继步用 add-proper x 映射前一步的严格路径。
add-legal 同时递归给相邻列和所有部分的严格合法性。

若种子取0，非零前提就不能实填，不能用本定理掩盖 lim const0。
本轮 Ω 种子是 Ω̂0=1，Ω-nonzero 显式保证此前提；
后继、极限、保留、gt 四种输出根构造子也都不是语法零。
没有运行“是否为0”的判定来挑一个严格子列。

### 极限行：互归纳中究竟要证明什么

输入的 Properˢ 不等于输出 Properˢ；limit-legal 明读 proper-map。
若要对完整 go 同时归纳，Proper 的三种构造子分别要求：

1. under-suc：把递归 CP 证据接到 successor 的第1支，successor-position 给出真路径；
2. under-lim：接入相应 n 支，limit-position 给出真路径；
3. under-first：保留行用 keep-position；gt 行用 collapse-position 接到输出第0支。
   其中 CP(go a,out start) 必须由源的第一支界和递归 CP 保持给出，不能空添。

cp-map 明确从严格保持导出弱 CP 保持；相等行仍用 self，不要求证明相等唯一。
上述引理只交出这些归纳分支的结构义务，不把它们说成完整 ψ 的归纳已完成。
尤其 gt 列本身合法还需链步与 out 的严格保持，下面说明不能由现有源条件通用推出。

## gt 反例与最小规则合同

[YiLglFoldPause](YiLglFoldPause.lagda.md) 给闭源与证据：

```text
One = suc 0
source = lc 0 raw1 One (ληe → One)
source-legal : Legalˢ source
source-R₂ : R₂ source
W = successor One = lim(copies One)
W-legal : Legalˢ W
```

源的层号合法、第一支与所有分支均为1；第一支界／单调性用弱 CP.self，
证明无关性为 refl。根需要的 Below(1,source) 也由第一支给出，所以 R₂ 真。
源中没有 ℕ 极限，不含违反新严格性的子列；所有相关前提均为闭实例。
有界比较以合法树1为公共界，root-gt 编译为 refl，实际选择 (1 > 0) 的 gt 行。

SourceRules 只取必须成立的三条局部方程：

```text
go 0 = One
go One = successor(go 0)
go source = lim(λn → go(source-body(points n)))
```

points 是已给的合法坐标序列；不假设所有序列都是 γ，
也不为构造链新增 LF→Raw 回收器。真正按 gt 规则产生的链若存在，当然也在该否定范围内。
observer／contract-instance 证明这三条局部方程可同时满足，
但 observer 是合同的观察实例，不是完整 ψ，也没有完整折叠的合法性保持。

前两条方程强制 go One=W；源分支恒 One，所以 out 对所有合法坐标恒 W。
no-rule-preservation 证明任何满足这三条局部方程的 go，其源输出都不能 Legalˢ。
这不是从空的“完整 Fold 存在”前提推出矛盾。

no-proper-W 排除了所有 Properˢ W W：若有该路径，只能进 W 的某个 copies One n；
copies-finite 给每项有限，finite-position 给 CP 的有限向下闭包，
于是会推出 W 有限，与其极限根构造子冲突。
证明不比较两个极限函数，不用 Funext 或 UIP。

### 为什么递归 go 的单调性不足以给 out 单调性

同一个源的 raw1、raw2 都通过守卫，且 raw-strict 已给 Dn(raw1,raw2)，
coordinate-strict 已给读回后的 Properˢ(1,2)。源分支却把两者都送到 One。
即使递归 go 把**源树之间已有的严格路径**保持了，
这两个分支值之间也只有弱 CP.self，根本没有可交给归纳假设的 Properˢ。
no-out-dn-map 编译否定了把这些坐标严格步通用送成严格 out 步的合同。

链的第一件事“γ 是 step γ 的真位置”也不是弱 Ω 分支单调性给出的字段。
本轮没有继续实现 γ 或回收链点；即使免费给任意合法坐标链，常 out 已使输出失败，
所以不必为得到反例而先完成它。

## 分类与能否随构造避开

**编译事实：** no-selected-iter 对任意迭代器、任意选列函数 select 排除严格输出。
首步后开始、任意有限移位、事后挑子列都仍是常 W，不能补出 Properˢ W W。
这里甚至允许任意 select，不只可判定选法。

**诊断：** gt 的逐点规则保留常输出，这是规则的代数事实；
触发它的是平行 Legalˢ／R₂ 仍允许常 Ω 分支的源域。
改变 Raw 相邻合法性并不会排除这个源；它也没有使用旧的退化 Raw 极限。
这是规则与现有合法域组合下的反例，不是所有树表示或所有折叠方案的否定。
没有给 source 的 EBO Rep／Reach 证书，不能声称实际 EBO 轨道已经停顿。
也未对整个 Ω 源赋序数值，不把“退化”扩写成未证明的源值结论。

**这个已知常输出可以不用判定换写法。** [YiLglFoldValue](YiLglFoldValue.lagda.md)
直接返回 W，replacement-legal 给严格合法性；same-value 给 lim constW 与 W
经 Countable 读到既有 A 值前序后的双向≤。observed-output 为 refl，确认它对应本反例的观察输出。
这不是抽严格子列，而是消去已知常输出的外层极限。
该值证据只针对这两棵可数输出，不是全 LF 的值解释或原高层源的值定理。

本轮没有改变 gt 行，也没有给任意分支函数判定常性或自动附上常性证据的程序。
对这个构造已经知道常性的例子，可以随构造返回 W；
对完整 ψ 的所有源何时获得这种证据，仍是未做的接口义务，不能称已完成通用修补。

### 壁垒和停止条件

常输出的局部替代没有判定任意下标或函数，没有挑选子列。
既有有界比较始终带字面合法界1；没有给 Ordᴰ 精确初始段加 Ω 共尾元的有界三歧接口，
因此未实填 Barrier.barrier 的前提。
Properˢ 是结构路径；没有值严格 View／Enc，也未实填 BrwViewNeg.strict→LPO。
没有证明一般识别常函数或一般严格化必然触壁垒，不将它们直接说成 LPO 定理。
未用 UIP／Funext、裸下标律、高层固定类型回收或原始树补码。

## 翻译账与验证

copies、从零开始复制、逐点极限、lt/eq 保留、gt 的 out(iter step start n)
均照 JiaExactFold 的形状检验；其来源是照 EBO 规则写的甲模板。
本轮没有把这些形状称作树侧唯一要求，也没有悄悄改 gt 来使严格性通过。
结构严格性引理只用平行树构造子与位置，否定来自合法域里的常 Ω 分支。
值上的局部替代留在第4层，不进入折叠或证书定义。

新模块 If／Pause／Value／Report 逐件删自己的字面接口，单6G冷编；
报告的所有肯定／否定均依成功编译，不依赖有限样本或失败错误码。
禁用构造、导入闭包、定义切片及独立复核记在 LOG。
既有数学文件不动，无完整 ψ／γ、无新成品闭项或强度下界；P1仍 x=Ω·ω²。
