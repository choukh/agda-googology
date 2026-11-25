# S3 第三轮： (b) 前缀 Ω 仍有实际不可比对

**结论是 (b)。** 前缀 Ωprefix(x)=x ⊞ Ω(x) 对一切合法层号保持合法，
其塔和极限 Λp 也合法；但不能覆盖全部实际 fsnc 比较。
新反例为 **(Ω·2+1, ω)**：目标 ω 不是 ν=Ω·2 的字面子项。
在本轮前缀表示下，两端互不为 CP 第一位置，故没有任何合法 CP 公共上界。
这限定于本轮构造方程与 CP，不否定其它表示或 S3。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound3 where

import OCF.Align.YiPrefixLevels
import OCF.Align.YiPrefixNames
import OCF.Align.YiPrefixWitness
import OCF.Align.YiPrefixCounter
import OCF.Align.YiPrefixChain
```

## 全层合法性与命名范围

[YiPrefixLevels](YiPrefixLevels.lagda.md) 的 Legal-Ωp 对每个合法 LF 树给
新 Ω 的合法性，不按有限站定制。tower 反复施 Ωprefix，tower-step 由
prefix-position 给相邻位置；Λp 是这条塔的合法 ℕ 极限，ΩprefixΛp 仍合法。
闭包在同一 Level 类型内，不把高层信息送入固定低层类型。
没有证明 Λp 与原 Λ 同值，也没有假设 Ωprefix 一般保持 CP。

[YiPrefixNames](YiPrefixNames.lagda.md) 重做层号命名解释：
零、后继、Ωprefix、有限 Ω 单项和、标准 ω（lim natF）。
ω-fs 证明 ω 码的第 n 支为 natT n，name-coherent 证明命名证书不同
不改变原树投影；不识别证书或 Level 记录本身。

这仍是构造命名子域，不是任意正参数 ψ 的 S4 全域语义解释。
主反例端点均在该域；Extension 固定相同构造方程，agrees 使反例
对任意这样的总扩展仍成立。合同有 structure-model 实例；其中其它
正 ψ 填 Λp 只用于展示可满足，不参与主反例，不冒充 EBO 值解释。
有限 T 没有新添 Λ 常数，Λp 的构造与合法性在树侧单独给出。

## 实际发生与来源

[YiPrefixWitness](YiPrefixWitness.lagda.md) 使用上一轮已冻结的 Reach、
FsnCall、Actual；集合仍精确跟随 fsn 内部的 fsnc 调用。
从真实 hc-tower 3 的 EBOψ 3 出发，分支依次为：

```text
1,1,3,0,1,1,1,2,2,1,2,2,1,0,0,0,0,3,0
```

每一步均实填 cof=cω。source-equation 证明十九步到达：

```text
parent = ψ_ω(Ω_{Ω·2+1})
middle = ψ_ω(Ω_parent)
source = ψ_0(Ω_middle)
```

comparison-call 为 arg-step(index-step(arg-step(index-step(hit))))，
在最内层 parent 的 fsnc 比较 Ω·2+1 与 ω。counter-call 给 Actual，
counter-gt 由全称 actual-gt 给码比较为 gt；有限搜索只用来找路径。

**来源仍是内层层号字段的后继对外层 γ 链的目标，不是同一 Ω 结点的两个分支。**
target-origin 给 t10=ψ₀(Ω_{Ω_{ω+1}})，gamma-origin 给 t10→t11
运行 γ_ω 链的确切等式，目标 ω 从这条外层链进入。
最内层正规 Ω_{Ω·2+1} 的共尾层为 Ω·2，比较取其后继。

上一轮的来源分析保留：[YiRound2](YiRound2.lagda.md#实际发生路径与形状)
中 (Ω₂+1,2) 的目标 2 来自 Ω_{Ω₃} 处 γ₂ 链；前缀修补确实消除了那一对。
本轮新对的目标 ω 不出现在 ν 的字面子项中，单点修补的结论不能外推。

## 不可比性与字面无关

[YiPrefixCounter](YiPrefixCounter.lagda.md) 的 left-not-right 排除左端
是 lim natF 的第一位置：若是，左端就须是一棵有限后继树，然而它含 lc。
right-not-left 沿左端有限的 suc／fst 脊柱排除 lim natF；no-common
再用已证明的公共界化简排除任意合法 CP 公共界。
actual-counter 与 extension-no-common 分别交无条件实例和任意总扩展版本。

Pure 表示所有 ψ 的参数为空的递归 Ω 单项和；ν-pure 实填 ν。
Sub 明列字面自身／下标／参数／尾项／单项头的出现关系，pure-sub
证明该域对子项封闭，而 ω-not-pure 排除 ω。
target-not-in-index 因而编译证明 ω 不在 ν 的字面子项内，不只是未搜到。
它没有否定码侧小于关系，也没有把“字面无关”当成语义独立。

## RR3-Design §2.4：条件定理与仍未证明的部分

[YiPrefixChain](YiPrefixChain.lagda.md) 把可以直接证明的条件精确列出：
有向图的每条边被解释成同方向 CP，且任意两顶点有有限有向路径到共同后继，
则解释像有合法公共界，故沿 CP 成链。共同后继的像就是所需合法界；
自然数后继图实填这两个前提，不是空合同。
proper-wf／proper-irrefl 对第一位置的真结构下降证明无环，cp-antisym
给 CP 反对称；common-cp-dec／common-eq-dec 在给定合法公共界时
判定 CP 与原树相等。Consequences.cp-dec／tree-eq-dec 将这两个决策
用于满足图条件的全部解释像，所以这条条件结论确实给可判定的 CP 链。
这里所有相等都只涉及原树，不涉及 Level 记录或合法性证据。

**本轮没有证明“任何覆盖全部 Actual 的表示，其全部实际层号必成链”。**
卡点是实际图自身的共同后继／共同合法脊柱事实；它不由逐边覆盖给出。
若只给逐边 Common，连 CP 方向也未固定。实际比较全为 gt 是码侧事实，
不能在任意表示下代替这些树侧证据。

Counter 的 fork-edge-position／fork-not-chain 另给一个三顶点有限图：
0→left 和 0→right 都有 CP，两个上端仍不可比。
这只否定“逐边覆盖＋共同下端就足够”的抽象推理，不是 Actual 图的反模型。
此外，从树像的比较搬回原层号码上的全序，还需相等反射及序方向保真；
本轮不把树像、合法性证书相等与码相等混为一谈。
所以 RR3-Design §2.4 的实际图全称主张仍属待证判断，未据此关闭路线。

## 翻译账与验证

| 本轮结构 | 来源与用途 | 边界 |
|---|---|---|
| Ωprefix 与塔 Λp | 按作者指定前缀修补，合法性来自原加法／结构 Ω | 没有改旧定义，未证明同值或全比较覆盖 |
| Name 的 Ω 和、标准 ω | 第 4 层按参照构造命名，ω-fs 核对基本列 | 不进入纯树定义；不是任意 ψ 的语义解释 |
| 十九步路径、Sub／Pure | 实际发生与语法来源诊断 | 提供当前表示反例，不是成品强度 |
| ChainHyp | 显式共同界来源的图条件 | Actual 的共同后继尚未实填，不冒称全局链 |

没有写 ψ、反馈、FGH 或改已有数学定义；没有 UIP、Funext、裸层号比较律。
五墙中世界更新、拷贝运输、固定 HB 收缩、反馈合法化、留下结点规则的前提
均未引入。P1 仍为 x=Ω·ω²；本轮不是新的序数值前沿。

正式编译从仓库根，单路 6G：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound3.lagda.md +RTS -M6G -RTS
```

五个数学模块与入口共六件删除各自接口后冷编，六件均 Checking，
单路 6G 退出 0；safe／without-K 齐全，禁用构造与洞 0。
旧依赖用已有接口，不使用 ignore-interfaces；没有失败的 Agda 轮次。
结构闭包与反例证明经配对只读审查，条件链定理经主路读证、删接口冷编。
闭包、切片及导航审计数据同时记入 LOG；不以搜索无反例宣称全称结论。
