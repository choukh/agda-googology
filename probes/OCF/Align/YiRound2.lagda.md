# S3 第二轮（第 4 层诊断）：(b) 实际比较 Ω₂+1 与 2 无合法 CP 公共界

**结论是 (b)。** EBO-tree″ 的 k=3 支中，沿十二次实际基本列选择，
出现 fsnc 比较 (Ω₂+1, 2)。在当前零／后继／Ω 的自然树表示下，
两端互不为 CP 第一位置，因此不存在任何合法 CP 公共上界。
这个反例对任意保留上述构造方程的总扩展解释也成立，不依赖其它 ψ 码如何解释。

同轮只检查指定修补：新 Ωprefix(x)=x ⊞ Ω(x) 使这一对重新 CP 可比，
并给出合法公共界。没有由单点修补推出全部实际比较都已解决。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound2 where

import OCF.Align.YiSpineCommon
import OCF.Align.YiSpineTrace
import OCF.Align.YiSpineNames
import OCF.Align.YiSpinePrefix
import OCF.Align.YiSpineWitness
import OCF.Align.YiSpineCounter
```

## 公共界等价与实际比较集合

[YiSpineCommon](YiSpineCommon.lagda.md) 按作者的化简定义：
Common a b 是一个合法 Level 界及两份 CP 证据；Spinal a b 是两个 CP 方向之和。
common→spinal 用上一轮 compare，spinal→common 取较大者。
所以对固定的两端原树，仅换一个更大的合法 CP 界不能修补不可比。

[YiSpineTrace](YiSpineTrace.lagda.md) 的 Reach 从 EBOψ k 开始，
只按可数参照树的前驱及 ω 基本列向下展开，带相应 cof 证据。
reach-hc 证明每个到达项都有 HC，根使用真实 hc-tower k。

FsnCall 按原 fsn 的四条调用来源递归：
参数为 Ω 共尾时的 hit、和的尾部、ω 参数内部、ω 共尾 Ω 下标内部。
Actual 保存一个 Reach 源、其 ω 共尾证据及 FsnCall。
**它只记录 EboLeanDef.fsnc 的那次比较，不混入 cofψ₊ 或 fsTc 的其它比较，
也不把任意语法子项当作可到达节点。** 这里不必保存最后 fsn 的 n，
因为这四种内部路由及比较操作数均不依赖该 n。

actual-gt 对所有 Actual 证明码比较为 gt；first-call 在 EBOψ 1 实填 (1,0)。
码比较 gt 不蕴含树侧 CP 可比，下面给实际反例。

## 层号码的解释范围

[YiSpineNames](YiSpineNames.lagda.md) 的 Name c 用零、后继、Ω 给 EBO 层码
命名证书；ι_L 将其解释为上一轮的合法 Level。两个反例端点都完整落在此域。
name-coherent 证明同一码的原树表示不依赖该域内的命名证书，不使用 UIP。

本轮没有伪造正参数 ψ 的通用树侧解释，也没有交付 S4 的全域语义 ι_L。
**这里实现的是可复用的构造命名子域。** Extension 另列任意总解释应满足的
零／后继／Ω 原树方程，agrees 证明它在命名域与 ι_L 一致。
extension-no-common 因而对每个这样的总扩展排除本轮反例的公共界。
所以即使后来实填其它 ψ 码，此反例仍不能在原树形下消失。

structure-model 仅证明 Extension 合同非空：它在未指定的正参数 ψ 分支填合法 Λ。
它不是拟用的 EBO 值解释，也不参与主反例或实际发生性证明。
反例没有利用该任意填值；主结果 no-common 没有 Extension 参数。
Λ 已在 Level 中合法，本轮没有向有限 T 伪添一个 Λ 码。

## 实际发生路径与形状

[YiSpineWitness](YiSpineWitness.lagda.md) 从 EBOψ 3 的真实塔支开始，
依次取 fsn 分支：

```text
1, 0, 1, 1, 3, 2, 0, 0, 0, 2, 0, 0
```

到达的项由 source-equation 编译证明为 ψ₀(Ω_{ψ₂(Ω_{Ω₂+1})})。
它的 fsn 首先递归进入外层 ψ₀ 的 Ω 参数，再递归进入这个 Ω 的下标，
在 ψ₂(Ω_{Ω₂+1}) 处调用 fsnc。其参数共尾度为 Ω_{Ω₂+1}，
故比较操作数恰为 Ω₂+1 与 2。
counter-call 保存完整 Actual 证据，十二步的每一次 ω 共尾均已实填。

**形状分类：是内层 Ω 的层号字段与外层链分支目标之间，不是同一 Ω 结点的两个分支坐标。**
到达 t₅ 后，t₅=ψ₀(Ω_{Ω₃})，t₅→t₆ 的 γ₂ 链引入目标 2，
由 target-origin／gamma-origin 两条等式标明来源。
后来内层正规 Ω_{Ω₂+1} 的共尾层字段为 Ω₂，fsnc 用其后继 Ω₂+1 与目标 2 比较。

## 不可比与指定前缀修补

[YiSpineCounter](YiSpineCounter.lagda.md) 的 left-not-right／right-not-left
排除两个 CP 方向；no-common 用公共界等价排除任意合法公共界。
其中左端树为 suc(Ω(2))，右端为 suc(suc(0))；原 Ω(2) 的 CP 脊柱
经过两个第一支后只到 1，不经过 2。

[YiSpinePrefix](YiSpinePrefix.lagda.md) 仅在新文件给 add 与 Ωprefix。
Legal-add 和原 Ω 合法性随构造给出新合法 Level；prefix-position 对每个 x
证明 x 是 Ωprefix(x) 的 CP 前缀。
patched-position、patched-common 对同一个 Actual 码对 (Ω₂+1,2) 给：
2 是新左端 suc(Ωprefix(2)) 的第一位置，新左端本身就是合法公共界。

这只说明**改树形能消除这个反例**，未证明一般 Ω 位置保持、全部 Actual 可比、
值对应或最终派发闭包；未采用修补覆盖旧定义，也未写树侧 ψ。
不以此反例否定 S3，不改变 CP、LevelFixCore、YiLevelBase 或纲领。

## 翻译账与验证

| 本轮结构 | 来源／用途 | 边界 |
|---|---|---|
| Reach 与 FsnCall | 按参照 HC、fsn 的实际调用定义第 4 层集合 | 不进入乙的定义或合法性依赖 |
| Name 与 ι_L | 明读 EBO 的零、后继、Ω；解释仍用既有树构造 | 仅命名子域，总 S4 解释未交；反例对所有保留此域的总扩展有效 |
| Extension 居留模型 | 证明结构合同可满足 | 正 ψ 的 Λ 填值不作语义解释，不用于主反例 |
| Ωprefix 的 x ⊞ Ω(x) | 为修复实际反例所检查的候选树形 | 只查一对；并未证明这形状在成品中必需或保持值 |

本轮没有世界更新、拷贝界运输、固定 HB 收缩、ψ 反馈或留下路径规则，
未触发五墙的相应前提；没有 UIP、Funext 或裸树上的比较律。
P1 仍为 x = Ω·ω²。这个实际反例及单点修补不是新的成品值前沿。

正式从仓库根，单路 6G：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound2.lagda.md +RTS -M6G -RTS
```

六个数学模块与入口删除各自接口后冷编，七件均 Checking，退出 0；禁用构造 0。
旧依赖用已有接口，未 ignore-interfaces。审查模块经主路从头读证明、删接口冷编。
名字域的限定、Actual 调用路由、反例形状分类及前缀修补均已只读配对审查。

初次退出 42 分别为 source 名字与记录投影冲突、非单射 tree／cof 头下漏显式隐参；
隐藏投影及显式给源项／两端 Level 后通过，没有改冻结接口或使用证明无关。
本轮无 251、无超时，不使用失败轮 HTML／切片。
有限 Python 搜索只提供路径线索；上述发生性、等式与反例均由成功 Agda 编译确认，
没有把搜索无反例或搜索覆盖数当作全称结论。
Common／Prefix 的定义闭包保持干净；本篇聚合为可读记号的第 4 层入口，
不作整篇导入闭包无记号的成品认证。完整审计数见 LOG。
