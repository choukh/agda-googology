# D7 最后一轮：(b) 规范闭包通过，闭种子零步使 gt 停顿

**交付 (b)，触发硬止损第2条。** 四处单调条件均已严格，旧反例被排除；
规范 Ω、读回、cO、top、全部塔层和 Λ 的合法性闭包均已编译。
但存在满足新合法性的 Ω 源，分支严格单调且在下界种子 raw1 上取0。
忠实零步返回1，原守卫又迫这个闭步的 Raw 输出仍为 raw1，
故 gt 输出成为常1列，要求不存在的 Properˢ(1,1)。
按作者硬止损关闭 D7，不再修补合法性、种子或规则，不继续 γ。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFullReport where

import OCF.Align.YiLglFullCore
import OCF.Align.YiLglFullVal
import OCF.Align.YiLglFullExamples
import OCF.Align.YiLglFullFold
import OCF.Align.YiLglFullStop
import OCF.Align.YiLglFullZeroStep
```

## 四处严格的平行块

[YiLglFullCore](YiLglFullCore.lagda.md) 新增 DnL，沿 Pre 的实际槽位读出下层 Dn，
不比较两个裸下标；在 Raw.lc 中用 DnL→Dn 取代原弱分支单调性。
Raw.lim 的相邻 Dn 保留。
[YiLglFullVal](YiLglFullVal.lagda.md) 的 Legal 在 LF.lim 用 Properˢ，
在 LF.lc 用坐标 Dn→分支 Properˢ；同坐标仍只有守卫无关性。

| 位置 | ℕ 极限 | Ω 结点 |
|---|---|---|
| Raw | 相邻 Dn | DnL 坐标步→输出 Dn |
| LF | 相邻 Properˢ | Dn 坐标步→输出 Properˢ |

第一支到分支仍为弱 Cp／CP，Gd 下界仍可取等号。
Ω̂、up、cO 的程序形状不改；这是新的平行类型，不能混用旧 LF／Raw 的证据。
未迁移20个模块，也未修改既有定义或结论。

## 第2、3条：旧反例排除与规范构造

[YiLglFullExamples](YiLglFullExamples.lagda.md) 在新类型里重写旧形状，分别给：

- no-round11-coordinate：常 raw1 的 Raw ℕ 极限不合法；
- no-fold-source：上一轮常1的 LF Ω 源不合法；
- no-old-eta：上一轮常 suc top 的 Raw Ω 坐标不合法；
- no-old-bad：上一轮读回的常 suc Ω₁ LF Ω 源不合法。

这些是新类型中同形对象的否定，不是把旧对象强转到新类型。
FullVal 的闭包定理为：

```text
Legal-Ω̂ : ∀x Legal x → Legal(Ω̂x)
lgl→Legal : ∀y Legal y → ∀T Lgl y T → Legal(up y T)
Legal-tw : ∀n Legal(tw n)
Legal-Λ : Legal Λ
Lgl-cO : ∀k Lgl k (cO k)
```

top 的 Lgl 对全部层为 tt；读回 top 的合法性就是同一 Legal-Ω̂。
dn-proper、Ω-proper 直接运输给定真路径，Legal-Ω̂／lgl→Legal／lglK→Legal
互递归随输出给证据；塔的相邻 Properˢ 和全部层合法性一次成立，非有限采样。
因此本轮没有触发硬止损第1条。

## ψ 已完成的条件归纳步

[YiLglFullFold](YiLglFullFold.lagda.md) 将最小条件接口接到新 Legal：

- 零种子：规范 Ω 的合法性与非零性已有全层定理；零行使用它不需判定。
- 后继：右递归加法保持 Properˢ，非零基步给 copies-step，successor-legal 给输出合法。
- 极限：limit-legal 显式使用递归调用的严格保持，不能只由输入步进冒称输出步进。
- lt/eq 保留：keep-legal 用源的严格 Ω 分支和 proper-map 给严格 out 分支，弱第一支用 cp-map。
  全部合法分支的合法性都由递归合法性给出，没有漏掉分支内部的 ℕ 极限。
- gt：chain-output-legal 仍分开链的真步、out 保持真步、每点合法三项；不是这些项的自动生产器。

这些合同有 Ω 映射／自然数结构链实例，但不把实例说成完整 ψ。
这里检验的是同一 Raw 域上的保留；若另给 coe，必须先给它运输真坐标路径的证据，
组合后才可调用 out 的严格保持。未把旧 Acc 侧 coe 的性质自动搬到新树。
硬止损发生后没有继续补完整 go 互归纳或实际 γ 构造。

## 新反例：分支严格，但下界种子返回原点

[YiLglFullStop](YiLglFullStop.lagda.md) 的 lower 只在 Raw0 上结构递归：

```text
lower zero = 0
lower raw1 = 0
lower (suc a) = suc(lower a)       （a不是zero时）
lower (lim f) = lim(λn lower(f(n+1)))
lower top = 0
source = lc 0 raw1 0 (ληe → lower η)
```

Raw0 没有可构造的 lc／em。lim 丢首支是此**源分支函数**的定义，
不是修改 ψ 或合法性：原列第 n 支的位置证据沿严格步进搬到第 n+1 支后再递归，
lower-cp 给弱路径运输，lower-dn 在源坐标非零时给 Properˢ。
每个尾列坐标非零由前一 Dn 步给出，因此 lower-legal 覆盖全部合法 Raw0。
guard-nonzero 从源的原守卫给非零前提，source-legal 逐字段实填新 Legal。

source 的分支不是常函数，所有 Ω 分支严格单调且严格合法；
反例没有遗漏的 Raw 或 LF 单调字段，也不靠坏 ℕ 子列。
但是 seed=raw1 正是可入下界，body-at-seed 为 refl，分支值是0。
first-at-seed 也为 CP.self；no-first-strict 指明不能把这个已保留的第一支合同再改严格。
因此本例明确使用作者刻意保留的两处弱关系，按指令不再补形状。

目标0、字段0的派发量为1，合法树1是两者的字面公共界；
root-above 携带 Properˢ(0,1)，所以此处走模板 gt。

### 固定性必须来自执行，而不是额外假设

FullStop 的 SeedChain 明读 raw 分量的固定性、初项、步进；
它的 no-rule-preservation 是显式局部合同的条件否定，合同有 canonical-chain 和 observer 实例。
为避免把任意 seed-fixed 偷当成模板事实，
[YiLglFullZeroStep](YiLglFullZeroStep.lagda.md) 另外核验闭零步。

ZeroStep 仅要求这次递归输出仍过原守卫，且读回符合该零步：

```text
output-guard : ∀e Gd 0 seed (step seed e)
read-step : ∀e up 0 (step seed e) = go(body seed e)
zero-row : go 0 = 1
```

guarded-one-unique 证明：若一个 Raw0 坐标过 seed 守卫且读回是1，它只能是 raw1。
top 虽也读回1，却被同一守卫排除；其余构造子逐个排除或递归到唯一 rawzero。
这是**一个带守卫闭值的反演**，不是全局 up 单射、任意 LF→Raw 回收、判定或 UIP。

fixed-from-zero 因而从上述正常执行义务推出每份守卫证据下 step seed e=seed。
给定模板初项和步进，chain-from-zero 推出全部点的 raw 分量仍是 seed，
不比较 Σ 或守卫证据。于是 out 逐点等于 go0=1。
no-faithful-output／no-faithful-preservation 排除该 gt 输出的 Legal，
因为它的第0步要求 Properˢ(1,1)，而 no-proper-one 排除了所有该证据。

canonical-zero-step、canonical-chain 与 observer 给这些局部合同的闭实例，
所以否定不是靠空前提；但 observer 不被冒称完整 ψ，链也未被冒称完整 γ 实现。
本反例只用此次递归零调用，不需要先给其它所有递归调用构造一个完整折叠。

## 硬止损与壁垒

**触发的是第2条：满足新合法性的源，在忠实闭零步及 gt 模板下输出停顿。**
规范构造通过；在上述忠实闭零步合同下，从该种子开始且满足给定步进方程的坐标链
不增长，而非“增长只能靠判定”。完整 γ 函数未实现。
比较也不能给出假的 Properˢ(1,1)，本轮没有触发或声称第3条。

按作者最后一轮的硬止损关闭 D7，不再更改下界、第一支、种子、lower、合法性或 gt 规则。
没有实施局部等值修补、移位挑列或转入 D8 实现。
没有给这个源 EBO Rep／Reach，不称实际 EBO 轨道反例；
关闭的是作者指定的全新 Legal 源域上的 D7 检验，不外推为所有折叠方案不可能。

所有真路径都由结构产生，比较仍只在给定字面界下。
没有 Ordᴰ 精确初始段＋Ω共尾元的有界三歧接口，也没有值严格 View／Enc；
没有实例化 Barrier.barrier 或 BrwViewNeg.strict→LPO。
本轮不需要判定；反例是所要求增长为假的编译事实，不是壁垒推论。

## 翻译账与验证

Raw.lc 新增 DnL→Dn 字段由 no-omega-two 逼出，保留同坐标证据无关性。
LF 的两个严格字段沿用上轮形状，规则仍照 JiaExactFold（照 EBO）的零、后继、逐点极限、
lt/eq 保留与 gt 链模板；不称这些规则已由树自身唯一推出。
lower 是本轮合法反例的树侧结构函数，不是新增折叠规则或新的正则性修补。
旧数学定义与结论不改；README／LOG 按本次澄清更新，并补记 YiLglAll*。
无20模块迁移、完整 ψ／γ、FGH、成品闭项或新值下界；P1仍 x=Ω·ω²。

从仓库根，七件逐件删除自己的字面接口，单6G冷编均退出0；safe／without-K齐全，
禁用构造、洞、UIP／Funext前提、绝对路径和尾随空白命中0。
源码闭包本地2／4／5／5／5／6／9件，各编译器图与源码集合完全一致，记号／C线命中0。
七件及读标签正对照均成功生成HTML与编译器图；核心切片记号命中0，
EboLean3Lab.ebo-lab″正对照为352块、记号33／词36。切片仅是语法近似。
名字／导航检查0问题，七篇6个本地链接全部存在，git diff --check退出0。
独立否定路已由主路读全文、查陈述及实例、删接口冷复核；
配对路另只读核对DnL七槽、规范互递归、源全分支严格与闭值反演，范围核对通过。
