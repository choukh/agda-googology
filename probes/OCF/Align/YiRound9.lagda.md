# S3 第九轮：(b) 原支已修补，全合法层的保留覆盖仍缺生成证据

**交付 (b)。** 主审建议在第八轮的支上成立，而且可推广到目标 Ω 的全部保留坐标。
两类 DispEv 及 InvD 加结构证据的 InvDS 已定义。全层 γ 保持未完成：
只有 Legal 与一次严格保留证据，不能保证高层合法坐标的下一根也有 DispEv。
本轮给非空反例，不把它说成 EBO 实际轨道反例或两类证据路线的否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound9 where

import OCF.Align.YiDispBase
import OCF.Align.YiDispCountable
import OCF.Align.YiDispHigher
import OCF.Align.YiDispWideAudit
import OCF.Align.YiDispSeed
```

## 两类证据的准确范围

[YiDispBase](YiDispBase.lagda.md)的 DispEv i j 中，j 是 Ω 结点的字段；
原模板比较 suc j 与目标 i。两种来源：

- bounded 保存一个合法公共界 B 以及 suc j、i 在 B 中的 CP。
  bounded-order 只在这个界内调用原 compare，三种结果按旧模板选择保留／折叠。
- structural 保存 Below(suc j,i)：沿后继、ℕ支、第一支或原 Gd 合法 Ω 支的真路径，
  choice 直接为 keep。它不判断有没有路径，不判断其它方向，也不比较两个宽位置。

Below 没有自反构造子，没有把 lc.k 直接视为值下界。
原 Pre 同时记录值分支与 Raw 槽位；它的每个槽位并不自动证明
对应后继层号是目标的真子树。因此本轮采用明确的 Pre 类路径关系，
没有只把 Pre 改名成“小于”。没有新增序数值大小的验收定理。

InvDS 保留原 InvD 的实际需求 D，另保存已知保留调用的结构需求 S。
actual-ev 永远从原 InvD 给出 bounded；retained-ev 才使用 structural。
没有把某个实际需要判定的比较改走结构型。pred-inv／enter-inv 也保留这两个来源，
需求的完整运行覆盖仍另给，不因多了 S 就声称已完成。

## 第八轮那一支，以及目标 Ω 的全部坐标

[YiDispCountable](YiDispCountable.lagda.md)先给 selected-ev：
Ω 的 ηb=suc(lim raw-nat) 支恰为 suc b，因此一条 e-branch 就给
Below(suc b,Ω)，selected-keep 为 refl。不需要补码或给两个宽位置作比较。

successor-coordinate 对每个原 Gd 合法后继形坐标给同样结论；
all-zero-coordinates 更覆盖全部合法 Raw0 坐标：
Ω_(up0η) 内每个字段的派发量，先由已有 omega-fields 得到 CP 位置，
再接上目标 Ω 的真实 η 分支，给 Below。seed-cover 因此覆盖原 Ω_Ω 的全部字段。

all-retained-Ω 再给一个全称定理：对任意合法字段 j，若在目标 Ω 下
DispEv 已选择 keep，则 RetainedDomain(Ω,j) 成立，含第一支及所有原 Gd 坐标。
证明使用 Ω 的真子树全是 Small，再用 up-fields／omega-fields 接到路径上。
Small j 的条件对任意目标也有 small-retained-domain 版本；条件不是空假设，
目标 Ω 的上述定理直接实填它。不是有限测试，也不只检验 ω+1。

[YiDispSeed](YiDispSeed.lagda.md)装配第八轮真实 γ 种子及完整 Env：
seed-mixed 保留原实际需求包络，给 OnlyΩ 结构需求；
实际(1,0)的 actual-root 经 bounded 得到 collapse，所选 b／Ω 支经 structural 得到 keep。
这实填了 InvDS 的非空实例。D 仍是第七轮明列的0／Ω包络，
不把这个装配冒称完整 γ 输出或回灌保持；start 的 NoRetain 实例与原起点也已编译。

## 推广到全部合法层号时，哪里给不出证据

[YiDispHigher](YiDispHigher.lagda.md)只用原树及原 Legal 构造：

```text
j      = lc 1 (cO 1) 0 (λ η e → 0)
i      = suc(suc j)
source = Ω_(suc j)
```

j、i、source 均合法。initial 给一条非自反 e-suc 路径
suc j → i，故初始确实严格保留，不靠 eq；initial-common 还提供判定型来源。
Raw j 的 top 有原 Gd 守卫，读回 Ω_j。该支的直接根字段为1，下一次需要 DispEv i 1。
它也正好是 source 的第一支，所以并非只在任意坐标的深处失败。

- no-common 排除派发量2与 i 的任何合法 CP 公共界。
- no-below 排除 Below(2,i)，no-next-ev 因而排除两类 DispEv。
- no-retained-domain 用合法 top 支的直接 K.at 得出否定。
- no-full-position 还把 lc.k 加入普通子树路径，仍排除2在 i 中出现。
  因而不是遗漏了第一轮 Pre 所允许的字段路径就造出失败。

RetainedDomain 的全部 Field 量词是充分覆盖合同，并非模板最小必要条件；
本反例失败在第一支／top支的直接根，即使删除额外的 in-index、深层字段量词仍失败。
root-slot 的 Pre 槽位确实存在，但 Raw 槽位的类型本身不能当成派发量2到目标的路径。

这是全 Legal 域上对“初始保留证据会自动传到所有后续根”的反例，
没有从 EBOψ k 给出到该树的实际路径，不称其为冻结 Actual 的反例。
也没有证明必须改旧 Legal：可以另外研究带覆盖证据的生成域，
但还须随构造给证据并证明 γ／回灌保持。本轮没有实填这项全层生成闭包。

## 编译错误原文

仓库外尝试把 Raw j 的 top 读回当成目标 j 的真实分支，再穿过两个后继：

```text
attempt : Below (F.suc (Y.tree H.one)) (Y.tree H.i)
attempt = more (more (one (e-branch G.top H.top-guard)) e-suc) e-suc
```

单6G退出42；以下只替换实验目录路径：

```text
<实验目录>/HigherBranchAttempt.agda:11.64-69: error: [UnequalTerms]
(F.lc (Y.tree H.one) (OCF.Align.LevelFixVal.cO (Y.tree H.one))
 (Y.tree Y.zero) (λ η e → Y.tree Y.zero))
!= (F.suc (Y.tree Y.zero)) of type F.LF
when checking that the expression e-suc has type
Edge
(F.suc
 (F.lc (Y.tree H.j) (OCF.Align.LevelFixVal.cO (Y.tree H.j)) _t_11
  _g_12))
(Y.tree H.i)
```

top 的守卫属于外层字段 j；它给 source 中的支，不给目标 j 的支。
j 自身根字段是1，分支恒为0。不是任意 Raw j 读回都能通过目标的分支到达。
编译错误只否定这次接线；任意其它两类证据也不存在的结论由 no-next-ev 保证。

这里确实已有带 Ω 结点的坐标层 j，top 读回也非 Small（top-not-small）。
这是结构口径，不是新增序数值不可数定理；失败还在第一支出现，
因此不把它说成只有不可数坐标才可能失败的壁垒。
未用 UIP／Funext、裸下标比较律、固定类型回收或修改纲领，五墙的完整接口也未实例化。

## Barrier 核对

已读 [Barrier.Ω-Extension 与 barrier](../Barrier.lagda.md)。其关键字段
<ᴵ-dec 对同一宽上界下任意两点给三分，并且要求 Ordᴰ 精确初始段与Ω共尾上界。
本轮没有提供这些字段：

- bounded 仍只消费同一合法树的 CP 第一位置证据，保持原来范围。
- structural 只消费一条给定方向的路径，不判断路径存在性，不比较不同分支。
- 没有构造 Below 与 Ordᴰ 的精确初始段解释，不能直接把它当作 Barrier 的序。

[YiDispWideAudit](YiDispWideAudit.lagda.md)还给编译过的 no-wide-compare：
a=lim(n+1)、b=lim n 都是 Ω 的宽位置，但互不为 Below，且不相等。
在 Small 目标内，宽路径仍能读成 CP，所以旧反例足以证明这一点。
因此当前宽关系的全三分接口本身已有否定，绝不能把两份宽路径送给原 compare。
这不是 LPO 的新证明，也没有把原树路径与序数值序混为一谈。

## 翻译账与验证

DispEv 的判定部分保留原 CP 比较；结构部分来自树的真实分支路径，
没有读记号选择分支或改变 LF／Legal／Ω／Raw／Gd。
InvDS 把实际判定与已知保留的调用分开；两种需求的运行覆盖仍显式待证。
保留递归合同沿原 ψ 模板，但 Higher 只说明旧前提不足，不以它关闭其它证书设计。
Seed 只是第4层已有实际历史的装配，未把其中记号导入成品接口。
P1 仍 x=Ω·ω²，无新值界、FGH 或全层 γ 保持。

从仓库根正式编译，单路6G：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound9.lagda.md +RTS -M6G -RTS
```

五件数学模块与入口共六件逐件删自身接口后冷编退出0；禁用构造0。
Base／Countable／Higher／WideAudit 的源码及编译器闭包无记号／C线依赖；
Seed及入口按授权含第4层记号装配，不误报成品闭包干净。详细审计记入LOG。
失败实验不进成功闭包，不生成或使用其 HTML／切片。
