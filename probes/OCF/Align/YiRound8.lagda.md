# S3 第八轮：(b) γ 输出的保留分支尚未接通

**交付 (b)，γ 步保持 InvD 未完成。** 起点、前驱与进入原分支已证；
实际 γ_Ω 的合法种子包及其 InvD 也已实填。停在构造下一点的保留结点分支，
不是再次证明旧 InvD 过强，也没有给出“非空 InvD 输入的 γ 输出不保 InvD”定理。

本轮检验的接法是：保留原 Gd 全域，保留支继续递归调用同一 ψ，
每个被递归处理的 Ω 根仍以合法 CP 公共界派发。此接法在一个具体合法支上
缺少公共界；no-keep-seed-dispatch 排除了这份局部派发接口。
不否定其它坐标／上下文表示或乙路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound8 where

import OCF.Align.YiGammaBase
import OCF.Align.YiGammaKeep
import OCF.Align.YiGammaWitness
import OCF.Align.YiGammaSeed
```

## 读过的定理链与第六轮补记

开工前已读 [RouteReview3 §5.7](../../Survey/RouteReview3.md#57-以甲为脚手架完成乙-s1-与-s3-的定理链-2026-11-09-汇总)。
S1 的逐项 ψ 模板、种子合同保留；S3 已证明目标由历史生成，
也已经排除“字段在树中、目标在 Env 中就必须相容”的过强要求。
[第六轮入口](YiRound6.lagda.md)仅补一句回指第七轮：no-gamma-seed 读作
不变量要求过度，其本身未定位实际 γ 调用，不单凭它称实际保持的反例或障碍；
第七轮的非发生范围限于冻结 Actual，γ 内部其它调用本轮另行定位。
旧定理、结论及定义不改。

先重读 [CRw 的 PS／PH](../Lean/CRwFold.lagda.md)、
[PH-ΦX 及 PH-ch](../Lean/CRwPath.lagda.md)、[X1Up](X1Up.lagda.md)、
[RouteSeal](../../Survey/RouteSeal.md)、[Stage §3 层2](../../Survey/Stage-2026-11-06.md#层-2-折叠)。
CRw 的保路径证明需要实际折叠的低层归纳假设及可入／世界运输律，
不能用“迭代一个已经返回证书的任意函数”冒充 γ 保持。
这里只参考，不导入 C 线模块，也没有重开 C 线。

## 已实填的非空构造

[YiGammaBase](YiGammaBase.lagda.md)给纯树结果：

- start 对任意需求 D 给 Env=[0] 的最小正规起点，复用旧 Ctx。
- pred-inv、enter-inv 分别沿后继前驱／原合法支缩小字段集合；不新增需求。
  pred-inv 的前提可由 suc-inv(start D) 实填；进入分支的实际实例是下文 entered-seed-invD。
- Point ν 从 Raw ν 坐标与原 Gd 守卫开始；read-point 的 Legal 随读回给出。
  Certified 把该点与读回树的 InvD 放在一起，不假设存在下一包。
- seed=cOν 对一切合法 ν 有 Point；seed-read 与结构 Ω 一致。
  certify-seed 仅把已有种子 InvD 装包，不把它叫 γ 保持。

携带的数据各有用途：raw 是下一次 f γ 的分支参数；admitted 是这个参数所需的
原 Gd 证据；invariant 供该读回输出以后真正需要的字段／目标比较。
没有任意 Level→固定 Raw ν 的回收器，也不把此坐标包改成树的新构造子。

## 实际 γ，不是任取的一对

[YiGammaWitness](YiGammaWitness.lagda.md)的九步编号为
1,0,0,2,1,0,0,2,0，从 EBOψ 3 到 ψ₀(Ω_{Ω+1})。
每步都有 Reach 与 ω 共尾证据；source-equation、outer-actual 已编译。
外层真正的 fsnc 比较是 (Ω+1,0)，因此引入 ν=Ω。

seed-equation／seed-feedback／first-equation 给：

```text
β  = Ω_{Ω+1}
γ₀ = Ω_Ω
β[γ₀] = γ₀
γ₁ = ψ_Ω(Ω_Ω)
```

[YiGammaSeed](YiGammaSeed.lagda.md)核对完整旧 Env 为
[0,0,0,1,0,0,0,0]，新 Env 在前面加入 Ω，没有丢掉1或重复0。
old-context／new-context 分别用1／Ω作界，故这里不是历史合界失败。
β-tree、seed-tree 均在已有零／后继／Ω命名域逐构造子对应。
source-invD 认证待折叠的参数树 β，不是假称已给整项 ψ₀β 的树解释。

source-invD、seed-history-invD 以及 gamma-seed 实填第七轮同一个 ActualDemand Ω
包络下的前提。它只允许闭目标0／Ω，旧历史成员1没有此包络的需求；
不据此声称完整 γ 内部调用已被覆盖。前提非空，同时范围保持明确。
entered-seed-invD 还从当前参数的 InvD 与原守卫直接进入 γ₀ 所选支，
得到加入新目标以前的种子 InvD；它仍不是 ψ_Ω 在这棵种子上的下一次输出。

## 真正缺的是哪个分支的证据

把 ψ_Ω 作用于 γ₀=Ω_Ω，根的比较是1<Ω，root-common 已有合法公共界。
按模板保留该根后，分支函数仍须对原 Gd 每个合法 η 定义。
选择 η=ηb=suc(lim raw-nat)：guard-b 已实填，该支正是 Ω_{suc b}，
b=lim nat-read。selected-branch-tree 是这个树形的 refl 方程。
下一次递归根派发需要 Common(suc b,Ω)。

[YiGammaKeep](YiGammaKeep.lagda.md)的 no-common-b-ν 排除任意这样的合法界：
Ω 不是各支有限的 b 的 CP；b 也不是 Ω 那条有限第一脊柱的 CP。
KeepSeedDispatch 仅收集“合法后继形输入支的直接根”所需证据，
no-keep-seed-dispatch 用这一支否定它。不重新量化所有历史成员、下标内部字段，
也不把这个接口写回 InvD 当作新假设。

代码侧同时核验这个调用的来源与范围：γ₁ 为 Ω 共尾，ω+1<Ω 是合法坐标，
kept-branch-equation 给 γ₁[ω+1]=ψ_Ω(Ω_{ω+1})；
其 Ω 基本列的 fsTc 比较为 (ω+1,Ω)，结果 lt。
b-columns 实填 b 与标准ω码的全部有限列项对应；不用 Funext 把两个极限树判等。

**这不是冻结 Actual 中的一对。** not-frozen-actual／no-kept-demand 明确否定它。
旧 Actual 只记录可数 Reach 源中的 fsnc，而这里是实际 γ 产生的不可数坐标的 fsT 支。
因此不能用这个 lt 对反驳第七轮的全局 gt 定理，也不能把它说成 ActualDemand
下 InvD 不保持。缺口是：构造 γ 输出的保留支所需的递归派发，比现有需求包络多。
即使把所需证据另行携带，当前固定层号树形下也没有这一个 Common 可携带。

## 编译错误原文

在仓库外单6G尝试以当前目标 Ω 本身作界，复用选定支的原 Gd 位置：

```text
attempt : Common (Y.suc W.b-level) R.ν
attempt = R.ν , V.cp→CP F.zero (proj₁ W.guard-b) , V.self
```

退出42；以下只替换实验目录路径：

```text
<实验目录>/GammaKeepAttempt.agda:13.17-48: error: [UnequalTerms]
F.zero != F.lim W.nat-read of type F.LF
when checking that the inferred type of an application
  V.CP (V.up F.zero (V.cO F.zero)) (V.up F.zero W.ηb)
matches the expected type
  V.CP (Y.tree (Y.suc W.b-level)) (Y.tree R.ν)
```

原 Gd 只给1到该坐标的位置，不能给该坐标到目标 Ω 的位置。
这次算法失败之外，no-common-b-ν 才排除其它候选公共界。
没有用这次编译错误或一个被加强的 InvD 前提来否定整条 γ 路线。

## 五墙、C 线停点与本轮边界

本轮确实已用到不可数坐标：γ 种子是 Raw Ω 中的 top，读回 Ω_Ω，
seed-not-small 证明它不是纯零／后继／ℕ极限树；γ₁ 也有 Ω 共尾的码侧证明。
这里“不可数坐标”使用上述 Raw Ω／cΩ 的结构口径，未交 LF 的序数值不可数定理。
具体缺失比较仍显现在其合法 Raw0 支 ηb，不是不可数坐标判等。
与 C 线层2直接重合的义务是“留下的结点要对任意合法坐标有定义”。

| 交接中的墙 | 本轮前提核对 |
|---|---|
| 裸下标精确更新推出判定 | 无 at/off 世界更新，未实例化 |
| 拷贝墙 | 无独立拷贝间的 Bd／WMatch，未实例化 |
| 坐标收缩自身高度 | Point 从本层 Raw 构造，无全层回收／retraction，未实例化 |
| 回灌必须合法化 | 已给种子的原 Gd／Legal；没有提供全坐标 sh 与 nxt=e+1，不声称已实例化该定理 |
| 保留回灌与下层单调规则冲突 | 本轮有保留全域分支的具体派发缺口，未给 PS.ad↓／分量保持的完整前提，不叫重证 no-lower-rule |

因此停止在这个具体接线的构造处；五堵墙的完整接口均未实例化。
没有需要 UIP／Funext、裸树下标律、固定类型坍缩或修改纲领的步骤。
若换上下文相对的层号／坐标组织，需另给位置生成及类型运输，
不能从本篇推断那种设计也不可能。没有继续写 ψ 全部情况或回灌保持。

## 翻译账与验证

Point／Certified、起点与缩小字段的局部保持只读树、原 Gd、Legal、CP、InvD。
尝试保留的根、同目标递归分支及 γ₀=Ων、γ₁=ψν(fγ₀) 均照 JiaExactFold 模板，
尚未去翻译；本轮以局部接口否定精确指出这个模板与当前位置派发的缺口。
Witness／Seed 只在第4层明读记号核验来源、名字及列对应，不将它们导入树侧定义。
没有新的值界，P1 仍 x=Ω·ω²。

正式从仓库根，单路6G：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound8.lagda.md +RTS -M6G -RTS
```

四件数学模块及入口共五件逐件删除自身接口冷编退出0；禁用构造0。
纯树 Base／Keep 的导入闭包及定义切片无记号／C线依赖；
Witness／Seed 与聚合入口按授权是记号诊断，不误报为成品闭包干净。
失败实验不进成功闭包，不使用其 HTML／切片；完整记录见 LOG。
