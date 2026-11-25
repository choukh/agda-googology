# S3 第六轮： (b) 起点与 Ω_Ω 已过，γ 仍缺可入兼容

**结论是 (b)。(i)(ii)成立，(iii)未完成。** 新 InvR 随选中的分支另取合法界，
已在原 Ω_Ω 上实填，不再要求全树共享一个 B。卡点在下一项：
只用原 Gd 作为可入域，不能无条件运输扩界后的路径；当 γ 目标ν=Ω时，
合法的 Ω_ν 种子与保留ν的环境不兼容，所需正规源 Ω_{Ω+1} 被这个候选排除了。
这不是一个具有 InvR 输入的实际 γ 输出反例，不否定其它 Ad／shift 设计或 S3。

第七轮的[实际需求复核](YiRound7.lagda.md)已证明：no-gamma-seed 那一对在逐项有限列对应下不是冻结的 Actual；因此它读作“不变量要求过度”，本身不构成实际 γ 保持的反例或障碍。这里的 Actual 只覆盖可数源的 fsnc；γ 内部其它调用须另外定位。以下定理与结论原样保留。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound6 where

import OCF.Align.YiRBase
import OCF.Align.YiRCountable
import OCF.Align.YiRStep
import OCF.Align.YiRTransport
```

## 保留的旧否定与本轮新接口

按作者确认，[第五轮入口](YiRound5.lagda.md)已补记：no-inv只否定
“全树共享一个界”的形状，不否定沿当前路径换Ctx的方案。
旧Inv、LF、CP及Ω均未改动。

[YiRBase](YiRBase.lagda.md)的Path在当前Ω结点只检查当前派发字段k+1。
选中合法输入η后，取一个该支的合法新界B′，给CP B B′及该支在B′里的后续证据。
不同η的B′没有比较义务，也不生产它们的共同界。
InvR再保存Ctx Env，使沿所选路径的每次界扩展都能运输环境成员。

该候选暂取原Gd守卫为可入域；并未额外给出依赖当前Ctx的Ad。
Ω处的函数逐支提供后续证据，不把不同支的字段收集到一个旧B；
但它仍要支持每个原Gd输入。这正是后面被检验的覆盖选择。

## 先读 C 线：三条律与原停点

已读[CRw的PS／PH](../Lean/CRwFold.lagda.md)、
[PH-ΦX](../Lean/CRwPath.lagda.md)、[X1Up入口及naive-anti](X1Up.lagda.md)、
[X1UpIf](X1UpIf.lagda.md)、[RouteSeal](../../Survey/RouteSeal.md)、
[Stage §3](../../Survey/Stage-2026-11-06.md#3-四层各自的困难)。只作参考，没有导入C线模块。

CRw的PH只对Ad可入坐标要求在nx给出的新世界递归。
PH-mono依靠ev↑、ad↓、nx↑；PH-⊞把左加项搬进分支新界时也用PH-mono。
PH-ΦX是带这些条件、旧Tw结构及地板/输入路径的同底结论，不能直接作为新InvR的γ定理。
X1Up的naive-anti只否定其具体实例中的朴素反单调律，不是本轮候选的否定定理；
它提示必须把可入域及进入后世界一起设计，不能只换一个递归谓词。

旧C线在不可数层兼容、留下结点须对任意坐标有定义处受阻。
本轮的避让尝试是：不在不同分支间比较字段，进入哪一支就只构造那一支的界；
新界全是Level，未降到固定可数类型。但仅此尚未解决原Gd输入与当前Env的兼容。
本轮没有因此声称已绕开旧C线停点。

## (i)(ii) 的实填证明

[YiRCountable](YiRCountable.lagda.md)给树侧辅助定理：
Small是仅含零、后继、ℕ极限的层号形状，不预设合法性；
omega-fields证明Small x时，Ω_x的全部派发字段都是x的CP。
up-fields／upK-fields／upN-fields沿结构互递归，覆盖下标内部及合法分支。
raw0-small给每个零层原始坐标读回的Small证据。

合法性另由原Gd中的Lgl及lgl→Legal给出，不把形状当成合法性，
也不需要函数外延把两条自然数函数认成同一条。

[YiRStep](YiRStep.lagda.md)的fields-path把旧单界证据转成逐支新路径：
在已有全字段界时，每支可继续取同一个B；反向没有这个要求。
of-global据此复用第五轮start，得到(i)。

在原Ω_Ω上，外层当前界为1。对每个Gd(0,1,η)，令x=up0η：

- coordinate给合法x；coordinate-after-one由守卫给CP 1 x。
- raw0-omega-fields给Ω_x的全字段界x。
- branch-path把它转成该支的Path。

omega-omega／omega-omega-inv于是对所有合法零层分支给(ii)。
enter沿选定支的CP B B′运输整个Env，得到那一支的InvR，没有跨分支合界。
因此第五轮a、b两字段可以分别在自己的分支界中，不再造成初始矛盾。

## (iii) 的实际停点：运输与标准种子

[YiRTransport](YiRTransport.lagda.md)先否定一个不能免费照搬的运输接口：
no-unconditional-raise。旧Path 1 Ω_Ω与1 CP b都已实填，b为第五轮的自然数极限树，
但Path b Ω_Ω不存在：只取ηa这一支，新界若保b并包含该支派发suc a，
就给a、b一个合法共同CP界，与已编译no-common矛盾。
所以即使两个界都是Small，也不能由界顺序推出本候选的Path运输。

更具体的γ种子检查取ν=Ω₁，即首个带Ω结点的层号树。
标准种子为Raw ν里的top，seed-guard实填其守卫，seed-read以refl读回Ω_ν。
seed-context也实填携带ν与0的合法上下文。

然而no-gamma-seed证明：对任意Env，InvR(ν∷Env)(Ω_ν)不存在。
证明只进入种子的一条Raw0 ηa支：旧环境要求保ν，新支要求包含字段a，
而ν与a两向CP均被否定。允许其它支另取其它新界不能修补这一条支。
no-gamma-source再证明合法正规源Ω_{ν+1}也无InvR：根派发位置让ν可入环境，
其第一子树正是Ω_ν，就会导出前述不可能的种子证据。

这里的输入覆盖不足是真正的停点：不能把更高源的InvR前提已空
包装成“对一切层的γ保持”定理。本轮没有定义γ全部迭代或ψ其它情况，
也没有得到一个非空InvR输入的实际γ输出反例。
需要另给依赖当前上下文的Ad及实际γ点落入Ad的证明，或另一个满足任务的接口；
本轮不把未实填的Ad／shift当作已有结果。

## 编译错误原文

在γ种子的新上下文里，尝试复用(ii)的读回新界算法：

```text
attempt = one-in-B ,
  fields-path B (Y.tree S.Ω₁) (fields-mono one-in-B one-omega-fields) ,
  (λ η e → coordinate η e , coordinate-after-one η e , branch-path η e)
```

B取seed-context里的ν+1。单6G退出42，下面仅替换实验目录路径：

```text
<实验目录>/RSeedAttempt.agda:24.29-53: error: [UnequalTerms]
F.zero !=
F.lc (Y.tree Y.zero) (V.cO (Y.tree Y.zero)) (V.upT (Y.tree Y.zero))
(λ η₁ e₁ → V.up (Y.tree Y.zero) η₁)
of type F.LF
when checking that the expression coordinate-after-one η e has type
V.CP (Y.tree B) (Y.tree (coordinate η e))
```

守卫只给1到读回坐标的位置，没有给ν+1到坐标的位置。
这一算法失败之外，no-gamma-seed才排除了任意其它合法新界对该选定分支的修补；
不把一次类型错误当成所有分支相对接口不可能的证明。

## 五墙与“不可数坐标”的精确范围

当前停点是“原Gd全域与保留旧上下文的可入兼容失败”。
运输反例已在两个Small界之间出现；γ种子例首次保留非Small的旧目标ν=Ω，
但矛盾仍显现在嵌套的Raw0支ηa，并没有调用不可数坐标判等。
因此不能直接写成“已重证C线的不可数坐标墙”。

| 交接的墙 | 本轮的前提核对 |
|---|---|
| 裸下标精确更新推出判等 | 无函数世界at/off写回，未实例化 |
| 拷贝墙 | 无独立种类拷贝间Bd路由或WMatch，未实例化 |
| 固定坐标收缩自身高度 | 未构造整层编码/解码retraction，未实例化 |
| 回灌必须合法化 | 未给全坐标sh与新界=e+1的实例，未实例化 |
| 留下带反馈的下层规则冲突 | 未定义Keep与PS.ad↓规则，未实例化 |

C线“留下的结点须对任意坐标有定义”的域问题在这里仍是相关义务：
原Gd不能自动保证坐标适应当前Ctx。若想沿Raw0用shift处理任意高层B，
还需层兼容前提；不能把任意高层信息送进固定Raw0。本轮没有尝试该总编码，
没有要求UIP／Funext、裸下标律或改变纲领约束。

## 翻译账与验证

新Path只按树构造子、CP和合法界分情况；branch界由读回树或原界本身给出，
不按记号语法分情况。Small辅助与界运输均是树侧定义。
原Gd作为全部可入域是本轮明确检验的设计选择，其覆盖缺陷如实保留，
不以“改名成Kripke可入”假称已经满足ev↑／ad↓／nx↑。
所有旧数学定义不动，没有C线或记号导入，也没有因验收去改树形。
P1仍x=Ω·ω²；(iii)未完成，不能报告ψ派发已没有结构障碍。

正式从仓库根，单路6G；冷编与依赖审计记入LOG：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound6.lagda.md +RTS -M6G -RTS
```

四件数学模块与入口共五件删除各自接口后冷编，均Checking、单6G退出0；
safe／without-K齐全，禁用构造与洞0。源码导入闭包本地16／库叶19，记号禁用0，
成功编译器图的本地集合一致，无C线或X1Up导入。相关定义切片的记号命中均0，
读标签正对照正常；不作完整成品或成本认证。
Countable／Step／Transport及入口的证明与范围经配对只读审查，审查路模块由主路冷编复核。
失败scratch另退出42，未进入成功导入闭包，也未使用其HTML或切片。
