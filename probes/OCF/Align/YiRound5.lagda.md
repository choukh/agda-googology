# S3 第五轮： (b) 全分支共用单界的不变量在零层坐标已失败

**结论是 (b)。** 本轮把“当前树的一切 Ω 字段都在同一个 B”按完整树理解，
包括每个合法 Ω 分支内部的字段。Ctx及局部保持可以无记号地写出，
但当前 LF／CP 表示的奇异 Ω 根已含两个互不为第一位置的字段，
所以不能给它初始化这样的 Inv。前缀 Ω 的相应根也已证明不能满足该 Inv。
这不是泛称 S3 不可能；否定的范围是这个全分支单界接口和检查过的树形。

**第六轮范围补记（作者确认）：no-inv否定的是“全树共享一个界”这一形状。**
折叠沿一条路径前进，进入分支后换上下文的InvR属于另一份不变量；
本篇没有否定这种分支相对设计，也没有否定乙路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound5 where

import OCF.Align.YiCtxBase
import OCF.Align.YiCtxStep
import OCF.Align.YiCtxFork
```

## 先读的 C 线接口与可复用边界

按作者要求已读[RouteSeal](../../Survey/RouteSeal.md)的维护政策、
[Stage §3](../../Survey/Stage-2026-11-06.md#3-四层各自的困难)，
以及[CRwFold](../Lean/CRwFold.lagda.md)的PS／PH、
[CRwPath](../Lean/CRwPath.lagda.md)的PH-mono／PH-ΦX。
这些文件只作参考，没有进入新模块的导入闭包。

PH在一个Ω结点的形状是：种类证据Ev B κ，加上对每个可入输入
e、a:Ad B κ e，在新世界nx B κ e a里递归证明分支带路径。
因此它不要求全部合法分支里的字段都留在同一个旧B；
psStep还把新种类的可入写为存在更大的世界及该世界中的分支路径。

可复用的是“证书随构造给出、只在已给路径的域上比较、在进入分支时携带
新界与旧证据运输”的组织方法。不能直接复用其结论：PH-ΦX限定旧Tw XS m
的同底折叠，还需种子/输入PH、路径结构及B在1之上的前提；
它不是任意LF或本轮Inv的现成保持定理。
PH-mono／PH-chain也依赖ev↑／ad↓／nx↑等迁移律，本轮没有免费加入这些律。
Stage的不可数坐标、反馈、留下规则停点与这些前提分开核对，不能统称同一堵墙。

## 冻结接口与已经成立的部分

[YiCtxBase](YiCtxBase.lagda.md)把树环境取为有限List Level：
每个成员是合法树，不读上一轮Env中的记号码，也不补raw树的码。
Ctx保存合法Level界B及每个环境成员到B的CP。
Field k t记录t中某个lc k的字段；Inv要求它的派发字段suc k到B有CP。
区别k和k+1，才能从后者的定位给新增γ目标k的定位。
Field包括下标、第一支、ℕ支及每个Gd守卫允许的Ω分支；没有悄悄改成活动路径。

[YiCtxStep](YiCtxStep.lagda.md)已经编译的正面部分：

- field-legal：合法当前树里的字段k自身合法，随取出构造合法Level。
- compare-field-env：任一派发字段与环境成员都在同一合法界下，可用compare。
- raise-ctx／raise-inv：若已给旧界到合法新界的CP，则运输旧证据。
- adjoin-field：已定位字段k+1的前驱k可加入Env，取B′=B，当前树的Inv保持。
- pred-inv：当前树为后继时，取其前驱保Inv。
- start：Env=[0]、当前最小正规Ω₁时，B=1给完整Inv。

adjoin-example与pred-source／pred-example实填上述局部保持前提。
但adjoin-field只证明“Env加入ν而当前树不变”这一半；没有证明新γ输出的全部字段保持。
start也只是最小正规Ω的实例，不冒称全部塔根的初始化已经完成。

## 卡点：全分支单界，而非不可数坐标

[YiCtxFork](YiCtxFork.lagda.md)检查原结构Ω的奇异根及前缀候选的对应根。
反例使用两个第0层合法坐标，只有零、后继、ℕ极限，不用任何高层Ω坐标。
两个分支读回后，各自在内层产生一个Ω结点；其字段分别为两条不同的自然数极限树。
每条极限的相邻项都按后继前进，反例不依赖常值极限。

两字段的第0支不同，故树不相等；若一方是另一方的真CP，就须进入一个有限后继树，
而极限树不可能是有限后继树的CP。因此两个方向都被编译否定。
若存在Inv，它给两字段（乃至其后继）到B的位置；compare立即迫使二者CP可比，矛盾。
所以不只是某种合界算法失败，而是这些固定字段没有任何合法CP公共界。

raw坐标的Gd前提及两棵当前根的合法性均实填；Ctx[0]本身也有实例。
不可满足的是这些奇异根的全字段Inv，不能用“再选更大的B”修补。
两条读回的自然数列逐项等于相应有限树，但没有用函数外延识别整个lim函数。
这一步并未要求UIP或Funext。

两条编译否定分别是no-inv与prefix-no-inv，对任意树环境Env成立。
原Legal的分支单调仅对已经有Gd／Cp关系的坐标对要求输出关系；
它不使所有位于同一下界之上的坐标两两可比。本轮Inv额外要求全分支字段
共享一个CP界，才强制这些字段成为一条脊柱；反例没有否定原Ω或Legal。

## 编译失败的合界尝试

另外检查“把两个字段放在一个ℕ极限的相邻两支”这一树侧候选。
它不按记号语法分情况，但合法性需要从第一字段到第二字段的CP；该位置不存在。
失败实验直接使用Fork导出的两个实际字段包：

```text
pair : ℕ → Y.Level
pair zero = a-level
pair (suc n) = b-level

candidate : Y.Level
candidate = Y.lim pair (λ { zero → V.self ; (suc n) → V.self })
```

单6G退出42。原文如下，仅把实验目录路径换成占位符：

```text
<实验目录>/CtxJoinAttempt.agda:14.36-42: error: [UnequalTerms]
OCF.Align.LevelFixCore.LF.suc (OCF.Align.YiCtxFork.nat-read n) !=
V.up OCF.Align.LevelFixCore.LF.zero (OCF.Align.YiCtxFork.raw-nat n)
of type OCF.Align.LevelFixCore.LF
when checking that the expression V.self has type
V.CP (Y.tree (pair zero)) (Y.tree (pair 1))
```

实验本身不进导入闭包；此错误指出step0的候选CP不能填成self。
否定任意其它B的结论依靠已编译的no-common／no-inv，
不把这一次合界算法的类型错误当作一般不可能性证明。

## 五堵墙逐条对照

| 交接中的墙 | 该定理的关键前提 | 本轮是否具备 |
|---|---|---|
| 精确世界更新推出弱判等 | 在裸下标函数世界上给更新及at/off律 | 没有函数世界或精确分量写回；adjoin-field只复用已有B |
| 拷贝界运输 | 指定独立世界拷贝间的Bd路由／WMatch | 没有KS种类拷贝、坐标映射或跨拷贝路由 |
| 坐标收缩自身高度 | 把整层高度编码到固定坐标并有retraction律 | 没有这样的编码或收缩律；只使用既有结构读回 |
| 反馈必须合法化 | 进入后界=e+1，并有全坐标反馈sh | 没有定义ψ反馈sh或该新界规则；字段合法性随当前树给出 |
| 留下带反馈与下层规则冲突 | Keep形状、回灌坐标和PS.ad↓等下层律 | 尚未定义留下的ψ结点或这些规则，不能套用no-lower-rule |

因此本轮未实例化五条墙的完整前提。卡点更早：全体合法分支的字段
被要求共用同一条CP脊柱，零层坐标已经能产生不可比字段。
不能把这个结论改写成“旧C线的不可数坐标墙已被重证”。

## 停点、翻译账与验证

未完成的是全部初始塔根的Inv与新γ输出字段保持；没有续写ψ的其它情况。
Ctx／Inv及保持辅助只按树形、位置证据和合法性定义，无记号、C线成品依赖。
旧LF、CP、Ω、Ωprefix、合法性及第四轮历史来源定理均未修改。
Env来源可追溯不自动给Env和全部分支字段的公共CP界，这是本轮新划出的边界。

若以后改成可入分支各有新Ctx，属于另一份接口与义务，不能算本轮已完成；
这里没有自行改变“全部字段同一B”的约束，也不否定那个不同接口或S3。
P1仍为x=Ω·ω²，没有新闭项、FGH或序数值下界。

正式编译从仓库根，单路6G，冷编、禁用构造及导入闭包审计统一记入LOG：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound5.lagda.md +RTS -M6G -RTS
```

三件数学模块与入口共四件删除各自接口后冷编，均Checking、单6G退出0；
safe／without-K齐全，禁用构造与洞0。代码导入闭包本地12／库叶19，记号禁用0，
成功编译器图的本地集合完全一致，没有CRw模块。
Ctx／Inv及局部保持与否定的定义切片均无记号命中，读标签正对照正常；
这些是依赖审计，不是完整成品或成本认证。证明和范围已配对只读审查。
失败的合界scratch单独退出42，未把它或其HTML作为成功证据。
