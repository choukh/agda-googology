# S3 第七轮：(b) no-gamma-seed 的冲突对不是实际需求

**交付 (b)。** 相对于本轮明确的逐项有限列对应，原表示与 Ωprefix 表示中，
no-gamma-seed 用到的那个字段的后继，都不可能以 ν=Ω 为 Actual 目标。
不是搜索不到路径：no-actual-field／no-prefix-actual-field 否定所有这样的路径。
因此第六轮的否定仍是 InvR 接口的否定，不能据它否定实际 γ 派发。

本轮只定义按需 InvD，并检查原／前缀 Ω_Ω 种子；不证 γ 保持，不写 ψ。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound7 where

import OCF.Align.YiDBase
import OCF.Align.YiDSeed
import OCF.Align.YiDActual
```

## 非发生定理的准确口径

[YiDActual](YiDActual.lagda.md)明读既有 Actual、Targets、targets-below。
Actual 仍是从 EBOψ k 沿前驱／ω基本列展开时的 fsnc 调用；
不把 cof、fsTc 的其它比较或尚未定义的树侧 ψ 派发偷偷加入集合。
target-in-env 只有实际目标属于历史 Env 的正向结论；
字段在树里、目标在 Env 里，并不构成 Actual 的见证。

原字段 a=lim(n+1)，前缀字段为1+a=lim(n+2)。
逐项对照采用 FiniteColumns：c 为 ω 共尾，且每个树分支与 c[n]
同时是同一个有限数的 natF／natT 表示。这是闭字段的验收关系，
不是给任意 Raw 树补码；也不把移位列的极限树与标准ω树判等。

- a-columns 实填字面原始码1+ω；prefix-a-columns 实填2+ω。
  两码不是标准形，因而没有把它们作为标准 EBO 层码交付。
- finite-column-bounds 不假定标准形：若 cof c=cω、c[2] 至少为有限2，
  则 c 及 c+1 都小于 Ω。正规 Ω 的 fsn 哑值说明共尾前提必须保留。
- a-any-code-bounds／prefix-any-code-bounds 对任意 FiniteColumns 对应码成立，
  由同一证书的第2支分别读出有限3／4。不靠码唯一性或上述两个展示码。
- no-any-actual-pair／no-any-prefix-actual-pair 再与 targets-below 的 gt 冲突。
  no-actual-field／no-prefix-actual-field 把字段树保留在存在码的命题里，
  从而全局排除这个树／码逐项对应口径中的实际发生。

若有标准形满足该列证书，也在否定量词内；没有声称已构造标准形实例。
不涉及仅按序数值对应、基本列却不同的解释，也没有新增序数值验收结果。

## InvD 与种子检查

[YiDBase](YiDBase.lagda.md)是无记号的树侧接口。
InvD D E t 保存已有 Ctx E；对每个字段 k、每个 u∈E，
只在有需求 D(suc k,u) 时提供该对的合法 Common。
不同需求不共享界，需求的界也不必扩展整个历史界。
这去掉了旧 InvR 为每个分支字段保留整个 Env 的额外要求。
没有假定任意两个裸层号都可比。

[YiDSeed](YiDSeed.lagda.md)按树结构证明 seed-fields／seedp-fields：
原种子与前缀种子的全部字段都是 Small，含下标内部、第一支、每个合法 Raw 支。
small-position 从 CP 的向下封闭给这一步；add-small-fields 处理前缀。
没有为不可数坐标判等，也没有给 Raw 输入生成码。

验收层的 ActualDemand 是一个明确的保守需求包络：
码侧带真正 Actual，树侧保留 Small→候选派发码<Ω 的码界，
以及当前 Env=[Ω,0] 的两个闭目标名字。它多收同一可数层内的候选，
不冒称精确 Rep 或完整树侧运行关系。

seed-invD／prefix-seed-invD 无额外前提地检查全部这些需求：
目标Ω时，字段 Small 与 targets-below 排除需求；目标0时，派发树本身就是公共界。
root-demand／root-checked 用实际 first-call(1,0) 实填非空的需求及公共界，
所以不是把 D 定义为空来放过种子。no-counter-demand 两版也单列了确切冲突字段的排除。

related-check 明列将来应用到完整对应 Q 所需的两条覆盖义务：
Q 保 Small 码界，且在当前 Env 中保两个闭目标名字。
任何满足这两条的 Q 相关 Actual 需求均由包络覆盖；不要求 Q 对原始树全定义。
本轮不交完整 S4 对应的这两个实例，也不从种子检查推断 γ 保持或 ψ 已可派发。

## 翻译账与验证

InvD、字段形状与前缀处理只按树、合法性、CP 定义；纯树模块不导入记号或 C 线。
ActualDemand／FiniteColumns／finite-column-bounds 属第4层，按作者本轮授权读 EBO 基本列。
未把记号判据写入树、合法性或新的树运算；旧 LF、Ω、Ωprefix、InvR 均保留。
未要求 UIP／Funext、裸树下标律、高层到固定类型的总编码或纲领外约束。
不实例化五堵墙的新前提，不关闭乙路线。P1 仍 x=Ω·ω²。

正式从仓库根，单路6G：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound7.lagda.md +RTS -M6G -RTS
```

三件数学模块及入口共四件，逐件删除自己的接口后冷编退出0；禁用构造0。
树侧两件的源码与编译器导入闭包无记号／C线依赖，定义切片为0；
本入口及 Actual 诊断按授权含记号，不将其误报为成品闭包干净。
详细编译、配对只读复核与导航检查记于 LOG。
