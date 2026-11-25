# S3 第十轮：(b) 全层保留定理已证，候选 Reg 的 Ω 闭包失败

**交付 (b)。第4条的全层定理成立；卡在第3条的 Ω 保持。**
本轮按候选形状定义 Reg，排除第九轮退化 Ω 结点，并证明任意 Reg 字段层的
第一支／全部合法坐标均有保留派发证据。但 q=lim const0、x=suc q 均满足 Legal＋Reg，
Ωx 不满足 Reg。这份候选尚不能作为全层 Ω 闭合的正则层号类型，
所以未交全塔／Λ、完整 γ 种子与 (InvDS＋Reg) 的全层保持。
不否定其它 Reg 形状或乙路线。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRound10 where

import OCF.Align.YiRegBase
import OCF.Align.YiRegCover
import OCF.Align.YiRegZeroLimit
import OCF.Align.YiRegInstances as I

-- 仅在入口核对已有实际历史名字；下列四个数学模块均无记号依赖。
open import Data.List.Relation.Unary.All using (All)
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiRegBase using (Reg)
import OCF.Align.YiGammaSeed as H

actual-env-reg : All (λ x → Reg (Y.tree x)) H.Enew
actual-env-reg = I.known-env-reg
```

## Reg 的定义、旧反例与传递

[YiRegBase](YiRegBase.lagda.md)冻结如下候选，不改旧 Legal 或树：

```text
Reg 0 = ⊤
Reg (suc x) = Reg x
Reg (lim f) = ∀n Reg(f n)
Reg (lc k c t g) =
  Below(suc k,lc k c t g) × Reg k × Reg t × ∀ηe Reg(g η e)
```

最后的 ηe 仍带原 Gd。它保存单个方向的位置证据，不判定裸坐标，
不比较两个宽位置，也不把原始树补成记号码。Reg 与 Legal 独立，使用时取两者。
no-old-counter 直接用第九轮 no-below-j 排除 Reg(j)。
edge-reg／below-reg 证明沿真实子树传递 Reg；定义、排反例和向下传递均已通过。

reg-fields 给一项关键结论：Reg 树的每个字段 k 都有 Below(suc k,该树)。
遇到 lc.k 的内部字段时，先用当前 Reg 给出的界，再经 k→suc k 接入，
没有把字段标注本身冒称下界。

## 第4条：任意层的保留覆盖

[YiRegCover](YiRegCover.lagda.md)的主定理是：

```text
all-retained-reg : (i j : Level) → Reg(tree j) →
  (ev : DispEv(tree i,tree j)) → choice ev = keep → RetainedDomain(tree i,j)
```

它比本轮要求更强：目标只需原 Level 合法性，不再额外要求 Reg i。
不是目标 Ω 专属或有限测试；字段层与合法坐标的层均不受限。
RetainedDomain 仍是先前充分覆盖合同，包含第一支及所有原合法坐标里的 Field。

证明有两步：

1. kept-under 从已有判定型 keep 或结构型 keep，提取 j 到 i 的真路径。
   bounded 的 eq 行仍能用 j→suc j 接入，不要求再对宽位置比较。
2. omega-cover／up-cover／upK-cover 互递归，upN-cover 沿原 Pre 槽位递归。
   每一步都带 Reg y 及已有 Below(y,i)，给出 Ωy／读回树全部字段到 i 的路径。
   lc 根使用 Reg 的显式 bound，index、first、branch 使用相应子树 Reg。

up-cover 的内部结论可加强到任意 Raw 值，但每次都带固定正则层及字面目标路径；
它不是对裸坐标之间的律。RetainedDomain 中仍只有原 Gd 合法坐标会被调用。
新证据由结构递归直接给出，保留调用始终返回 structural，
实际需要判定的调用仍由原 InvD／bounded 负责。

**这只证明派发覆盖，不证明读回树自身 Reg。** 两者不能混为一个保持定理。

## 已实填的非空实例与未完成的可满足性义务

[YiRegInstances](YiRegInstances.lagda.md)给：

- nat-reg、ω-reg、Ω-reg 及 above-Ω-reg：有限层、标准ω、Ω和Ω+2均满足候选 Reg。
- retained-above-Ω：目标 Ω+2、字段层 Ω 的保留覆盖，量化全部合法 Raw Ω 坐标。
  因而全层主定理有非 Small 字段层实例，不依赖虚假的前提。
- known-env-reg 与入口 actual-env-reg：第八轮完整新 Env 的 Ω、0、1及重复项均满足 Reg。
- 塔的0／1／2层 Reg。没有给全塔或 Reg Λ，也没有给第八轮 γ 种子 Ω_Ω 的 Reg，
  不称这些特定树不满足 Reg；本轮的反例不是它们。

通用“Reg x 则 Reg Ωx”已被下面反例否定，因此不能把未实填的全塔／种子合同
当作可满足性结果。没有通过逐站补低层闭项来替代全层要求。

## 卡点：新的退化 ℕ 极限

[YiRegZeroLimit](YiRegZeroLimit.lagda.md)给编译过的反例：

```text
q = lim(λn → 0)
x = suc q
Ωx = lc q top (lim(λn → 1)) (ληe → up q η)
```

q-legal／x-legal 与 q-reg／x-reg 全部实填，Ωx 仍由旧定理保证 Legal。
原分支域也非空（top-guard）。但 no-root-bound 排除 Below(x,Ωx)，
故 no-reg-omega-x 与 no-omega-preservation 否定这份候选的全域 Ω 保持。

原因可精确定位：Pre q 没有槽位；在 Raw q 中 top 没有真前驱。
若合法 raw 极限的一支包含 top，则其它支与 top 在同一个合法窄界下用原 cmpC 比较，
top-back／top-at-zero／top-forward 推出所有支仍包含 top。
所以 guarded Raw q 坐标只能由 top、后继、极限生成（TopBuilt），
读回以 Ωq=lim const1 为底。看极限第0支即可排除 q 或 x 在其读回中出现，
不需要函数外延或在宽界下比较。

nonroot-reg 还实填 Ωx 除根 Below 以外的全部 Reg 条件：
Reg q、Reg Ωq、全部合法分支读回的 Reg 都成立，且那些读回均 Small。
所以不是又在未检查的分支里塞了一个坏 Ω 子树。
新退化形状是**常零 ℕ 极限**；候选在 lim 行只逐支递归，未排除它。
这里没有做 LF 序数值解释，不把“退化”写成已证明的序数值0。

本反例还给 no-reg-raw-feedback 与 no-reg-seed-x：在合法 Reg 层 x，
合法 top 读回／既有结构种子算法都输出这个非 Reg 的 Ωx。
这说明原 Gd／Legal／Reg 不足以自动保证一般读回或种子保持，
不是一个已构造的实际 ψ／γ 输出反例，也不否定只在更小生成域上的保持。

## 编译错误原文

单6G实验尝试用通过原守卫的 top 后继给 Ωx 根的位置：

```text
attempt : Below Z.x (V.Ω̂ Z.x)
attempt = one (e-branch (G.suc G.top) (inj₂ (inj₁ refl) , tt))
```

退出42；以下仅替换实验目录路径：

```text
<实验目录>/OmegaRegAttempt.agda:15.16-62: error: [UnequalTerms]
F.suc F.zero != F.zero of type F.LF
when checking that the expression
e-branch (G.suc G.top) (inj₂ (inj₁ refl) , tt) has type
Edge Z.x (V.Ω̂ Z.x)
```

该坐标读回 suc(Ωq)，不是需要的 suc q；常值1与常值0在这里直接不等。
这次路径构造失败之外，no-root-bound 才排除了所有其它合法支或第一支的路径。
失败轮没有生成或使用 HTML／切片。

## 本轮停在哪里，翻译账

定义合法、旧反例已排、位置传递已过，第4条全层分派已证。
停在候选正则性对 Ω 的闭包；由此没有进入第5条的完整 γ／回灌与 InvDS＋Reg 保持。
不采用函数外延，不增加裸坐标律，不比较宽位置，不构造固定层回收器，
也未实例化五堵墙的完整接口。这里是候选形状的保持失败，不是正性或宇宙层级错误。

Reg 的 bound 字段由编译否定 no-next-ev 指出的“派发量在节点下没有位置”缺口逼出，
形状只读树的路径与构造子，没有读取或按记号规则分情况；它没有新增记号启发字段。
原折叠的保留模板仍来自既定脚手架，本轮没有展开 ψ 或改其规则。
保持否定来自新的常零极限，未修改旧 Legal 或专门排除这一闭项来冒称闭包已经成立。
以后若修订正则性，须另证可满足性与生成闭包，不能把本候选的否定扩大为所有 Reg 不可能。
P1仍 x=Ω·ω²，没有新值界或 FGH。

从仓库根正式编译，单路6G：

```sh
agda --library-file=<库文件> -i src -i probes probes/OCF/Align/YiRound10.lagda.md +RTS -M6G -RTS
```

四件数学模块及入口共五件逐件删除各自字面接口冷编退出0；禁用构造0。
数学模块的源码／编译器闭包及关键定义切片无记号或C线依赖；
入口仅为实际 Env 名字核对而明读已有第4层模块，不误报入口闭包干净。
独立否定路的结果经主路读全文、删接口冷编复核；详细日志与审计见 LOG。
