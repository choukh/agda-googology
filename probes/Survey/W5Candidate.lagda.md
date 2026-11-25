# W5：W4 折叠的一份候选改写（并行候选，不替换 W4）

前三层的候选，作者 2026-11-25 同意另开文件；值上没有新定理。块与树的原运算不变（`W4Block`、`W4Ops` 共用），改的只是 Ω 形层号上 "朝某个孩子里的层折" 的几行，依据是层号是值、不同孩子里的同一层只差路径，所以不比较孩子。可数层号定理与 BTBO 下界在候选上原样成立（`lower₅`、`btbo-lower₅`）；它是否高于 W4、是否达到 EBO 没有定理。模块原件是留档附件，用 `scripts/w5cand/materialize.py` 抄成实验目录再编译，原 W4 的链与候选的链并存。[审计 §9 至 §13](W4-EBO-独立审计-Fable52.md) · [保留判定的回报](Reports-2026-11-24/KKp-保留判定里的有限层.md) · [定位的两条定理](Reports-2026-11-24/KLp-有限层完全定位器.md)、[否定](Reports-2026-11-24/KLn-完全定位推出LPO.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W5Candidate where

open import Data.Product using (proj₁)
open import W4Block
open import W4Ops using (Tr⁺; Ωt)
import W4Fold
import WVOne
open import W5Path using (Ok)
open import W5Fold using (Base; ψ; EBOᶜ)
open import W5VOne using (read; 𝟏)
import OCF.Align.Level as LV
open import OCF.Align.Value using (_≼_)
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Lean.YiAbsObs using (LPO)
open import K5Mir using (IsS; IsS→IsN; code)
open import K5LowIface using (Cov)
import K5Low
import K5Btbo
import KBtbo
import KLoc
import KLnNeg
import K5Loc
import K5KpLoc
import W5Loc
```

与 W4 的四处差别（差异文件在审计 §9.7、§10.2、§11.3 与保留判定的回报里）：

1. 证书多带一条可选路径：Ω 形层号的孩子 zero 的层号到每个孩子。塔的证书给出它。孩子 zero 里的树（低塔的内容）朝别的孩子里的层折时，经这条路径嵌进目标孩子再折。
2. 朝别的孩子里的**有限层**折时，在树自己的孩子里找到那一层就地折（定位器 `W5Loc.loc`，可靠由类型保证）。
3. 保留判定：目标层与槽位层都是有限层且槽位层更低时保留，其余仍走链。
4. 仍要回退时，尾巴带着左项的语境折，不从头折。

值定理在候选上原样成立；原 W4 的那条并列在后。

```agda
lower₅ : (m : L) (st : IsS m) (o : Ok m) (S : Base m) → Cov S
       → (β : Tr⁺ zero) → 𝟏 ≼ read (proj₁ β) → (w : zero ≤ m)
       → LV.ψ⁰ (LV.Ω (code m (IsS→IsN m st) o)) ≼ read (proj₁ (ψ m o S zero w β (proj₁ (Ωt m))))
lower₅ = K5Low.lowerW

btbo-lower₅ : tr₀ Ord-Ord.BTBO ≼ read EBOᶜ
btbo-lower₅ = K5Btbo.btbo-lower

btbo-lower₄ : tr₀ Ord-Ord.BTBO ≼ WVOne.read W4Fold.EBOᶜ
btbo-lower₄ = KBtbo.btbo-lower
```

定位的界线是两条定理：有限层上候选的定位器完全；对无穷层完全的定位器推出 LPO（后一条对任何定位器，陈述在原 W4 的名字空间里）。

```agda
loc-complete : K5Loc.CompleteFin W5Loc.loc
loc-complete = K5KpLoc.cFin

loc-wall : KLoc.NegStmt
loc-wall = KLnNeg.neg
```

形状事实（都是 `refl`，在各自的模块里）：`W5Exp4Shape.branch-1`、`branch-2`、`branch-3`（"右边接上 Ω_Ω" 朝孩子 1 里的第 1 层，结点在下标 1、2、3 处的分支是就地的折叠，不是尾巴）；`K5KpShape.kp-keep`、`kp-chain`（孩子位置上槽位层为第 1 层的结点，朝别的孩子里的第 2 层保留，朝第 1 层走链）；`W5Trace.βQ-shape`（真实运行里第一处损失处的条目是两层挂起的乘幂）。

范围。候选与 W4 逐行不可比（判断，审计 §14）：W4 的回退行把孩子里的树整个折到第 0 层作尾巴，候选只取它朝目标层的折叠，后者再折到第 0 层可以更小；所以没有、也不指望有 "候选不低于 W4" 的定理，两个闭项谁大不知道。另外没有证的：无穷的私有层上仍然回退；Ω 形层号的保留判定与参照一侧的一致性没有定理（可数层号上有）。按孩子下标是不是构造子 zero 分情况，与 `obs→dec` 一族的前提对照过陈述，没有另写实例。翻译账：改动的理由都来自树侧，不读记号；它们是第四层的审计逼出的前三层候选，单列在 LOG。
