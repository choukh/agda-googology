# 小例的末端链检查
验收文件；固定输入三个后继的 Ψ、对应分支折叠均有 ψ₀(Ω₃) 下界。
实例实际填入 reflect-at 的值序与全 HC 前提；不填 two 对象的 ChildBound 或 NΨ。
来源：YiTVSmallAccept 的有限层出口，有限层实例取 YiUTTwoLocal.zero-rel 的 n=2、j=0。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTMSmallAccept where
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTVPsi as Q
import OCF.Lean.YiTCValue as C
import OCF.Lean.YiTMSmall as S
import OCF.Lean.YiTMAccept as A
open import OCF.Lean.YiTVRead
import OCF.Lean.YiTBFam as LF
import OCF.Lean.YiRBFam as RF
import OCF.Lean.YiCLLow as CL
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiUTTwoLocal as U
import OCF.Align.Level as L
import OCF.Align.Value as W

relation : K.M⁰ U.small (proj₁ (C.collapseᵛ B.zero (P.Ok-tw 0) S.v S.hv))
relation = LF.sΩ-LF {n = 2} {j = 0} (proj₂ (P.Ok-tw 1) S.c) (MT.rbᶻ (Q.Finite.h S.c))
  (RF.tu (RF.pu (RF.pu (RF.can CL.s0)))) (F.B₀ (Q.Finite.h S.c)) (O.Ωt B.zero)
  (λ i u → K.⊴r) (K.m1 refl K.mz)
small-NΨ : (h : SI.E.HC U.small) → SI.E.tree h W.≼ readV (Q.Ψ B.zero (P.Ok-tw 0) S.v S.hv)
small-NΨ h = W.≼-trans (XI.tree-back h)
  (W.≼-trans (K.lower⁰ relation (XI.back h))
    (W.≅→≼ (L.≅-sym (read-val (proj₁ (C.collapseᵛ B.zero (P.Ok-tw 0) S.v S.hv))))))
small-result : K.M⁰ U.small (proj₁ (Q.Finite.fold S.c))
small-result = A.reflect-at (XI.back U.small-hc) (Q.Ψ B.zero (P.Ok-tw 0) S.v S.hv)
  (proj₁ (Q.Finite.fold S.c)) S.small small-NΨ
```
