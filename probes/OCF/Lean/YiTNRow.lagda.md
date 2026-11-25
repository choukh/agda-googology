# 实际孩子族的后继层出口
不读记号；编译定理：剥去孩子根后继后的 Ω 折叠值不高于该孩子的折叠值。
只处理 YiTZLocal.child；不提供 ChainAdvance 1。
来源：YiTQSmall.one-two 的同层 mono 与第 1 累计支证明，变量化后复用。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTNRow where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTMInner as I
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTYLocal as Y
-- 只在本路实际孩子族上剥去根后继；不求一般跨层单调。
shift : B.Tr B.zero → B.L
shift d = T.two B.⊕ (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero d))
module At (d : B.Tr B.zero) (o : P.Ok (T.child d)) (w : P._≤_ B.zero (shift d)) where
  a = shift d
  oa = proj₂ o tt
  ra = MT.rbᶻ a
  bs = F.B₀ a
  β = O.Ωt B.zero
  fold = TB.ψ a oa ra bs B.zero w β
  low = fold (proj₁ (O.Ωt a))
  high₀ = fold (B.suc B.zero)
  high₁ = fold (B.suc (proj₁ (O.next⁺ (O.Ωt a))))
  high = TB.ψ (T.child d) o (MT.rbᶻ (T.child d)) (F.B₀ (T.child d))
    B.zero (P.inu (λ _ → w)) β (proj₁ (O.Ωt (T.child d)))
  predecessor-low : V.val B.zero (proj₁ low) V.≼ V.val B.zero (proj₁ high)
  predecessor-low = V.≼l 1 (V.≼-trans
    (V.◁→≼ (V.val-mono B.zero (TB.mono a oa ra bs B.zero w β
      {x = proj₁ (O.Ωt a)}
      {y = B.suc (proj₁ (O.next⁺ (O.Ωt a)))}
      (B.◃t (B.◃l 0) B.◃s))))
    (V.≼-trans (I.right-⊹ (V.val B.zero (proj₁ high₀)) (V.val B.zero (proj₁ high₁)))
      (proj₂ (V.val-+ (proj₁ high₀) (proj₁ high₁)))))
module Actual (d : B.Tr B.zero) where
  module A = At d (T.o-child d) (P.self P.∙ P.z≤ (shift d))
  opaque
    unfolding Y.Canonical.target-fold
    target-eq : proj₁ A.high ≡ Y.Canonical.target-fold d
    target-eq = refl

  low-to-feed : V.val B.zero (proj₁ A.low) V.≼ V.val B.zero (T.Canonical.Target.feed d)
  low-to-feed = subst (λ x → V.val B.zero (proj₁ A.low) V.≼ V.val B.zero x)
    (sym (Y.Canonical.target-feed d))
    (subst (λ x → V.val B.zero (proj₁ A.low) V.≼ V.val B.zero x)
      target-eq A.predecessor-low)
```
