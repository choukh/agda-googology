# 可数读回的最小实例与第 1 项
验收文件，读记号；有限形状检查覆盖 d = zero、suc zero；one-all 为任意 d 的第 1 项关系。
来源：有限证明复用 YiBVSmall.at-three 与 YiTBFam.Self.PF/liftC/liftU；上行复用 YiKCFin。
这给读回域和后继前提的可满足实例，不是一般 m1 证明，不代替 BranchNeed。
入口：at-zero、at-one、one-all；一般未填步骤在 YiQLRead.Step。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQLCheck where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiQLRead as Q
import OCF.Lean.YiKCFin as Fin
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiANFam as AF
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiRBFam as RF
import OCF.Lean.YiCLLow as L
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiBVDomain as D
import OCF.Align.EboLeanDef as E
zero-shape : S.child B.zero ≡ H.fn 3
zero-shape = refl
one-shape : S.child (B.suc B.zero) ≡ H.fn 4
one-shape = refl
zero-reference : E.fsT D.slot [] ≡ S.small-index
zero-reference = refl
one-reference : E.fsT D.slot (E.natT 1) ≡ AF.ψᴺ 1 (AF.Ωᴺ 1)
one-reference = refl
at-zero : ∀ o r → TF.SΩ (E.fsT D.slot []) 3 1 o r (P.inu (λ _ → P.inc tt P.self))
at-zero = S.at-three
at-one : ∀ o r → TF.SΩ (E.fsT D.slot (E.natT 1)) 4 1 o r
  (P.inu (λ _ → P.inu (λ _ → P.inc tt P.self)))
at-one o r = TF.liftU o r (P.inu (λ _ → P.inc tt P.self))
  (TF.liftU (proj₂ o tt) (proj₂ r tt) (P.inc tt P.self)
    (TF.liftC (proj₂ (proj₂ o tt) tt) (proj₂ (proj₂ r tt) tt) P.self
      (λ base beta ok hb → TF.Self.PF 0 (proj₂ (proj₂ (proj₂ o tt) tt) tt) (proj₂ (proj₂ (proj₂ r tt) tt) tt) base beta hb (H.Mβ 0))))
domain-zero : K.M⁰ [] B.zero
domain-zero = K.mz
domain-one : K.M⁰ (E.natT 1) (B.suc B.zero)
domain-one = K.m1 refl K.mz
one-all : ∀ {d} → K.M⁰ (E.natT 1) d → Q.Need (E.natT 1) d
one-all m = lift (Fin.suc-⊴ (Fin.pos1 m refl))
  where
  lift : ∀ {d} → K._⊴_ (B.suc B.zero) d → Q.Need (E.natT 1) d
  lift K.⊴r = at-one
  lift (K.⊴◃ e) = Q.weak (E.natT 1) e at-one
step-at-one : ∀ d → Q.Need [] d → Q.Need (E.natT 1) (B.suc d)
step-at-one d ih = one-all (K.m1 refl K.mz)
```
