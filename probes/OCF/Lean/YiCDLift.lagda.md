# 规范读回域上的后继归约

验收文件；编译条件定理。StepSᶜ 只在 Canon 上量化，推出域上的 Lift₁ᶜ，未实填一般 StepSᶜ。
来源：YiLTLift.liftQ、Red.lift-red；增加前驱与第一位置下行的域证据，不重证原保持引理。
原 ωᶜ、其后继与字面自然数在域内；是否够接龙骨另核。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCDLift where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Ωt)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiRBCrit using (h₁)
open import OCF.Lean.YiHCRel using (M⁰; mz; m1; mL; mΩ; mU; mw; mc)
open import OCF.Lean.YiANFam using (ψᴺ)
open import OCF.Lean.YiMENote using (cofψω; fsnψω)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiLTLift using (Q; Qz; QL; Qc; up◃; cofΩω; fsnΩω; Ωt≤; StepS; module Red; step-fin)
open import OCF.Lean.YiLTKid using (ℓ¹; module Sem)
open import OCF.Lean.YiCDCanon
import OCF.Align.EboLeanDef as E
open E using (cof; c1; pred; natT; fsn)
import OCF.Lean.YiCLFam as CF
open import OCF.Lean.YiCLCrit using (ωᶜ)

fin-CF : ∀ n → Fin (CF.nat n)
fin-CF zero = fz
fin-CF (suc n) = fs (fin-CF n)

ω-in : Canon ωᶜ
ω-in = cl fin-CF

sω-in : Canon (suc ωᶜ)
sω-in = cs ω-in

StepSᶜ : Set
StepSᶜ = ∀ {η x} → Canon x → cof η ≡ c1 → M⁰ (pred η) x
       → Q (ψᴺ 0 (E.Ωt (pred η))) (h₁ x)
       → Q (ψᴺ 0 (E.Ωt η)) (h₁ (suc x))

restriction : StepS → StepSᶜ
restriction st _ = st

liftQᶜ : StepSᶜ → ∀ {η c} → Canon c → M⁰ η c → Q (ψᴺ 0 (E.Ωt η)) (h₁ c)
liftQᶜ st cc (mz {x = c}) = Qz c
liftQᶜ st cc (m1 e m) = st (suc-inv cc) e m (liftQᶜ st (suc-inv cc) m)
liftQᶜ st {c = c} cc (mL {t = η} e h) =
  QL (cofψω (natT 0) (E.Ωt η) (cofΩω η e))
    (λ k → subst (λ z → Q z (h₁ c))
      (sym (trans (fsnψω (natT 0) (E.Ωt η) k (cofΩω η e))
        (cong (ψᴺ 0) (fsnΩω η k e)))) (liftQᶜ st cc (h k)))
liftQᶜ st cc (mΩ {p = ()} _ _ _)
liftQᶜ st cc (mU {c = ()} _ _)
liftQᶜ st cc (mw m d) = up◃ d (liftQᶜ st (below cc d) m)
liftQᶜ st cc (mc le m) = Qc (app≤ 0 [] (Ωt≤ le)) (liftQᶜ st cc m)

module Restricted (r : Rb ℓ¹) where
  open Sem r
  Lift₁ᶜ : Set
  Lift₁ᶜ = ∀ {η c} → Canon c → M⁰ η c → Kdˢ c (E.Ωt η) (proj₁ (Ωt (h₁ c)))

  lift-redᶜ : StepSᶜ → Lift₁ᶜ
  lift-redᶜ st cc m = Red.Q→Kd r (liftQᶜ st cc m)

step-finite : ∀ n → Q (ψᴺ 0 (E.Ωt (natT (suc n)))) (h₁ (suc (CF.nat n)))
step-finite = step-fin
```
