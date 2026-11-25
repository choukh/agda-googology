# 前驱闭包域上的后继归约

验收文件；编译条件定理。StepSᴾ 在 Pre 上量化，推出同域上的 Lift₁ᴾ；完整 StepSᴾ 未实填。
来源：YiCDLift.liftQᶜ 与 lift-redᶜ 的证明换入 YiPCDom 的向下闭包；原保持引理直接复用。
有限后继结论沿用 YiLTLift.step-fin；本文件不声称提高主线的无条件强度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPCLift where
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
open import OCF.Lean.YiPCDom
import OCF.Align.EboLeanDef as E
open E using (cof; c1; pred; natT; fsn)
import OCF.Lean.YiCLFam as CF


StepSᴾ : Set
StepSᴾ = ∀ {η x} → Pre x → cof η ≡ c1 → M⁰ (pred η) x
       → Q (ψᴺ 0 (E.Ωt (pred η))) (h₁ x)
       → Q (ψᴺ 0 (E.Ωt η)) (h₁ (suc x))

restriction : StepS → StepSᴾ
restriction st _ = st

liftQᴾ : StepSᴾ → ∀ {η c} → Pre c → M⁰ η c → Q (ψᴺ 0 (E.Ωt η)) (h₁ c)
liftQᴾ st cc (mz {x = c}) = Qz c
liftQᴾ st cc (m1 e m) = st (suc-inv cc) e m (liftQᴾ st (suc-inv cc) m)
liftQᴾ st {c = c} cc (mL {t = η} e h) =
  QL (cofψω (natT 0) (E.Ωt η) (cofΩω η e))
    (λ k → subst (λ z → Q z (h₁ c))
      (sym (trans (fsnψω (natT 0) (E.Ωt η) k (cofΩω η e))
        (cong (ψᴺ 0) (fsnΩω η k e)))) (liftQᴾ st cc (h k)))
liftQᴾ st cc (mΩ {p = ()} _ _ _)
liftQᴾ st cc (mU {c = ()} _ _)
liftQᴾ st cc (mw m d) = up◃ d (liftQᴾ st (below cc d) m)
liftQᴾ st cc (mc le m) = Qc (app≤ 0 [] (Ωt≤ le)) (liftQᴾ st cc m)

module Restricted (r : Rb ℓ¹) where
  open Sem r
  Lift₁ᴾ : Set
  Lift₁ᴾ = ∀ {η c} → Pre c → M⁰ η c → Kdˢ c (E.Ωt η) (proj₁ (Ωt (h₁ c)))

  lift-redᴾ : StepSᴾ → Lift₁ᴾ
  lift-redᴾ st cc m = Red.Q→Kd r (liftQᴾ st cc m)

step-finite : ∀ n → Q (ψᴺ 0 (E.Ωt (natT (suc n)))) (h₁ (suc (CF.nat n)))
step-finite = step-fin

step-zero : Pre zero → cof (natT 1) ≡ c1 → M⁰ (pred (natT 1)) zero
          → Q (ψᴺ 0 (E.Ωt (pred (natT 1)))) (h₁ zero)
          → Q (ψᴺ 0 (E.Ωt (natT 1))) (h₁ (suc zero))
step-zero _ _ _ _ = step-fin 0

step-zero-domain : Pre zero
step-zero-domain = idx0

step-zero-rel : M⁰ (pred (natT 1)) zero
step-zero-rel = mz

step-zero-ih : Q (ψᴺ 0 (E.Ωt (pred (natT 1)))) (h₁ zero)
step-zero-ih = Qz zero
```
