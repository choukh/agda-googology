# 塔第 2 项折到第 0 层的保持
> 验收文件（读记号）。编译定理，条件为孩子接口 `Kid₂` 与底 `GB²`；两条路径取一致路径或经下标层。
> 来源：推导归纳的其余行照 `YiLTKid.Top.Fold.LF¹`；回灌链用 `feedΩ`，只需下标层输出不低于底。
> 不填读回孩子的 `Lift₂`；不改任何树侧定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKQFold where
open import OCF.Lean.YiKQRel
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω)
open import OCF.Lean.YiANFam using (cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; node⁺; kp)
open import OCF.Lean.YiRBFam using (OKB)
open import OCF.Lean.YiTBRow using (ψ; mono)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (M⁰; mz; mL; m1; mΩ; mU; mw; mc; module G⁰)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiANFam using (ψᴺ)
import OCF.Lean.YiLTKid as One

γΩ≤ : ∀ a k → E.Ωt (E.γT a [] k) ≤ᵀ One.ΩΩ
γΩ≤ a zero = inj₁ (E.hd< (E.lv< (E.hd< (E.lv< E.[]<))))
γΩ≤ a (suc k) = inj₁ (E.hd< (E.lv< (E.hd< (E.lv< E.[]<))))

module Fold (K : Kid₂) (B : Base ℓ²) (gb : Top.GB² K B) where
  open Top K
  F : zero ≤ ℓ² → Tr⁺ zero → Tr ℓ² → Tr⁺ zero
  F w β x = ψ ℓ² o² r² B zero w β x

  F¹ : Tr ℓ² → Tr (tw 1)
  F¹ x = proj₁ (ψ ℓ² o² r² B (tw 1) (ink self) (B (tw 1) (ink self)) x)

  feed : (Tr (tw 1) → Tr ℓ²) → Tr (tw 1) → Tr (tw 1)
  feed g c = F¹ (g c)

  feedΩ : ∀ a k x → A.M¹ (E.Ωt (E.γT a [] k)) (F¹ x)
  feedΩ a k x = mc (γΩ≤ a k)
    (G¹.m⊴ (bK gb) (ψ-⊵ ℓ² o² r² B (tw 1) (ink self) (B (tw 1) (ink self)) x))

  chain : ∀ a (g : Tr (tw 1) → Tr ℓ²) k
        → A.M¹ (E.Ωt (E.γT a [] k)) (iter (feed g) zero (suc k))
  chain a g k = feedΩ a k (g (iter (feed g) zero k))

  Fz : ∀ w (β : Tr⁺ zero) → M⁰ (ψᴺ 0 []) (proj₁ β)
     → ∀ x → M⁰ (ψᴺ 0 []) (proj₁ (F w β x))
  Fz w β hβ x = G⁰.m-zl (λ y → proj₁ (F w β y)) (mono ℓ² o² r² B zero w β) hβ x

  gbx : ∀ x c → OKB (λ i u → ψ ℓ² o² r² B i (inc c u) (B i (inc c u)) x)
  gbx x c i u = ⊴-trans (bC gb c i u) (ψ-⊵ ℓ² o² r² B i (inc c u) (B i (inc c u)) x)

  isz : ∀ {a x} (m : M² a x) → IsZ m → a ≡ []
  isz mz _ = refl
  isz (m1 _ _) ()
  isz (mL _ _) ()
  isz (mΩ _ _ _) ()
  isz (mU _ _) ()
  isz (mw _ _) ()
  isz (mc _ _) ()

  LFU : ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 []) (proj₁ β)
      → ∀ {s} (x : Tr ℓ²) (c : Tr (tw 1)) (y : Tr (h₂ c)) (ey : h₂ c ⊢ zero ◃ y)
      → Kd c s y → M⁰ (ψᴺ 0 s) (proj₁ (F w β (up x c y ey)))
  LFU wu β hβ x c y ey ch = foldᶜ c (z≤ (h₂ c)) (inj₁ refl) _ (gbx x c) (F _ β x) (Fz _ β hβ x) ch
  LFU wi β hβ x c y ey ch = foldᶜ c (z≤ (tw 1) ∙ proj₂ (proj₁ o²) c) (inj₂ refl) _ (gbx x c) (F _ β x) (Fz _ β hβ x) ch

  LF² : ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 []) (proj₁ β)
      → ∀ {a x} (m : M² a x) → Sp m → M⁰ (ψᴺ 0 a) (proj₁ (F w β x))
  LF² {w} pw β hβ (mz {x = x}) sp = Fz w β hβ x
  LF² {w} pw β hβ (m1 {t = a} {x = x} e h) sp =
    G⁰.m-next (F w β x) (cofψ1 [] a e) (λ k → fsnψ1 [] a k e) (LF² pw β hβ h sp)
  LF² {w} pw β hβ (mL {t = a} {x = x} e h) sp =
    mL (cofψω [] a e) (λ k → subst (λ z → M⁰ z (proj₁ (F w β x)))
      (sym (fsnψω [] a k e)) (LF² pw β hβ (h k) (sp k)))
  LF² {w} pw β hβ (mΩ {t = a} {p = inj₁ (inj₁ tt)} {g = g} e refl h) sp =
    node0 pw β g (mL (cofG [] a refl e)
      (λ k → subst (λ z → M⁰ z (proj₁ (limc⁺ (λ k′ → F w β (g (iter (feed g) zero k′))))))
        (sym (fsnG [] a k refl e))
        (G⁰.m-cum (λ k′ → F w β (g (iter (feed g) zero k′))) (suc k)
          (LF² pw β hβ (h (E.γT a [] k) (iter (feed g) zero (suc k)) (chain a g k))
            (sp (E.γT a [] k) (iter (feed g) zero (suc k)) (chain a g k))))))
    where
    node0 : ∀ {w} → Pw w → (β : Tr⁺ zero) (g : Tr (tw 1) → Tr ℓ²)
      → M⁰ (ψᴺ 0 a) (proj₁ (limc⁺ (λ k → F w β (g (iter (feed g) zero k)))))
      → M⁰ (ψᴺ 0 a) (proj₁ (F w β (Ω (inj₁ (inj₁ tt)) g)))
    node0 wu β g q = q
    node0 wi β g q = q
  LF² pw β hβ (mΩ {p = inj₁ (inj₂ p)} _ () _) sp
  LF² pw β hβ (mΩ {p = inj₂ _} _ () _) sp
  LF² {w} pw β hβ (mU {s = s} {x = x} {c = c} {y = y} {e = ey} m ch) sp =
    subst (λ z → M⁰ (ψᴺ 0 (z ++ s)) (proj₁ (F w β (up x c y ey)))) (sym (isz m sp))
      (LFU pw β hβ x c y ey ch)
  LF² {w} pw β hβ (mw m d) sp = mw (LF² pw β hβ m sp) (mono ℓ² o² r² B zero w β d)
  LF² pw β hβ (mc le m) sp = mc (app≤ 0 [] le) (LF² pw β hβ m sp)
```
