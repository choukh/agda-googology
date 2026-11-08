# 规范层同构的原kind限制计算

原res/res⁻在同一B两份合法证上沿原kind计算；代表元、实际路径、
坐标back函数一起保留，不仅给代表元层的同构。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedProofRestrict where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedProofIf

rank-shape : ∀ B l₁ l₂ κ → rank B l₁ κ L.≅ᴵ rank B l₂ κ
rank-shape hz l₁ l₂ ()
rank-shape (hs B) l₁ l₂ (inj₁ κ) = rank-shape B l₁ l₂ κ
rank-shape (hs B) l₁ l₂ (inj₂ _) = proof-shape B l₁ l₂
rank-shape (hl f) l₁ l₂ (n , κ) = rank-shape (f n) (proj₂ l₁ n) (proj₂ l₂ n) κ
rank-shape (hΩ () f) l₁ l₂ κ

restrict-back : ∀ B l₁ l₂ κ →
  L.res⁻ (bound B l₂ κ) (proof-shape B l₁ l₂) ≡
  L.restr (L.≅ᴵ-sym (rank-shape B l₁ l₂ κ)) (bound B l₁ κ)
    (L.tr (rank-shape B l₁ l₂ κ))
restrict-back hz l₁ l₂ ()
restrict-back (hs B) l₁ l₂ (inj₁ κ) rewrite restrict-back B l₁ l₂ κ = refl
restrict-back (hs B) l₁ l₂ (inj₂ _) = refl
restrict-back (hl f) l₁ l₂ (n , κ)
  rewrite restrict-back (f n) (proj₂ l₁ n) (proj₂ l₂ n) κ = refl
restrict-back (hΩ () f) l₁ l₂ κ

restrict-forward : ∀ B l₁ l₂ κ →
  L.res (bound B l₁ κ) (proof-shape B l₁ l₂) ≡
  L.restr (rank-shape B l₁ l₂ κ) (bound B l₂ κ)
    (L.tr⁻ (rank-shape B l₁ l₂ κ))
restrict-forward hz l₁ l₂ ()
restrict-forward (hs B) l₁ l₂ (inj₁ κ) rewrite restrict-forward B l₁ l₂ κ = refl
restrict-forward (hs B) l₁ l₂ (inj₂ _) = refl
restrict-forward (hl f) l₁ l₂ (n , κ)
  rewrite restrict-forward (f n) (proj₂ l₁ n) (proj₂ l₂ n) κ = refl
restrict-forward (hΩ () f) l₁ l₂ κ
```
