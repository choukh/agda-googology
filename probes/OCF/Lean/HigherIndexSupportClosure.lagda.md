# 支持证书随低界扩张、加法与后继嵌入闭合

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexSupportClosure where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.HigherIndexSupportIf

next-up : ∀ c κ β e (ad : Coord c κ β e) → β ⊲ next c κ β e ad
next-up hz (inj₁ _ , inj₁ ()) β e ad
next-up hz (inj₁ _ , inj₂ _) β e ad = hsuc (proj₁ ad)
next-up hz (inj₂ d , κ) β e ad = hself
next-up (hs c) (inj₁ κ) β e ad = next-up c κ β e ad
next-up (hs c) (inj₂ _) β e ad = proj₁ (proj₂ ad)
next-up (hl f) (n , κ) β e ad = next-up (f n) κ β e ad
next-up (hΩ (inj₁ ()) f) κ β e ad
next-up (hΩ (inj₂ _) f) (inj₁ _ , inj₁ ()) β e ad
next-up (hΩ (inj₂ _) f) (inj₁ _ , inj₂ _) β e ad = hsuc (proj₁ ad)
next-up (hΩ (inj₂ _) f) (inj₂ d , κ) β e ad = next-up (f d) κ β e ad

coord-down : ∀ c κ {β β′} → β ⊲ β′ → ∀ e (ad′ : Coord c κ β′ e) →
  Σ (Coord c κ β e) (λ ad → next c κ β e ad ⊲ next c κ β′ e ad′)
coord-down hz (inj₁ _ , inj₁ ()) q e ad
coord-down hz (inj₁ _ , inj₂ _) q e ad = (⊲ᴮ-tr q (proj₁ ad) , proj₂ ad) , hself
coord-down hz (inj₂ d , κ) q e ad = tt , q
coord-down (hs c) (inj₁ κ) q e ad = coord-down c κ q e ad
coord-down (hs c) (inj₂ _) q e (v , r , lv , s) = (v , ⊲ᴮ-tr q r , lv , s) , hself
coord-down (hl f) (n , κ) q e ad = coord-down (f n) κ q e ad
coord-down (hΩ (inj₁ ()) f) κ q e ad
coord-down (hΩ (inj₂ _) f) (inj₁ _ , inj₁ ()) q e ad
coord-down (hΩ (inj₂ _) f) (inj₁ _ , inj₂ _) q e ad = (⊲ᴮ-tr q (proj₁ ad) , proj₂ ad) , hself
coord-down (hΩ (inj₂ _) f) (inj₂ d , κ) q e ad = coord-down (f d) κ q e ad

event-up : ∀ c {β β′} → β ⊲ β′ → ∀ κ → Event c β κ → Event c β′ κ
event-up hz q (inj₁ _ , inj₁ ()) p
event-up hz q (inj₁ _ , inj₂ _) p = tt
event-up hz q (inj₂ d , κ) p = ⊲ᴮ-tr p q
event-up (hs c) q (inj₁ κ) p = event-up c q κ p
event-up (hs c) q (inj₂ _) p = tt
event-up (hl f) q (n , κ) p = event-up (f n) q κ p
event-up (hΩ (inj₁ ()) f) q κ p
event-up (hΩ (inj₂ _) f) q (inj₁ _ , inj₁ ()) p
event-up (hΩ (inj₂ _) f) q (inj₁ _ , inj₂ _) p = tt
event-up (hΩ (inj₂ _) f) q (inj₂ d , κ) (bd , p) = ⊲ᴮ-tr bd q , event-up (f d) q κ p

mono : ∀ c {β β′} → β ⊲ β′ → ∀ a → Support c β a → Support c β′ a
mono c q hz s = tt
mono c q (hs a) s = mono c q a s
mono c q (hl f) s = λ n → mono c q (f n) (s n)
mono c q (hΩ κ f) (ev , s) = event-up c q κ ev , λ e ad →
  mono c (proj₂ (coord-down c κ q e ad)) (f e) (s e (proj₁ (coord-down c κ q e ad)))

add : ∀ c β a b → Support c β a → Support c β b → Support c β (a ⊞ b)
add c β a hz sa sb = sa
add c β a (hs b) sa sb = add c β a b sa sb
add c β a (hl f) sa sb = λ n → add c β a (f n) sa (sb n)
add c β a (hΩ κ f) sa (ev , sb) = ev , λ e ad →
  add c (next c κ β e ad) a (f e) (mono c (next-up c κ β e ad) a sa) (sb e ad)

up-support : ∀ c β a → Support c β a → Support (hs c) β (up a)
up-support c β hz s = tt
up-support c β (hs a) s = up-support c β a s
up-support c β (hl f) s = λ n → up-support c β (f n) (s n)
up-support c β (hΩ κ f) (ev , s) = ev , λ e ad →
  up-support c (next c κ β e ad) (f e) (s e ad)
```
