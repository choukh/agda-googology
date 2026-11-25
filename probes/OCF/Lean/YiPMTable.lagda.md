# F2 比较表参数

参数化（工程），数学内容与 `YiVTFold` 的表和分情况相同；验收用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMTable where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold public using (Base; base; b⊥; n⊥; bs; ns; B₀; chB; kp; kp⁼; kp-ind; kp⁼-ind; Good; Good⁼)


Table : Set
Table = (k : L) (h : Tr k → L) (c c′ : Tr k) → Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))

empty : Table
empty k h c c′ = nothing

z≤ᶠ : (ℓ : L) → zero ≤ ℓ
z≤ᶠ zero     = self
z≤ᶠ (suc a)  = ins (z≤ᶠ a)
z≤ᶠ (lim g)  = inlu (λ n → z≤ᶠ (g n))
z≤ᶠ (Ωₗ k h) = inu (λ c → z≤ᶠ (h c))

loᶠ : (a b : L) → Maybe ((b ≤ a) ⊎ (a ≤ b))
loᶠ zero     b = just (inj₂ (z≤ᶠ b))
loᶠ (suc _)  b = nothing
loᶠ (lim _)  b = nothing
loᶠ (Ωₗ _ _) b = nothing

hiᶠ : (a b : L) → Maybe ((b ≤ a) ⊎ (a ≤ b))
hiᶠ a zero     = just (inj₁ (z≤ᶠ a))
hiᶠ a (suc _)  = nothing
hiᶠ a (lim _)  = nothing
hiᶠ a (Ωₗ _ _) = nothing

tbᶠ : (k : L) (h : Tr k → L) (c c′ : Tr k) → Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))
tbᶠ k h zero zero = just (inj₁ self)
tbᶠ k h zero c′   = loᶠ (h zero) (h c′)
tbᶠ k h c    zero = hiᶠ (h c) (h zero)
tbᶠ k h _    _    = nothing

tW : {A B X : Set} → Maybe (A ⊎ B) → (A → X) → (B → X) → X → X
tW (just (inj₁ a)) F G H = F a
tW (just (inj₂ b)) F G H = G b
tW nothing         F G H = H

tW-ind : {A B X : Set} (Q : X → Set) (m : Maybe (A ⊎ B)) {F : A → X} {G : B → X} {H : X}
       → ((a : A) → Q (F a)) → ((b : B) → Q (G b)) → Q H → Q (tW m F G H)
tW-ind Q (just (inj₁ a)) hF hG hH = hF a
tW-ind Q (just (inj₂ b)) hF hG hH = hG b
tW-ind Q nothing         hF hG hH = hH

tW-ind₂ : {A B X : Set} (Q : X → X → Set) (m : Maybe (A ⊎ B)) {F F′ : A → X} {G G′ : B → X} {H H′ : X}
        → ((a : A) → Q (F a) (F′ a)) → ((b : B) → Q (G b) (G′ b)) → Q H H′ → Q (tW m F G H) (tW m F′ G′ H′)
tW-ind₂ Q (just (inj₁ a)) hF hG hH = hF a
tW-ind₂ Q (just (inj₂ b)) hF hG hH = hG b
tW-ind₂ Q nothing         hF hG hH = hH
```
