# Lemma 4.38 (b)(c)：𝕎 ∩ I ≅ W(𝕎) ∩ I

接 [Gamma](Gamma.lagda.md)。(b)：x ∈ 𝒜^𝕎(𝕎) ∩ I ⟹ x ∈ 𝕎：x ≺ ψ_I 0 时 x ∈ W(𝕎)|ψ_I 0 ⊆ 𝕎；否则 x^{−Fi} = ψ_I b ∈ 𝕎（≺ x 时经 τ^𝕎(x)，= x 时用 (a)），ψ_I(b+1) ∈ 𝕎，x ∈ W(𝕎)|ψ_I(b+1) ⊆ 𝕎。(c) 由 (b) 对 W(𝕎) 归纳。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Gamma2 (F : OTFacts) where

open OTFacts F

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith
open import Mahlo.Inacc.BoolLemmas
open import Mahlo.Inacc.OTLemmas
open import Mahlo.Inacc.WO.K
open import Mahlo.Inacc.WO.Base
open import Mahlo.Inacc.WO.CLemmas
open import Mahlo.Inacc.WO.OrderLemmas F
open import Mahlo.Inacc.WO.Lemma47 F
open import Mahlo.Inacc.WO.Dist F
open import Mahlo.Inacc.WO.Closed F
open import Mahlo.Inacc.WO.Closed2 F
open import Mahlo.Inacc.WO.Union F
open import Mahlo.Inacc.WO.Lemma431 F
open import Mahlo.Inacc.WO.Gamma F

open import Level using (Level; 0ℓ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
```

## 2. Lemma 4.38 (b)(c)

```agda
-- (b) 𝒜^𝕎(𝕎) ∩ I ⊆ 𝕎
L4-38b : ∀ {x} → 𝒜 𝕎 𝕎 x → x ≺ I′ → 𝕎 x
L4-38b {x} a@(mx , τ⊆) x≺I with ≺-or-⪰ x ⟨ psi IR zer ⟩
... | inj₁ x≺ψ0 = ⊑← (proj₂ Ag𝕎) 𝕎-ψI0 (𝒲-intro (mx , λ t → 𝕎⊆𝒲𝕎 (τ⊆ t))) (≺⇒⪯ x≺ψ0)
... | inj₂ ψ0⪯x = fromForm (Fi-form ox ψ0⪯x x≺I)
  where
    ox : OT x
    ox = M⊆OT mx
    fromForm : (∃ λ b → OT ⟨ psi IR b ⟩ × mFi x ≡ ⟨ psi IR b ⟩ × pFi x ≡ ⟨ psi IR (b + one) ⟩
                        × x ≺ ⟨ psi IR (b + one) ⟩) → 𝕎 x
    fromForm (b , oψb , eM , eP , x≺ψb+1) =
      ⊑← (proj₂ Ag𝕎) (𝕎-ψI+1 (OT-ψIb+1 oψb) ψb∈𝕎) (𝒲-intro (mx , λ t → 𝕎⊆𝒲𝕎 (τ⊆ t))) (≺⇒⪯ x≺ψb+1)
      where
        -- x^{−Fi} ∈ C^x(𝕎)；x^{−Fi} ≺ x 时在 τ^𝕎(x) ⊆ 𝕎，否则 x^{−Fi} = x 用 (a)
        cψb : C x 𝕎 ⟨ psi IR b ⟩
        cψb = subst (C x 𝕎) eM (dc-mFi (CψDC ox) ox mx)
        ψb∈𝕎 : 𝕎 ⟨ psi IR b ⟩
        ψb∈𝕎 with ⪯⇒≺⊎≡ (subst (λ t → t ⪯ x) eM (mFi⪯ ox))
        ... | inj₁ ψb≺x = τ⊆ (cψb , ψb≺x)
        ... | inj₂ ψb≡x =
          Γ-block.L4-38a b oψb (λ t → τ⊆ (subst (λ y → τ 𝕎 y _) ψb≡x t)) (subst (M 𝕎) (sym ψb≡x) mx)

-- (c) 𝕎 ∩ I ≅ W(𝕎) ∩ I
L4-38c : ∀ {y} → 𝒲 𝕎 y → y ≺ I′ → 𝕎 y
L4-38c = 𝒲-ind {B = λ y → y ≺ I′ → 𝕎 y} step
  where
    step : (𝒜 𝕎 (λ y → y ≺ I′ → 𝕎 y) ∩ 𝒲 𝕎) ⊆ (λ y → y ≺ I′ → 𝕎 y)
    step ((my , ih) , w) y≺I = L4-38b (my , λ t → ih t (≺-trans (proj₂ t) y≺I)) y≺I

𝕎∩I≅ : (𝕎 ∩ ↓ I′) ≅ (𝒲 𝕎 ∩ ↓ I′)
𝕎∩I≅ = (λ (p , o , q) → 𝕎⊆𝒲𝕎 p , o , q) , (λ (w , o , q) → L4-38c w q , o , q)
```
