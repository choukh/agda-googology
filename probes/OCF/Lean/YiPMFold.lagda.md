# F2 折叠按比较表参数化

参数化（工程），数学内容与 `YiVTFold` 相同，仅把四处查询的表作参数；空表为原 F2 行，验收用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMFold where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
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

  open import OCF.Lean.YiPMTable public using (tW; tW-ind; tW-ind₂; z≤ᶠ; loᶠ; hiᶠ; tbᶠ)
  mutual
    ψ⊥ : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → Tr ℓ → Tr zero
    ψs : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → (j : L) → j ≤ ℓ → (β : Tr j) → j ⊢ zero ◃ β → Tr ℓ → Tr j
    nz⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (x : Tr ℓ) → zero ⊢ zero ◃ ψ⊥ ℓ ε ρ B x
    nzs : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
        → j ⊢ zero ◃ ψs ℓ ε ρ B j w β nβ x
    mono⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) {x y : Tr ℓ}
          → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε ρ B x ◃ ψ⊥ ℓ ε ρ B y
    monos : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) {x y : Tr ℓ}
          → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε ρ B j w β nβ x ◃ ψs ℓ ε ρ B j w β nβ y

    ψ⊥ ℓ ε ρ B zero      = b⊥ B
    ψ⊥ ℓ ε ρ B (suc x)   = next (ψ⊥ ℓ ε ρ B x) (nz⊥ ℓ ε ρ B x)
    ψ⊥ ℓ ε ρ B (lim f a) = lim (λ n → ψ⊥ ℓ ε ρ B (f n)) (λ n → mono⊥ ℓ ε ρ B (a n))
    ψ⊥ ℓ ε ρ B (Ω p g)   =
      limc (λ n → ψ⊥ ℓ ε ρ B (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n)))
           (λ n → nz⊥ ℓ ε ρ B (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n)))
    ψ⊥ (suc a) ε ρ B (up x _ y e) =
      ψ⊥ a ε ρ
        (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)) y
    ψ⊥ (lim g) ε (ρc , R) B (up x n y e) =
      ψ⊥ (g n) (ε n) (ρc n)
        (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x)) y
    ψ⊥ (Ωₗ k h) ε ρ B (up x c y e) =
      ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)) y
    ψ⊥ zero ε ρ B (up x () y e)

    ψs ℓ ε ρ B j w β nβ zero      = β
    ψs ℓ ε ρ B j w β nβ (suc x)   = next (ψs ℓ ε ρ B j w β nβ x) (nzs ℓ ε ρ B j w β nβ x)
    ψs ℓ ε ρ B j w β nβ (lim f a) = lim (λ n → ψs ℓ ε ρ B j w β nβ (f n)) (λ n → monos ℓ ε ρ B j w β nβ (a n))
    ψs ℓ ε ρ B j w β nβ (Ω p g)   =
      kp ℓ ε ρ p w (λ q cv → Ω q (λ z → ψs ℓ ε ρ B j w β nβ (g (cv z))))
        (limc (λ n → ψs ℓ ε ρ B j w β nβ (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n)))
              (λ n → nzs ℓ ε ρ B j w β nβ (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n))))
    ψs ℓ ε ρ B _ self β nβ (up x c y e) = Upc ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y
    ψs (suc a) ε ρ B j (ins w) β nβ (up x _ y e) =
      ψs a ε ρ
        (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x))
        j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) y
    ψs (lim g) ε (ρc , R) B j (inl n w) β nβ (up x m y e) =
      caseW (way g R m n)
        (λ v → ψs (g n) (ε n) (ρc n)
          (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
          j w (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (emb (g n) (ε n) v y e))
        (λ v → ψs (g m) (ε m) (ρc m)
          (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
          j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) y)
    ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ (up x m y e) =
      ψs (g m) (ε m) (ρc m)
        (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j (ws m) (ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) y
    ψs (Ωₗ k h) ε ρ B j (ink w) β nβ (up x c y e) =
      ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
        j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) y
    ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ (up x c y e) =
      ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
        j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) y
    ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e) =
      tW (tb k h c c′)
        (λ u → ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
          (chB B (λ u′ → inb c u′) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
            (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
          j (w ∙ u) (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) y)
        (λ u → ψs (h c′) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′)
          (chB B (λ u′ → inb c′ u′) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
            (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
          j w (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (emb (h c′) (proj₂ (proj₂ ε c′)) u y e))
        ((ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y))
    nz⊥ ℓ ε ρ B zero      = n⊥ B
    nz⊥ ℓ ε ρ B (suc x)   = ◃t (nz⊥ ℓ ε ρ B x) (◃l zero)
    nz⊥ ℓ ε ρ B (lim f a) = ◃t (nz⊥ ℓ ε ρ B (f zero)) (◃l zero)
    nz⊥ ℓ ε ρ B (Ω p g)   = ◃t (nz⊥ ℓ ε ρ B (g (br0 ℓ p))) (◃l zero)
    nz⊥ (suc a) ε ρ B (up x _ y e) =
      nz⊥ a ε ρ
        (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)) y
    nz⊥ (lim g) ε (ρc , R) B (up x n y e) =
      nz⊥ (g n) (ε n) (ρc n)
        (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x)) y
    nz⊥ (Ωₗ k h) ε ρ B (up x c y e) =
      nz⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)) y
    nz⊥ zero ε ρ B (up x () y e)

    nzs ℓ ε ρ B j w β nβ zero      = nβ
    nzs ℓ ε ρ B j w β nβ (suc x)   = ◃t (nzs ℓ ε ρ B j w β nβ x) (◃l zero)
    nzs ℓ ε ρ B j w β nβ (lim f a) = ◃t (nzs ℓ ε ρ B j w β nβ (f zero)) (◃l zero)
    nzs ℓ ε ρ B j w β nβ (Ω p g)   =
      kp-ind ℓ ε ρ p w (λ Z → j ⊢ zero ◃ Z)
        (λ q cv gd → ◃t (nzs ℓ ε ρ B j w β nβ (g (cv (br0 j q)))) ◃w)
        (◃t (nzs ℓ ε ρ B j w β nβ (g (br0 ℓ p))) (◃l zero))
    nzs ℓ ε ρ B _ self β nβ (up x c y e) = Upc-nz ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y
    nzs (suc a) ε ρ B j (ins w) β nβ (up x _ y e) =
      nzs a ε ρ
        (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x))
        j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) y
    nzs (lim g) ε (ρc , R) B j (inl n w) β nβ (up x m y e) =
      caseW-ind (λ Z → j ⊢ zero ◃ Z) (way g R m n)
        (λ v → nzs (g n) (ε n) (ρc n)
          (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
          j w (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (emb (g n) (ε n) v y e))
        (λ v → nzs (g m) (ε m) (ρc m)
          (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
          j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) y)
    nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ (up x m y e) =
      nzs (g m) (ε m) (ρc m)
        (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j (ws m) (ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) y
    nzs (Ωₗ k h) ε ρ B j (ink w) β nβ (up x c y e) =
      nzs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
        j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) y
    nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ (up x c y e) =
      nzs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
        j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) y
    nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e) =
      tW-ind (λ Z → j ⊢ zero ◃ Z) (tb k h c c′)
        (λ u → nzs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
          (chB B (λ u′ → inb c u′) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
            (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
          j (w ∙ u) (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) y)
        (λ u → nzs (h c′) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′)
          (chB B (λ u′ → inb c′ u′) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
            (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
          j w (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (emb (h c′) (proj₂ (proj₂ ε c′)) u y e))
        (◃t (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x)
         (+-mono (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (ι-mono j (nz⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y))))
    mono⊥ ℓ ε ρ B ◃s     = ◃l zero
    mono⊥ ℓ ε ρ B (◃l n) = ◃l n
    mono⊥ ℓ ε ρ B ◃w     = ◃l zero
    mono⊥ (suc a) ε ρ B (◃u x _ y e) =
      mono⊥ a ε ρ
        (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)) e
    mono⊥ (lim g) ε (ρc , R) B (◃u x n y e) =
      mono⊥ (g n) (ε n) (ρc n)
        (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x)) e
    mono⊥ (Ωₗ k h) ε ρ B (◃u x c y e) =
      mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)) e
    mono⊥ zero ε ρ B (◃u x () y e)
    mono⊥ (suc a) ε ρ B (◃c x _ d) =
      mono⊥ a ε ρ
        (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)) d
    mono⊥ (lim g) ε (ρc , R) B (◃c x n d) =
      mono⊥ (g n) (ε n) (ρc n)
        (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x)) d
    mono⊥ (Ωₗ k h) ε ρ B (◃c x c d) =
      mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)) d
    mono⊥ zero ε ρ B (◃c x () d)
    mono⊥ ℓ ε ρ B (◃t d e) = ◃t (mono⊥ ℓ ε ρ B d) (mono⊥ ℓ ε ρ B e)

    monos ℓ ε ρ B j w β nβ ◃s     = ◃l zero
    monos ℓ ε ρ B j w β nβ (◃l n) = ◃l n
    monos ℓ ε ρ B j w β nβ (◃w {p = p} {g = g}) =
      kp-ind ℓ ε ρ p w (λ Z → j ⊢ ψs ℓ ε ρ B j w β nβ (g (br0 ℓ p)) ◃ Z)
        (λ q cv gd → subst (λ t → j ⊢ ψs ℓ ε ρ B j w β nβ (g t) ◃ Ω q (λ z → ψs ℓ ε ρ B j w β nβ (g (cv z)))) gd ◃w)
        (◃l zero)
    monos ℓ ε ρ B _ self β nβ (◃u x c y e) = Upc-base ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y e
    monos (suc a) ε ρ B j (ins w) β nβ (◃u x _ y e) =
      monos a ε ρ
        (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x))
        j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) e
    monos (lim g) ε (ρc , R) B j (inl n w) β nβ (◃u x m y e) =
      caseW-ind (λ Z → j ⊢ (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) ◃ Z) (way g R m n)
        (λ v → monos (g n) (ε n) (ρc n)
          (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
          j w (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (emb-nz (g n) (ε n) v y e))
        (λ v → monos (g m) (ε m) (ρc m)
          (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
          j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) e)
    monos (lim g) ε (ρc , R) B j (inlu ws) β nβ (◃u x m y e) =
      monos (g m) (ε m) (ρc m)
        (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j (ws m) (ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) e
    monos (Ωₗ k h) ε ρ B j (ink w) β nβ (◃u x c y e) =
      monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
        j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) e
    monos (Ωₗ k h) ε ρ B j (inu ws) β nβ (◃u x c y e) =
      monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
        j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) e
    monos (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (◃u x c y e) =
      tW-ind (λ Z → j ⊢ ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x ◃ Z) (tb k h c c′)
        (λ u → monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
          (chB B (λ u′ → inb c u′) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
            (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
          j (w ∙ u) (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) e)
        (λ u → monos (h c′) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′)
          (chB B (λ u′ → inb c′ u′) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
            (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
          j w (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (emb-nz (h c′) (proj₂ (proj₂ ε c′)) u y e))
        (+-mono (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (ι-mono j (nz⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y)))
    monos ℓ ε ρ B _ self β nβ (◃c x c d) = Upc-mono ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) d
    monos (suc a) ε ρ B j (ins w) β nβ (◃c x _ d) =
      monos a ε ρ
        (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x))
        j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) d
    monos (lim g) ε (ρc , R) B j (inl n w) β nβ (◃c x m d) =
      caseW-ind₂ (λ Z Z′ → j ⊢ Z ◃ Z′) (way g R m n)
        (λ v → monos (g n) (ε n) (ρc n)
          (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
          j w (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (emb-mono (g n) (ε n) v d))
        (λ v → monos (g m) (ε m) (ρc m)
          (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
          j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) d)
    monos (lim g) ε (ρc , R) B j (inlu ws) β nβ (◃c x m d) =
      monos (g m) (ε m) (ρc m)
        (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
          (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j (ws m) (ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) d
    monos (Ωₗ k h) ε ρ B j (ink w) β nβ (◃c x c d) =
      monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
        j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) d
    monos (Ωₗ k h) ε ρ B j (inu ws) β nβ (◃c x c d) =
      monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
        (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
          (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
        j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) d
    monos (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (◃c x c d) =
      tW-ind₂ (λ Z Z′ → j ⊢ Z ◃ Z′) (tb k h c c′)
        (λ u → monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
          (chB B (λ u′ → inb c u′) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
            (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
          j (w ∙ u) (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) d)
        (λ u → monos (h c′) (proj₂ (proj₂ ε c′)) (proj₂ ρ c′)
          (chB B (λ u′ → inb c′ u′) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
            (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
          j w (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (emb-mono (h c′) (proj₂ (proj₂ ε c′)) u d))
        (+-mono (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (ι-mono j (mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) d)))
    monos ℓ ε ρ B j w β nβ (◃t d e) = ◃t (monos ℓ ε ρ B j w β nβ d) (monos ℓ ε ρ B j w β nβ e)

  dS : (a : L) → Ev (suc a) → Rt (suc a) → Base (suc a) → Tr (suc a) → Base a
  dS a ε ρ B x = chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
    (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)

  dL : (g : ℕ → L) → Ev (lim g) → Rt (lim g) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
  dL g ε ρ B n x = chB B (λ u → inl n u) (ψ⊥ (lim g) ε ρ B x) (nz⊥ (lim g) ε ρ B x)
    (λ j′ w′ β′ n′ → ψs (lim g) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε ρ B j′ w′ β′ n′ x)

  dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Rt (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
  dW k h ε ρ B c x = chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
    (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)

  ψ₀ : (ℓ : L) → Ev ℓ → Rt ℓ → Tr ℓ → Tr zero
  ψ₀ ℓ ε ρ = ψ⊥ ℓ ε ρ (B₀ ℓ)

  twᶜ : ℕ → Tr zero
  twᶜ n = ψ₀ (tw n) (Ev-tw n) (Rt-tw n) (Ωt (tw n))

  EBOᶜ : Tr zero
  EBOᶜ = ψ₀ Λ Ev-Λ Rt-Λ (Ωt Λ)
```
