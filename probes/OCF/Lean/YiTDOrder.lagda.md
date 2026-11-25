# 全域派发与弱口径记号系统（验收定理）
编译定理：可靠全域派发给出原层序的可判定全序；加给定的一元算子即得 `Notation`，逆向亦成立。
结点内派发的出口另带 `Covers`，不能从算子封闭直接省去。前提实例在 `YiTDModels`。
复用来源：标准库 `Structures.Biased.isStrictTotalOrderᶜ` 与 `StrictToNonStrict.isDecTotalOrder`；不否定树自足。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTDOrder where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.Definitions using (Tri; Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.Structures using (IsStrictTotalOrder; IsDecTotalOrder)
import Relation.Binary.Structures.Biased as Biased
open import Relation.Binary.PropositionalEquality using (_≡_; refl; isEquivalence)
import Relation.Binary.Construct.StrictToNonStrict as SN
open import OCF.Lean.YiTDIface

module Theorems (F : Frame) where
  open Frame F
  open On F

  answer→tri : ∀ {x y} → Answer x y → Tri (x < y) (x ≡ y) (y < x)
  answer→tri (inj₁ p) = tri< p (λ { refl → irrefl p }) (λ q → irrefl (trans p q))
  answer→tri (inj₂ (inj₁ refl)) = tri≈ irrefl refl irrefl
  answer→tri (inj₂ (inj₂ q)) = tri> (λ p → irrefl (trans p q)) (λ { refl → irrefl q }) q

  tri→answer : ∀ {x y} → Tri (x < y) (x ≡ y) (y < x) → Answer x y
  tri→answer (tri< p _ _) = inj₁ p
  tri→answer (tri≈ _ p _) = inj₂ (inj₁ p)
  tri→answer (tri> _ _ p) = inj₂ (inj₂ p)

  scoped→global : ∀ {Req} → Evidence Req → (∀ x y → Req x y) → Evidence Global
  scoped→global D cover = record
    { E = Evidence.E D
    ; answer = Evidence.answer D
    ; provide = λ x y _ → Evidence.provide D x y (cover x y) }

  global→trichotomy : Evidence Global → Trichotomous _≡_ _<_
  global→trichotomy D x y = answer→tri (Evidence.answer D x y (Evidence.provide D x y tt))

  global→strict-order : Evidence Global → IsStrictTotalOrder _≡_ _<_
  global→strict-order D = Biased.isStrictTotalOrderᶜ record
    { isEquivalence = isEquivalence
    ; trans = trans
    ; compare = global→trichotomy D }

  global→order : Evidence Global → IsDecTotalOrder _≡_ (SN._≤_ _≡_ _<_)
  global→order D = SN.isDecTotalOrder _≡_ _<_ (global→strict-order D)

  global→notation : (ψ : A → A) → Evidence Global → Notation
  global→notation ψ D = record { ψ = ψ; ordered = global→strict-order D }

  notation→global : Notation → Evidence Global
  notation→global N = record
    { E = Answer
    ; answer = λ _ _ e → e
    ; provide = λ x y _ → tri→answer (IsStrictTotalOrder.compare (Notation.ordered N) x y) }

  covered→notation : (ψ : A → A) (N : Nodes) → Evidence (Scope N) → Covers N → Notation
  covered→notation ψ N D cover = global→notation ψ (scoped→global D cover)
```
