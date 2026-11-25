# 正自槽的 Ω₂ 返回之和

第四层，无条件。在 Ω₃ 正自槽的首项之后，每个实际加项都等于其完整 Ω₂ 查询的上确界。各加项的第一次查询是同一个值 Q，故 Q·ω 不超过整槽，且 Q 严格超过指数 1 的观察值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchRunSum where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import W4Block as W
import W4Ops as O
import WKTower as Tower
import B12Terminal as T
import B12ActualSlots as Slots
import B8FreezeMain as Add
import B18Product as M
import B12TerminalSrc as Source
import B13FiniteClosed as Covered
open import WVOne using (read; read-+; T₀)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≈ᵛ-refl; ≼-refl; ≼-trans; l≼; ≼l; z≼; +-mono)
import Survey.W4FiniteRaiseWindow as Window
import Survey.W4FirstBranchRunLive as Live

module At (r : T.Run Tower.Lω) (cv : Slots.Covered r) where
  module R = Live.Actual r
  module C = R.C
  Q = R.Ω₂ 0 0

  terms : ℕ → T₀
  terms zero = read (C.raw zero)
  terms (suc n) = L.lim (R.Ω₂ n)

  sums : ℕ → T₀
  sums zero = terms zero
  sums (suc n) = sums n L.+ terms (suc n)

  match : ∀ n → sums n ≈ᵛ C.prefix n
  match zero = ≈ᵛ-refl _
  match (suc n) = ≼-trans {b = mid} (+-mono (proj₁ (match n)) (proj₁ (R.whole-branch cv n)))
      (read-+ (O.cum C.raw n) (C.raw (suc n))) ,
    ≼-trans {b = mid} (Add.read-+′ (O.cum C.raw n) (C.raw (suc n)))
      (+-mono (proj₂ (match n)) (proj₂ (R.whole-branch cv n)))
    where mid = C.prefix n L.+ read (C.raw (suc n))

  copies : ∀ n → Q M.· L.natᶜ n ≼ sums n
  copies zero = z≼
  copies (suc n) = +-mono (copies n) (≼l {f = R.Ω₂ n} 0 (≼-refl Q))

  opaque
    unfolding Window.Receiver.full
    exact : L.lim sums ≈ᵛ Window.Receiver.full r 2
    exact = subst (L.lim sums ≈ᵛ_) (sym (R.I.complete (R.J.self-slot 2))) eq
      where
      eq : L.lim sums ≈ᵛ C.full
      eq = l≼ (λ n → ≼l {f = C.prefix} n (proj₁ (match n))) ,
        l≼ (λ n → ≼l {f = sums} n (proj₂ (match n)))

  ω-returns : Q M.· L.ωᶜ ≼ Window.Receiver.full r 2
  ω-returns = ≼-trans {b = L.lim sums} (l≼ (λ n → ≼l {f = sums} n (copies n))) (proj₁ exact)

module Actual = At Source.middle Covered.middle-covered
```
