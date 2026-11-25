# 任意多次有限层槽交接所付数列的精确上确界

第四层，无条件。每层将更新作任意有限次迭代再取极限。从 q 与高度参数 x 起步，全部已付下界的上确界恰为 q·ω^(ω^(x+ω))。当 q=bₙ 且 x 受 ε⁺(bₙ) 内某一步严格控制时，此上确界严格低于 ε⁺(bₙ)。这个界约束已付数列，实际槽仍可更大。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseBoundTransfer where

open import Data.Nat.Base as N using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-suc; ≼-trans; ≼-refl; s≼s; ≼l; l≼; z≼)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import Data.Empty using (⊥)
open import WVOne using (T₀; 𝟏; ≼-+ˡ)
import W4Block as W
import B13FiniteLift as Lift
import B13FiniteTower as Climb
import B14Height as Height
import B18Product as M
import B19IdealArithmetic as Ar
import B19IdealProduct as Product
import B22HeightValue as Formula
import B22MovingIndex as E
import B27UEpsilon as Hull
import Survey.W4FixedDepth as Fixed
import Survey.W4FiniteRaiseBound as Bound
import B12BtboCut as C
import B12TerminalTail as Tail

module Iteration (x q : T₀) where
  level = W.iter L.suc x
  cutoff = x L.+ L.ωᶜ
  amount = Climb.constant (Height.act x) q

  lifted : ∀ n → Climb.height (Height.act x) n ≡ Height.act (level n)
  lifted zero = refl
  lifted (suc n) = cong Lift.repeatω (lifted n)

  numeral : ∀ n → level n ≡ x L.+ L.natᶜ n
  numeral zero = refl
  numeral (suc n) = cong L.suc (numeral n)

  next : ∀ n → amount (suc n) ≡ Height.act (level (suc n)) (amount n)
  next n = cong (λ f → f (amount n)) (lifted (suc n))

  base : ∀ n → q ≼ amount n
  base zero = ≼-refl q
  base (suc n) = subst (q ≼_) (sym (next n)) (≼l {f = W.iter (Height.act (level n)) (amount n)} 0 (base n))

  upper : ∀ n → amount n ≼ Height.act (level (suc n)) q
  upper zero = ≼l {f = W.iter (Height.act x) q} 0 (≼-refl q)
  upper (suc n) = subst (_≼ Height.act (level (suc (suc n))) q) (sym (next n))
    (≼l {f = W.iter (Height.act (level (suc n))) q} 2 (Height.mono (≼-refl (level (suc n))) (upper n)))

  lower : ∀ n → Height.act (level n) q ≼ L.lim amount
  lower zero = ≼l {f = amount} 1 (≼l {f = W.iter (Height.act x) q} 1 (≼-refl _))
  lower (suc n) = ≼l {f = amount} (suc n) (subst (Height.act (level (suc n)) q ≼_) (sym (next n))
    (Height.mono (≼-refl (level (suc n))) (base n)))

  join : L.lim amount ≈ᵛ Height.act cutoff q
  join = l≼ (λ n → ≼l {f = λ k → Height.act (x L.+ L.natᶜ k) q} (suc n)
    (subst (λ t → amount n ≼ Height.act t q) (numeral (suc n)) (upper n))) ,
    l≼ (λ n → subst (λ t → Height.act t q ≼ L.lim amount) (numeral n) (lower n))

  explicit : L.lim amount ≈ᵛ (q M.· Ar.norm (Ar.norm cutoff))
  explicit = join Product.∙ Formula.exact cutoff q

finite-cut : ∀ k → (L.natᶜ k L.+ L.ωᶜ) ≈ᵛ L.ωᶜ
finite-cut k = l≼ (λ n → ≼l {f = L.natᶜ} (n N.+ k) (subst (_≼ L.natᶜ (n N.+ k)) (sym (sum n)) (≼-refl _))) ,
  ≼-+ˡ (L.natᶜ k) L.ωᶜ
  where
  sum : ∀ n → (L.natᶜ k L.+ L.natᶜ n) ≡ L.natᶜ (n N.+ k)
  sum zero = refl
  sum (suc n) = cong L.suc (sum n)

finite-tail : ∀ k q → L.lim (Climb.constant (Height.act (L.natᶜ k)) q) ≈ᵛ (q M.· Ar.norm (Ar.norm L.ωᶜ))
finite-tail k q = Iteration.join (L.natᶜ k) q Product.∙ (Height.mono (proj₁ (finite-cut k)) (≼-refl q) ,
  Height.mono (proj₂ (finite-cut k)) (≼-refl q)) Product.∙ Formula.exact L.ωᶜ q

paid-tail : ∀ q → L.lim (Climb.constant Tail.mulω q) ≈ᵛ (q M.· Ar.norm (Ar.norm L.ωᶜ))
paid-tail = finite-tail 0

module At (i : ℕ) where
  b = Fixed.sample i
  module H = Hull.At b
  small-zero : H.In L.zero
  small-zero = H.down {x = L.zero} {y = b} z≼ H.seed
  small-nat : ∀ k → H.In (L.natᶜ k)
  small-nat zero = small-zero
  small-nat (suc k) = H.sucC {L.natᶜ k} (small-nat k)
  small-omega : H.In L.ωᶜ
  small-omega = H.down {x = L.ωᶜ} {y = Ar.norm 𝟏} (M.one-left L.ωᶜ) (H.expC {𝟏} (small-nat 1))

  strict : ∀ x → H.In x → L.suc (L.lim (Climb.constant (Height.act x) b)) ≼ E.above b
  strict x px = H.finite {L.lim I.amount} (H.down {x = L.lim I.amount} {y = b M.· Ar.norm (Ar.norm y)}
    (proj₁ I.explicit) (H.mulC {b} {Ar.norm (Ar.norm y)} H.seed (H.expC {Ar.norm y} (H.expC {y}
      (H.sumC {x} {L.ωᶜ} px small-omega)))))
    where
    module I = Iteration x b
    y = I.cutoff

  no-next : (x : T₀) → H.In x → C.finite (suc (suc i)) ≼ L.lim (Climb.constant (Height.act x) b) → ⊥
  no-next x px h = s≼-irrefl (E.above b) (≼-trans {b = C.finite (suc (suc i))} (Bound.At.below-next-cut i)
    (≼-trans {b = L.lim (Climb.constant (Height.act x) b)} h (≼-trans {b = L.suc (L.lim (Climb.constant (Height.act x) b))}
      (≼-suc (≼-refl _)) (strict x px))))

  finite-height : ∀ k → L.suc (L.lim (Climb.constant (Height.act (L.natᶜ k)) b)) ≼ E.above b
  finite-height k = strict (L.natᶜ k) (small-nat k)
```
