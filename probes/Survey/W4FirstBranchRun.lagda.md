# 正自槽的第二个实际反馈地址

第四层，无条件。后继层 Ω 指数的第二个反馈地址严格高于孩子的完整 Ω。该地址的每次有限迭代均给一个时刻，在当时的槽表和种子上折叠完整的孩子 Ω，结果严格低于下一次实际更新。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchRun where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
import B12ActualSlots as Slots
import B12Strict as Strict
import B13FiniteLift as Lift
open import WVOne using (T₀; read; cum-≥)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-suc; ≼-trans; ≼l; l≼; s≼s)
import Survey.W4FiniteRaiseWindow as Win

module Loop (j : W.L) (o : P.Ok (Lift.sc j)) (K : F.Op {Lift.sc j} F.nil)
  (S : F.Base (Lift.sc j)) (β : O.Tr⁺ W.zero) where
  ℓ = Lift.sc j
  w = P.z≤ ℓ
  tag : j W.≤ ℓ
  tag = W.inc tt W.self
  body : W.Tr j → W.Tr ℓ
  body x = W.up W.zero tt (W.suc x) (O.z◃ x W.◃s)
  call = λ x → F.E o F.tdNil (body x) K S W.zero w β
  step = λ x → proj₁ (F.E o F.tdNil (body x) K S j tag (S j tag))
  point = W.iter step W.zero
  raw = λ k → proj₁ (call (point k))
  prefix = λ k → read (O.cum raw k)
  full = read (proj₁ (F.E o F.tdNil (proj₁ (O.Ωt ℓ)) K S W.zero w β))
  small = read (proj₁ (F.E o F.tdNil (W.suc W.zero) K S W.zero w β))

  strict-prefix : ∀ k → L.suc (prefix k) ≼ full
  strict-prefix k = ≼l (suc k) (Strict.strict (O.+-mono (O.cum raw k) (proj₂ (call (point (suc k))))))

  after-one : L.suc small ≼ prefix 1
  after-one = ≼-trans {b = L.suc (prefix 0)}
    (s≼s (Win.Window.At.into-first j o K S w β))
    (Strict.strict (O.+-mono (raw 0) (proj₂ (call (point 1)))))

  source : ∀ k → j W.⊢ proj₁ (S j tag) ◃ point (suc k)
  source k = F.Einf o F.tdNil (body (point k)) K S j tag (S j tag)

  m = F.chMT (F.tdNil {ℓ}) tt
  frame = F.chTD (F.tdNil {ℓ}) tt
  op = F.enterO m K
  initial : F.St (F.cons (O.down O.stop tt) F.nil)
  initial i t = S i (proj₂ t)
  target = F.σ m w

  module Branch (k : ℕ) where
    x = point (suc k)
    update = F.op (F.E o frame x op) (F.Einf o frame x op)
    state = λ n → F.itS update n initial
    seed = λ n → F.itV update n initial W.zero target β
    query : W.Tr j → ℕ → T₀
    query y n = read (proj₁ (F.E o frame y op (state n) W.zero target (seed n)))
    actual = λ n → read (proj₁ (seed n))

    below : ∀ {y} → j W.⊢ y ◃ x → ∀ n → L.suc (query y n) ≼ actual (suc n)
    below {y} d n = Strict.strict (F.Emono o frame op (state n) W.zero target (seed n) {x = y} {y = x} d)

    in-prefix : ∀ n → actual (suc n) ≼ prefix (suc k)
    in-prefix n = ≼-trans {b = read (raw (suc k))}
      (≼l {f = λ i → actual (suc i)} n (≼-refl _)) (cum-≥ raw (suc k))

    before : proj₁ (O.Ωt j) Slots.⊴ proj₁ (S j tag) → j W.⊢ proj₁ (O.Ωt j) ◃ x
    before (inj₁ eq) = subst (λ t → j W.⊢ t ◃ x) (sym eq) (source k)
    before (inj₂ d) = W.◃t d (source k)

    Ω-in : proj₁ (O.Ωt j) Slots.⊴ proj₁ (S j tag) → ∀ n → L.suc (query (proj₁ (O.Ωt j)) n) ≼ prefix (suc k)
    Ω-in cv n = ≼-trans {b = actual (suc n)} (below (before cv) n) (in-prefix n)

    next : ∀ y n → L.suc (actual n) ≼ query y n
    next y n = Strict.strict (F.Einf o frame y op (state n) W.zero target (seed n))

    cofinal : ∀ {y} → j W.⊢ y ◃ x → L.lim (query y) ≈ᵛ read (raw (suc k))
    cofinal {y} d = l≼ (λ n → ≼l {f = λ i → actual (suc i)} n (weak (below d n))) ,
      l≼ (λ n → ≼l {f = query y} (suc n) (weak (next y (suc n))))
      where
      weak : ∀ {a b : T₀} → L.suc a ≼ b → a ≼ b
      weak {a} p = ≼-trans {b = L.suc a} (≼-suc (≼-refl a)) p
```
