# 显式种子前缀覆盖实际初始生成元

对任意种子证明 Covers b initial，另给零/后继/ℕ-极限归纳子句。
这是值侧验收；不据此断言 D initial 合法或被原冻结轨道覆盖。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenCoverInitial where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top; _≤ᵛ_; z≤; l≤; ≤l; mul)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ≤⊞; mul-≤)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ll; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-add; same-mul)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenOutputIf using (Mode; changing; frozen; update)
import OCF.Align.FrozenOutputIf as If
open import OCF.Align.FrozenCoverIf using (D)
import OCF.Align.FrozenCoverIf as Cover
open import OCF.Align.FrozenAbsorbNegUpper using (P; base≤; mono; pure-same; composition; assoc; run-up; run-prefix; run-initial)
import OCF.Align.FrozenAbsorbNegUpper as Pure
open import OCF.Align.FrozenOutputModel using (same-trans)
import OCF.Align.FrozenOutputSim as Sim
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1 as Original

module Initial (A : Cd) where
  open If.Model A
  open Cover.Candidate A using (Covers)

  zero-cover : ∀ b → Covers b hz
  zero-cover b = ≤-trans (base≤ A b) (same-value (same-sym (run-up A frozen hz b)))
  successor-cover : ∀ b c → Covers b c → Covers b (hs c)
  successor-cover b c p = l≤ (λ n → ≤l n (mul-≤ p n))
  limit-cover : ∀ b f → (∀ n → Covers b (f n)) → Covers b (hl f)
  limit-cover b f p = l≤ (λ n → ≤l n (p n))

  tail-normal : ∀ b x c → Same
    (run frozen hz (up b ⊞ (up x ⊞ D (up c))))
    (P (run frozen hz (up b ⊞ up x)) c)
  tail-normal b x hz = same-refl _
  tail-normal b x (hs c) = ll (same-mul (tail-normal b x c))
  tail-normal b x (hl f) = ll (λ n → tail-normal b x (f n))

  branch-normal : ∀ b x → Same
    (run frozen hz (up b ⊞ (up x ⊞ D (up x))))
    (P A ((b ⊞ x) ⊞ x))
  branch-normal b x = same-trans (tail-normal b x x)
    (same-trans
      (pure-same (same-trans (run-prefix A frozen hz (up b) x)
        (same-trans (pure-same (run-up A frozen hz b) (same-refl x))
          (composition A b x))) (same-refl x))
      (composition A (b ⊞ x) x))

  module At (b : Cd) where
    module L = Pure.Orbit A b
    Rf : Cd → Cd
    Rf x = P A ((b ⊞ x) ⊞ x)
    module R = F.Col _⊞_ _⊞_ tt hz (λ _ _ → tt) (λ _ e → Rf e) (λ _ e → Rf e)

    actual-normal : Same (run frozen hz (up b ⊞ D (top (hs hz)))) (hl R.oO)
    actual-normal = ll CS.sums
      where
      rec-same : ∀ {w : Cd} {v : ⊤} {x y} → w ≡ hz → Same x y →
        Same (run frozen w (up b ⊞ (up x ⊞ D (up x)))) (Rf y)
      rec-same {x = x} refl xy = same-trans (branch-normal b x)
        (pure-same (same-refl A) (same-add (same-add (same-refl b) xy) xy))
      module CS = Sim.Sim (λ (w : Cd) (_ : ⊤) → w ≡ hz) hz tt refl hz hz zz
        (update frozen) (λ _ _ → tt) (λ p q → p)
        (λ w e → run frozen w (up b ⊞ (up e ⊞ D (up e)))) (λ _ e → Rf e)
        (λ w e → run frozen w (up b ⊞ (up e ⊞ D (up e)))) (λ _ e → Rf e)
        rec-same rec-same

    coordinates : ∀ n → L.C.ce n ≤ᵛ b ⊞ R.ce n
    outputs : ∀ n → L.C.oo n ≤ᵛ R.oo n
    coordinates zero = ≤-refl b
    coordinates (suc n) = ≤-trans (add-mono (coordinates n) (outputs n))
      (same-value (same-sym (assoc b (R.ce n) (R.oo n))))
    outputs n = mono (≤-refl A) (≤-trans (coordinates n) (≤⊞ (b ⊞ R.ce n) (R.ce n)))

    sums : ∀ n → L.C.oO n ≤ᵛ R.oO n
    sums zero = outputs zero
    sums (suc n) = add-mono (sums n) (outputs (suc n))

    initial-cover : Covers b (top (hs hz))
    initial-cover = ≤-trans (same-value (run-initial A changing b))
      (≤-trans (l≤ (λ n → ≤l n (sums n)))
        (same-value (same-sym actual-normal)))

  initial-cover : ∀ b → Covers b (top (hs hz))
  initial-cover = At.initial-cover

module Actual = Initial Original.TΩ1
```

首个 Ω 生成元已经对所有种子得到统一值覆盖，无额外正性前提。
Generated 的加法与坐标作用闭包仍未证明；D 的合法性是独立问题。
