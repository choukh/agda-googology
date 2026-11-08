# 生成元相加时实际首个反馈种子的严格推进

检验 Generated.plus initial initial 的真实反馈，不另选巨大种子。
下界来自首个后继回灌点；尚未假定冻结端的上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenAbsorbPair where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; mul)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; mul-≤)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenOutputIf using (Mode; changing; frozen; update; Generated; initial; plus)
open import OCF.Align.FrozenSupportExt using (generated-ext)
open import OCF.Align.FrozenAbsorbSeed using (right-add; positive-actual-base)
import OCF.Align.FrozenAbsorbSeed as Seed
import OCF.Align.FrozenOutputIf as If
import OCF.Align.FrozenOutputModel as M
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1 as Original

one : Cd
one = hs hz
I : HB (step S⊥)
I = top (hs hz)
pair : HB (step S⊥)
pair = I ⊞ I
pair-generated : Generated pair
pair-generated = plus initial initial

zero-add : ∀ (c : Cd) → Same (hz ⊞ c) c
zero-add hz = zz
zero-add (hs c) = ss (zero-add c)
zero-add (hl f) = ll (λ n → zero-add (f n))

module Pair (A : Cd) (positive-A : one ≤ᵛ A) where
  open If.Model A
  module S = Seed.Seed A positive-A
  module MC = M.Congruence A
  B : Cd → Cd
  B b = run changing b I
  B₀ = B hz
  BB₀ = B B₀

  module Outer = F.Col _⊞_ _⊞_ hz hz (update changing)
    (λ w e → run changing w (I ⊞ up e))
    (λ w e → run changing w (I ⊞ up e))

  first-seed : Same (Outer.ce 1) B₀
  first-seed = zero-add B₀
  first-seed-positive : one ≤ᵛ Outer.ce 1
  first-seed-positive = ≤-trans (S.Orbit.strict-seed changing hz)
    (same-value (same-sym first-seed))

  -- 确实是实际轨道中的种子，前缀值已严格超过原来的 B₀。
  prefix-progress : hs B₀ ≤ᵛ B (Outer.ce 1)
  prefix-progress = ≤-trans (s≤s (same-value (same-sym first-seed)))
    (S.Orbit.strict-seed changing (Outer.ce 1))
  prefix-not-stable : B (Outer.ce 1) ≤ᵛ B₀ → ⊥
  prefix-not-stable p = ¬s≤ᵛ B₀ (≤-trans prefix-progress p)

  prefix-base≥BB₀ : BB₀ ≤ᵛ B (Outer.ce 1)
  prefix-base≥BB₀ = same-value (MC.run-same changing I (generated-ext initial)
    (same-refl I) (same-sym first-seed))

  tail : Mode → Cd → HB (step S⊥) → Cd → Cd
  tail m b p c = run m b (p ⊞ up c)
  tail-positive : ∀ m b p c → tail m b p hz ≤ᵛ tail m b p c
  tail-positive m b p hz = ≤-refl _
  tail-positive m b p (hs c) = ≤l 0 (tail-positive m b p c)
  tail-positive m b p (hl f) = ≤l 0 (tail-positive m b p (f 0))

  tail-mono : ∀ m b p {c d} → c ≤ᵛ d → tail m b p c ≤ᵛ tail m b p d
  tail-mono m b p {d = d} z≤ = tail-positive m b p d
  tail-mono m b p (s≤s q) = l≤ (λ n → ≤l n (mul-≤ (tail-mono m b p q) n))
  tail-mono m b p (≤s q) = ≤l 0 (tail-mono m b p q)
  tail-mono m b p (l≤ q) = l≤ (λ n → tail-mono m b p (q n))
  tail-mono m b p (≤l n q) = ≤l n (tail-mono m b p q)

  strict-output : hs BB₀ ≤ᵛ Outer.oo 1
  strict-output = ≤-trans (s≤s prefix-base≥BB₀)
    (≤-trans
      (≤l 1 (add-mono (≤-refl _) (≤-trans (s≤s z≤)
        (S.Orbit.strict-seed changing (Outer.ce 1)))))
      (tail-mono changing (Outer.ce 1) I first-seed-positive))

  strict-pair : hs BB₀ ≤ᵛ run changing hz pair
  strict-pair = ≤l 1 (≤-trans strict-output (right-add (Outer.oo 0) (Outer.oo 1)))

module Actual = Pair Original.TΩ1 positive-actual-base
```

`prefix-not-stable` 已否定实际首个反馈点的前缀常值替换；范围精确到这条
Generated 内的轨道。`strict-pair` 给整个 changing pair 严格下界。
是否因此否定同点吸收，还要冻结 pair 的对应上界，不能跳过该义务。
