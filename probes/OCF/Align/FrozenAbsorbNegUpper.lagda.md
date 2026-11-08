# 双 Ω 冻结输出的纯闭包上界

以下先构造纯解释器与其轨道，最终接回同一 FrozenOutputIf 模型。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenAbsorbNegUpper where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; top; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ≤⊞; ⊞-≤ʳ; mul-≤)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-add; same-mul)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenOutputIf
import OCF.Lean.Fold1Fold as F
import OCF.Align.FrozenOutputSim as Sim

P : Cd → Cd → Cd
P A hz = A
P A (hs c) = hl (mul (P A c))
P A (hl f) = hl (λ n → P A (f n))

base≤ : ∀ A c → A ≤ᵛ P A c
base≤ A hz = ≤-refl A
base≤ A (hs c) = ≤l 0 (base≤ A c)
base≤ A (hl f) = ≤l 0 (base≤ A (f 0))

mono : ∀ {A B a b} → A ≤ᵛ B → a ≤ᵛ b → P A a ≤ᵛ P B b
mono {b = b} p z≤ = ≤-trans p (base≤ _ b)
mono p (s≤s q) = l≤ (λ n → ≤l n (mul-≤ (mono p q) n))
mono p (≤s q) = ≤l 0 (mono p q)
mono p (l≤ q) = l≤ (λ n → mono p (q n))
mono p (≤l n q) = ≤l n (mono p q)

pure-same : ∀ {A B a b} → Same A B → Same a b → Same (P A a) (P B b)
pure-same p zz = p
pure-same p (ss q) = ll (same-mul (pure-same p q))
pure-same p (ll q) = ll (λ n → pure-same p (q n))

composition : ∀ A d c → Same (P (P A d) c) (P A (d ⊞ c))
composition A d hz = same-refl _
composition A d (hs c) = ll (same-mul (composition A d c))
composition A d (hl f) = ll (λ n → composition A d (f n))

assoc : ∀ (a b c : Cd) → Same (a ⊞ (b ⊞ c)) ((a ⊞ b) ⊞ c)
assoc a b hz = same-refl _
assoc a b (hs c) = ss (assoc a b c)
assoc a b (hl f) = ll (λ n → assoc a b (f n))

infl : ∀ A → hs hz ≤ᵛ A → ∀ c → c ≤ᵛ P A c
infl A pos hz = z≤
infl A pos (hs c) = ≤l 1 (≤-trans (s≤s (infl A pos c))
  (⊞-≤ʳ (P A c) (≤-trans pos (base≤ A c))))
infl A pos (hl f) = l≤ (λ n → ≤l n (infl A pos (f n)))

module Orbit (A b : Cd) where
  module C = F.Col _⊞_ _⊞_ tt b (λ _ _ → tt)
    (λ _ e → P A e) (λ _ e → P A e)
  value : Cd
  value = hl C.oO

run-up : ∀ A m w c → Same (Model.run A m w (up c)) (P A c)
run-up A m w hz = same-refl A
run-up A m w (hs c) = ll (same-mul (run-up A m w c))
run-up A m w (hl f) = ll (λ n → run-up A m w (f n))

run-initial : ∀ A m b → Same (Model.run A m b (top (hs hz))) (Orbit.value A b)
run-initial A m b = ll (S.sums)
  where
  sim-step : ∀ {w : Cd} {v : ⊤} {x y} → ⊤ → Same x y →
    Same (Model.run A m w (up x)) (P A y)
  sim-step {w} {x = x} q xy = trans-same (run-up A m w x) (pure-same (same-refl A) xy)
    where
    trans-same : ∀ {a b c : Cd} → Same a b → Same b c → Same a c
    trans-same zz zz = zz
    trans-same (ss p) (ss q) = ss (trans-same p q)
    trans-same (ll p) (ll q) = ll (λ n → trans-same (p n) (q n))
  module S = Sim.Sim (λ (_ : Cd) (_ : ⊤) → ⊤) b tt tt b b (same-refl b)
    (update m) (λ _ _ → tt) (λ _ _ → tt)
    (λ w e → Model.run A m w (up e)) (λ _ e → P A e)
    (λ w e → Model.run A m w (up e)) (λ _ e → P A e) sim-step sim-step

module Upper (A : Cd) (pos : hs hz ≤ᵛ A) where
  B : Cd
  B = Orbit.value A hz
  module D = Orbit B hz
  module E = Orbit A B

  transfer : ∀ c → P B c ≤ᵛ P A (B ⊞ c)
  transfer c = ≤-trans (mono (infl A pos B) (≤-refl c))
    (same-value (composition A B c))

  coordinates : ∀ n → B ⊞ D.C.ce n ≤ᵛ E.C.ce n
  outputs : ∀ n → D.C.oo n ≤ᵛ E.C.oo n
  coordinates zero = ≤-refl B
  coordinates (suc n) = ≤-trans (same-value (assoc B (D.C.ce n) (D.C.oo n)))
    (add-mono (coordinates n) (outputs n))
  outputs n = ≤-trans (transfer (D.C.ce n)) (mono (≤-refl A) (coordinates n))

  sums : ∀ n → D.C.oO n ≤ᵛ E.C.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))

  upper-pure : D.value ≤ᵛ E.value
  upper-pure = l≤ (λ n → ≤l n (sums n))
```

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.FrozenOutputModel using (same-trans; module Congruence)
open import OCF.Align.FrozenSupportExt using (generated-ext)

run-prefix : ∀ A m w x c →
  Same (Model.run A m w (x ⊞ up c)) (P (Model.run A m w x) c)
run-prefix A m w x hz = same-refl _
run-prefix A m w x (hs c) = ll (same-mul (run-prefix A m w x c))
run-prefix A m w x (hl f) = ll (λ n → run-prefix A m w x (f n))

pair : HB (step S⊥)
pair = top (hs hz) ⊞ top (hs hz)

frozen-pair : ∀ A → Same (Model.run A frozen hz pair)
  (Orbit.value (Orbit.value A hz) hz)
frozen-pair A = ll S.sums
  where
  B = Orbit.value A hz
  sim-step : ∀ {w : Cd} {v : ⊤} {x y} → w ≡ hz → Same x y →
    Same (Model.run A frozen w (top (hs hz) ⊞ up x)) (P B y)
  sim-step {x = x} refl xy = same-trans (run-prefix A frozen hz (top (hs hz)) x)
    (pure-same (run-initial A frozen hz) xy)
  module S = Sim.Sim (λ (w : Cd) (_ : ⊤) → w ≡ hz) hz tt refl hz hz zz
    (update frozen) (λ _ _ → tt) (λ p _ → p)
    (λ w e → Model.run A frozen w (top (hs hz) ⊞ up e)) (λ _ e → P B e)
    (λ w e → Model.run A frozen w (top (hs hz) ⊞ up e)) (λ _ e → P B e)
    sim-step sim-step

module ActualUpper (A : Cd) (pos : hs hz ≤ᵛ A) where
  open Model A
  module U = Upper A pos
  b₀ : Cd
  b₀ = run changing hz (top (hs hz))

  target-same : Same (run changing b₀ (top (hs hz))) (Orbit.value A (Orbit.value A hz))
  target-same = same-trans
    (Congruence.run-same A changing (top (hs hz)) (generated-ext initial)
      (same-refl _) (run-initial A changing hz))
    (run-initial A changing (Orbit.value A hz))

  upper : run frozen hz pair ≤ᵛ run changing b₀ (top (hs hz))
  upper = ≤-trans (same-value (frozen-pair A))
    (≤-trans U.upper-pure (same-value (same-sym target-same)))
```

`ActualUpper.upper` 的输入就是 Generated.plus initial initial。正性前提可以用
FrozenAbsorbSeed.positive-actual-base 实例化；本篇上界不依赖记号或函数外延。
