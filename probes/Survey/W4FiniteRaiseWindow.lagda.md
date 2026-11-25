# 从每个实际正自槽中取出指数 1 的完整迭代

第四层。在每个实际相邻有限层的接收环境里，指定正自槽以 Ω 为指数。其第一位置收下指数 1 的完整迭代，整个 Ω 指数的观察又严格低于接收层的运行值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseWindow where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
import B13FiniteLift as Lift
import B12Terminal as T
import B12Strict as Strict
import B12ActualSlots as Slots
import WKTower as Tower
open import WVOne using (read; T₀)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; s≼s)
import Survey.W4FiniteRaiseRun as Run

module Window (j : W.L) (o : P.Ok (Lift.sc j)) (K : F.Op {Lift.sc j} F.nil) where
  ℓ = Lift.sc j
  m = F.chMT (F.tdNil {ℓ}) tt
  push : F.Base ℓ → F.St (F.cons (O.down O.stop tt) F.nil)
  push S i t = S i (proj₂ t)
  pull : F.St (F.cons (O.down O.stop tt) F.nil) → F.Base ℓ
  pull S i t = S i (F.σ m t)
  states : ∀ n S → pull (F.itS (F.enterO m K) n (push S)) ≡ F.itS K n S
  states zero S = refl
  states (suc n) S = cong (F.stepS K) (states n S)

  values : ∀ n S i (w : i W.≤ ℓ) v →
    F.itV (F.enterO m K) n (push S) i (F.σ m w) v ≡ F.itV K n S i w v
  values zero S i w v = refl
  values (suc n) S i w v rewrite states n S | values n S i w v = refl

  first = W.up {S = W.Sig ℓ} W.zero tt (W.suc W.zero) W.◃s
  run = F.E o F.tdNil
  module At (S : F.Base ℓ) (w : W.zero W.≤ ℓ) (v : O.Tr⁺ W.zero) where
    see = λ x → read (proj₁ (run x K S W.zero w v))
    terms = λ k → read (proj₁ (F.itV (F.enterO m K) (suc k) (push S) W.zero (F.σ m w) v))
    into-first : see (W.suc W.zero) ≼ see first
    into-first = l≼ λ k → ≼l {f = terms} k (subst (λ a → read (proj₁ a) ≼ terms k)
      (values (suc k) S W.zero w v) (≼-refl (terms k)))

    strict : L.suc (see (W.suc W.zero)) ≼ see (proj₁ (O.Ωt ℓ))
    strict = ≼-trans {b = L.suc (see first)} (s≼s into-first)
      (Strict.strict (F.Emono o F.tdNil K S W.zero w v {x = first} {y = proj₁ (O.Ωt ℓ)} W.◃w))

one : ∀ {j} {a : O.Tr⁺ j} {x} → Run.Power a x → W.Tr j
one {a = a} (Run.power e) = W.ex (proj₁ a) (proj₁ a) (proj₂ a) (W.suc W.zero) e

above-one : ∀ {j} {a : O.Tr⁺ j} {x} → proj₁ (O.Ωt j) Slots.⊴ proj₁ a →
  (p : Run.Power a x) → j W.⊢ proj₁ (O.Ωt j) ◃ one p
above-one {j} {a} (inj₁ eq) (Run.power e) = subst (λ t → j W.⊢ t ◃ W.ex (proj₁ a) (proj₁ a) (proj₂ a) (W.suc W.zero) e) (sym eq) W.◃e
above-one (inj₂ d) (Run.power _) = W.◃t d W.◃e

inside : ∀ {j} n → j ≡ Run.fin (suc n) → (o : P.Ok j) (B : F.Base j) (β : O.Tr⁺ W.zero)
  {a : O.Tr⁺ j} {x : W.Tr j} (p : Run.Power a x) →
  L.suc (read (proj₁ (F.ψ j o B W.zero (P.z≤ j) β (one p)))) ≼
  read (proj₁ (F.ψ j o B W.zero (P.z≤ j) β x))
inside n refl o B β {a} (Run.power tt) = Window.At.strict (Run.fin n) o (F.opB j o (proj₁ a) (proj₂ a))
  (λ i w → F.ψ j o B i w (B i w) (proj₁ a)) (P.z≤ j) (F.ψ j o B W.zero (P.z≤ j) β (proj₁ a))
  where j = Run.fin (suc n)

module Actual (r : T.Run Tower.Lω) where
  module J = Run.At r

  in-slot : ∀ n → L.suc (J.observe n (one (J.self-slot n))) ≼
    J.observe n (proj₁ (T.Run.bs (J.higher n) (Tower.gL n) (J.path n W.self)))
  in-slot n = inside n (Run.tower-level n) (J.ok n) (J.old n) (T.Run.β (J.replay n)) (J.self-slot n)

import B31Head as Head
import B31UProduct as Product
import B18Product as M
import B19PathValue as V
import B14PathHeight as Path
import B12TerminalSrc as Source

unit-in : ∀ j (r : T.Run j) → Product.fold₁ r ≼ read (T.value r)
unit-in j r = ≼-trans {b = read (proj₁ (T.Run.β r)) M.· Product.fold₁ r}
  (M.pad (T.Run.oneβ r) (Product.fold₁ r))
  (proj₂ (V.At.scale j (T.Run.ok r) (T.Run.bs r) (proj₁ (O.Ωt j)) (Path.standard j) (T.Run.β r)))

-- 使用接收方自己的子槽表，与交接前重算时用的表分别给出。
module Use {j k z} (h : Run.LastInput j k z) (r : T.Run k) where
  o = Run.child-ok h (T.Run.ok r)
  B = Run.restrict h (T.Run.bs r)
  see = λ x → read (proj₁ (F.ψ j o B W.zero (P.z≤ j) (O.Ωt W.zero) x))
  slot = B j W.self
  run : T.Run j
  run = T.makeRun o B (O.Ωt W.zero) (λ w → T.Run.oneB r (Run.into h w))
    (λ w → T.Run.omegaB r (Run.into h w)) (≼-refl _)
  covered : Slots.Covered r → Slots.Covered run
  covered cv i w = cv i (Run.into h w)

received : ∀ {j k z} n → j ≡ Run.fin (suc n) → (h : Run.LastInput j k z) (r : T.Run k) →
  L.suc (Use.see h r (proj₁ (Use.slot h r))) ≼ read (T.value r)
received n refl Run.child r = ≼-trans {b = H.leaf 1}
  (Strict.strict {x = proj₁ (F.ψ j H.o H.B W.zero (P.z≤ j) (O.Ωt W.zero) (proj₁ H.slot))}
    {y = proj₁ (H.probe 1)} (F.mono j H.o H.B W.zero (P.z≤ j) (O.Ωt W.zero)
      {x = proj₁ H.slot} {y = H.state 1} W.◃e))
  (≼-trans {b = Product.fold₁ r} (H.into 1) (unit-in (Lift.sc j) r))
  where
  j = Run.fin (suc n)
  module H = Head.Cell j r

module Receiver (r : T.Run Tower.Lω) where
  module J = Run.At r
  module U (n : ℕ) = Use (J.last-input n) (J.higher n)
  opaque
    small : ℕ → T₀
    small = λ n → U.see n (one (J.self-slot n))
    full : ℕ → T₀
    full = λ n → U.see n (proj₁ (U.slot n))

    in-full : ∀ n → L.suc (small n) ≼ full n
    in-full n = inside n (Run.tower-level n) (U.o n) (U.B n) (O.Ωt W.zero) (J.self-slot n)

    into-run : ∀ n → L.suc (full n) ≼ read (T.value (J.higher n))
    into-run n = received n (Run.tower-level n) (J.last-input n) (J.higher n)

    inherited : ∀ n (q : T₀) → ((u : T.Run (Tower.gL n)) → Slots.Covered u → q ≼ read (T.value u)) →
      Slots.Covered r → L.suc q ≼ small n
    inherited n q law cv = ≼-trans {b = L.suc (read (T.value (U.run n)))} (s≼s (law (U.run n) (U.covered n
      (Slots.enter W.sL Tower.gL r (suc n) (T.prefix Tower.gL (suc n)) cv)))) (Strict.strict {x = T.value (U.run n)}
        {y = proj₁ (F.ψ (Tower.gL n) (U.o n) (U.B n) W.zero (P.z≤ (Tower.gL n)) (O.Ωt W.zero) (one (J.self-slot n)))} cmp)
      where
      j : W.L
      j = Tower.gL n
      cmp : W.zero W.⊢ T.value (U.run n) ◃ proj₁ (F.ψ j (U.o n) (U.B n) W.zero (P.z≤ j) (O.Ωt W.zero) (one (J.self-slot n)))
      cmp = F.mono j (U.o n) (U.B n) W.zero (P.z≤ j) (O.Ωt W.zero) {x = proj₁ (O.Ωt j)} {y = one (J.self-slot n)}
        (above-one (J.covered cv n j W.self) (J.self-slot n))

module Live = Receiver Source.middle

in-tree : ∀ n → L.suc (Live.full n) ≼ read F.EBOᶜ
in-tree n = ≼-trans {b = read (T.value (T.finiteRun (suc n)))} (Live.into-run n) (T.finite-ge (suc n))
```
