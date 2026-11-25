# 第 4 层接收的正自槽在实际迭代中折叠 Ω₂

第四层，无条件。对实际 Ω₃ 指数的每个正反馈地址，任意有限迭代位置都可输入整棵 Ω₂。第一次完整反馈与第二次之和严格高于指数 1 的窗口，并严格低于整个 Ω₃ 指数的读值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchRunLive where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Unit.Base using (tt)
import W4Block as W
import W4Fold as F
import W4Path as P
import W4Ops as O
import B12Terminal as T
import B12ActualSlots as Slots
import B13FiniteLift as Lift
import B12TerminalSrc as Source
import B13FiniteClosed as Covered
import WKTower as Tower
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; s≼s)
open import WVOne using (T₀; read)
import Survey.W4FiniteRaiseRun as Receive
import Survey.W4FiniteRaiseWindow as Win
import Survey.W4FirstBranchRun as Branch
import Survey.W4FirstBranchRunFrame as Frame

module Input (j : W.L) (r : T.Run (Lift.sc j)) (a : O.Tr⁺ (Lift.sc j)) where
  ℓ = Lift.sc j
  o = T.Run.ok r
  B = T.Run.bs r
  w = P.z≤ ℓ
  run = F.ψ ℓ o B
  β = O.Ωt W.zero
  K = F.opB ℓ o (proj₁ a) (proj₂ a)
  S = λ i t → run i t (B i t) (proj₁ a)
  module C = Branch.Loop j o K S (run W.zero w β (proj₁ a))
  val = λ x → read (proj₁ (run W.zero w β x))

  complete : ∀ {x} → Receive.Power a x → val x ≡ C.full
  complete (Receive.power tt) = refl

  one : ∀ {x} (p : Receive.Power a x) → val (Win.one p) ≡ C.small
  one (Receive.power tt) = refl

  start : Slots.Covered r → proj₁ (O.Ωt j) Slots.⊴ proj₁ (S j C.tag)
  start cv = Slots.extend (cv j C.tag) (F.mono ℓ o B j C.tag (B j C.tag) {x = W.zero} {y = proj₁ a} (proj₂ a))

module Actual (r : T.Run Tower.Lω) where
  module R = Win.Receiver r
  module J = R.J
  module U = R.U 2
  a = J.old 2 (Tower.gL 2) W.self
  module I = Input (Tower.gL 1) U.run a
  module C = I.C

  Ω₂ : ℕ → ℕ → T₀
  Ω₂ k n = C.Branch.query k (proj₁ (O.Ωt (Tower.gL 1))) n
  prefix : ℕ → T₀
  prefix = C.prefix

  start : Slots.Covered r → proj₁ (O.Ωt (Tower.gL 1)) Slots.⊴ proj₁ (I.S (Tower.gL 1) C.tag)
  start cv = I.start (U.covered (Slots.enter W.sL Tower.gL r 3 (T.prefix Tower.gL 3) cv))
  paid : Slots.Covered r → ∀ k n → L.suc (Ω₂ k n) ≼ prefix (suc k)
  paid cv k = C.Branch.Ω-in k (start cv)
  whole-branch : Slots.Covered r → ∀ k → L.lim (Ω₂ k) ≈ᵛ read (C.raw (suc k))
  whole-branch cv k = C.Branch.cofinal k (C.Branch.before k (start cv))

  module Inner = Frame.In (Tower.gL 0) I.o C.frame C.op
  stage : ∀ k → L.suc I.C.small ≼ Ω₂ k 0
  stage k = ≼-trans {b = L.suc (read (C.raw 0))}
    (s≼s (Win.Window.At.into-first (Tower.gL 1) I.o I.K I.S I.w (I.run W.zero I.w I.β (proj₁ a))))
    (Inner.At.gain C.initial C.target (I.run W.zero I.w I.β (proj₁ a)))

  opaque
    unfolding Win.Receiver.small Win.Receiver.full
    Ω₂-above-one : ∀ k → L.suc (R.small 2) ≼ Ω₂ k 0
    Ω₂-above-one k = subst (λ x → L.suc x ≼ Ω₂ k 0) (sym (I.one (J.self-slot 2))) (stage k)
    nonzero : L.suc (R.small 2) ≼ prefix 1
    nonzero = subst (λ x → L.suc x ≼ prefix 1) (sym (I.one (J.self-slot 2))) C.after-one
    into : ∀ k → L.suc (prefix k) ≼ R.full 2
    into k = subst (L.suc (prefix k) ≼_) (sym (I.complete (J.self-slot 2))) (C.strict-prefix k)

module Live = Actual Source.middle

first-Ω₂ : ∀ k n → L.suc (Live.Ω₂ k n) ≼ Live.prefix (suc k)
first-Ω₂ = Live.paid Covered.middle-covered

Ω₂-whole : ∀ k → L.lim (Live.Ω₂ k) ≈ᵛ read (Live.C.raw (suc k))
Ω₂-whole = Live.whole-branch Covered.middle-covered
```
