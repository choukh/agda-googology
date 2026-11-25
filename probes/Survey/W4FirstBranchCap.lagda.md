# 指定 Ω 指数观察的真实正反馈与首项

第四层。展开接收方表上的完整观察可得一个可数序数和。首项恰为同一表的指数 1 观察。其后每个正反馈下标都是沿同一正路径更新槽表所得的 ℕ 极限，每个零层加数也是这些实际有限迭代的极限。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchCap where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import WVOne using (read; T₀)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼l; l≼)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
import WKTower as Tower
import B13FiniteLift as Lift
import B12Terminal as T
import Survey.W4FiniteRaiseWindow as Window
import Survey.W4FiniteRaiseRun as Run
import Survey.W4FirstBranchRun as Loop

record Parts (small full : T₀) : Set where
  field
    term : ℕ → O.Tr⁺ W.zero
    finite : ℕ → ℕ → T₀
    inner : ∀ n → read (proj₁ (term n)) ≡ L.lim (finite n)
    first : small ≈ᵛ read (proj₁ (term 0))
    outer : full ≡ L.lim (λ n → read (O.cum (λ k → proj₁ (term k)) n))

module Rows (k : W.L) (o : P.Ok (Lift.sc k)) (K : F.Op {Lift.sc k} F.nil) (S : F.Base (Lift.sc k))
            (v : O.Tr⁺ W.zero) where
  j = Lift.sc k
  module A = Window.Window k o K
  module First = A.At S (P.z≤ j) v
  module Chain = Loop.Loop k o K S v
  open Chain using () renaming (point to state; tag to path)
  term = λ n → Chain.call (state n)
  sub = λ z → F.op (F.E o Chain.frame z Chain.op) (F.Einf o Chain.frame z Chain.op)
  tail = λ z m i w u → F.itV (sub z) (suc m) Chain.initial i (F.σ Chain.m w) u

  index : ∀ n → state (suc n) ≡ W.lim (λ m → proj₁ (tail (state n) m k path (S k path)))
    (λ m → F.inf (sub (state n)) (F.itS (sub (state n)) (suc m) (A.push S)) k (F.σ A.m path) (tail (state n) m k path (S k path)))
  index n = refl

  finite = λ n m → read (proj₁ (tail (state n) m W.zero (P.z≤ j) v))
  first : First.see A.first ≼ First.see (W.suc W.zero)
  first = l≼ λ m → ≼l {f = λ q → read (proj₁ (F.itV K (suc q) S W.zero (P.z≤ j) v))} m
    (subst (First.terms m ≼_) (cong (λ a → read (proj₁ a)) (A.values (suc m) S W.zero (P.z≤ j) v)) (≼-refl _))

  result : Parts (First.see (W.suc W.zero)) (First.see (proj₁ (O.Ωt j)))
  result = record { term = term ; finite = finite ; inner = λ _ → refl ; first = First.into-first , first ; outer = refl }

positive : ∀ n {j} → j ≡ Run.fin (suc n) → (o : P.Ok j) (B : F.Base j) (β : O.Tr⁺ W.zero)
  {a : O.Tr⁺ j} {x : W.Tr j} (p : Run.Power a x) → Parts
    (read (proj₁ (F.ψ j o B W.zero (P.z≤ j) β (Window.one p))))
    (read (proj₁ (F.ψ j o B W.zero (P.z≤ j) β x)))
positive n refl o B β {a} (Run.power tt) = Rows.result (Run.fin n) o (F.opB j o (proj₁ a) (proj₂ a))
  (λ i w → F.ψ j o B i w (B i w) (proj₁ a)) (F.ψ j o B W.zero (P.z≤ j) β (proj₁ a))
  where j = Run.fin (suc n)

module Receiver (r : T.Run Tower.Lω) where
  module U = Window.Receiver r
  opaque
    unfolding Window.Receiver.small Window.Receiver.full
    actual : ∀ n → Parts (U.small n) (U.full n)
    actual n = positive n (Run.tower-level n) (U.U.o n) (U.U.B n) (O.Ωt W.zero) (U.J.self-slot n)

import B12TerminalSrc as Source
fourth : Parts (Window.Live.small 2) (Window.Live.full 2)
fourth = Receiver.actual Source.middle 2
```
