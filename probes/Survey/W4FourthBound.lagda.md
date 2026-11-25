# 第四层子运行的自槽落在哪一侧

第四层，无条件。把实际自槽用同一子运行折回零层，它严格夹在子运行的完整 Ω 值与外层 (4,1) 反馈之间。该槽等于以完整 Ω₄ 为指数的 ex 项。后继层的 Ω 输出只读取经孩子进入的底槽。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FourthBound where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import W4Block as W
import W4Fold as F
import W4Ops as O
import W4Path as Path
open import WVOne using (read; T₀)
import B12ActualSlots as Slots
import B31Head as Head
import B12Strict as Strict
import B12Terminal as T
import B12TerminalSrc as Source
import B13FiniteClosed as Covered
import B13FiniteLift as Lift
import WKTower as Tower
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import Survey.W4FixedDepth as D

module Successor (k : W.L) where
  root = Lift.sc k

  replace : F.Base root → F.Base root → F.Base root
  replace B C i W.self = C i W.self
  replace B C i (W.inc c w) = B i (W.inc c w)
  replace B C i (W.inu w) = C i (W.inu w)

  fold : Path.Ok root → F.Base root → O.Tr⁺ W.zero → W.Tr W.zero
  fold o B β = proj₁ (F.ψ root o B W.zero (Path.z≤ root) β (proj₁ (O.Ωt root)))

  same-output : ∀ o B C β → fold o (replace B C) β ≡ fold o B β
  same-output o B C β = refl

prefix-step : ∀ g n → W.nd W.sL g W.⊢ T.prefix g n ◃ T.prefix g (suc n)
prefix-step g zero = proj₂ (O.upz {s = W.sL} {h = g} 0 (O.Ωt (g 0)))
prefix-step g (suc n) = O.+-mono (T.prefix g (suc n)) (proj₂ (O.upz {s = W.sL} {h = g} (suc n) (O.Ωt (g (suc n)))))

below-step : ∀ {k} {a b c : W.Tr k} → a Slots.⊴ b → k W.⊢ b ◃ c → k W.⊢ a ◃ c
below-step (inj₁ refl) e = e
below-step (inj₂ d) e = W.◃t d e

module Input (s : W.Sh) (g : W.Ch s → W.L) (u : T.Run (Lift.sc (W.nd s g))) where
  j = W.nd s g
  module H = Head.Cell j u
  value = read (proj₁ (F.ψ j H.o H.B W.zero (Path.z≤ j) (O.Ωt W.zero) (proj₁ H.slot)))
  bound : L.suc value ≼ H.leaf 1
  bound = Strict.strict (F.mono j H.o H.B W.zero (Path.z≤ j) (O.Ωt W.zero)
    {x = proj₁ H.slot} {y = H.state 1} W.◃e)

module Fourth = D.Fourth
r = Fourth.sub
k = Fourth.k
p : k W.≤ Tower.Lω
p = W.inc 4 (W.inc tt W.self)

slot = proj₁ (T.Run.bs r k W.self)
observe : W.Tr k → T₀
observe x = read (proj₁ (F.ψ k (T.Run.ok r) (T.Run.bs r) W.zero (Path.z≤ k) (T.Run.β r) x))

stage : ℕ → W.Tr k
stage j = proj₁ (F.ψ Tower.Lω (T.Run.ok Source.middle) (T.Run.bs Source.middle) k p
  (T.Run.bs Source.middle k p) (T.prefix Tower.gL j))

stage-step : ∀ j → k W.⊢ stage j ◃ stage (suc j)
stage-step j = F.mono Tower.Lω (T.Run.ok Source.middle) (T.Run.bs Source.middle) k p
  (T.Run.bs Source.middle k p) (prefix-step Tower.gL j)

stored : stage 4 ≡ slot
stored = refl

starts : k W.⊢ proj₁ (O.Ωt k) ◃ stage 1
starts = below-step (Covered.middle-covered k p) (stage-step 0)

edge : ∀ {a b : W.Tr k} → k W.⊢ a ◃ b → L.suc (observe a) ≼ observe b
edge d = Strict.strict (F.mono k (T.Run.ok r) (T.Run.bs r) W.zero (Path.z≤ k) (T.Run.β r) d)

ahead : L.suc (read (T.value r)) ≼ observe slot
ahead = edge (W.◃t starts (W.◃t (stage-step 1) (W.◃t (stage-step 2) (stage-step 3))))

module ActualInput = Input W.sS (λ _ → Tower.gL 2) (T.finiteRun 4)

module Last (B : F.Base Tower.Lω) (v : O.Tr⁺ k) where
  partial = λ j → F.ψ Tower.Lω (T.Run.ok Source.middle) B k p v (T.prefix Tower.gL j)
  a = partial 3

  form : proj₁ (partial 4) ≡ W.ex (proj₁ a) (proj₁ a) (proj₂ a) (proj₁ (O.Ωt k)) tt
  form = refl

module ActualSlot = Last (T.Run.bs Source.middle) (T.Run.bs Source.middle k p)
```
