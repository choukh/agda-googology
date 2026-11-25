# YiXV: 实际 pre 2 的序数值上界
> 验收文件。档位：编译定理。read(pre 2) ≼ ψ₀(Ω₃)；实际 γ₂、全内链、底分量和部分和均已实填，尚未证明所有 pre n、Need1 或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Ceiling where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiCeilRead using (plus≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼)
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVSim as Old
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVThird as T
import OCF.Lean.YiXVTwo as W
import OCF.Lean.YiXVThirdZero as T0
import OCF.Lean.YiXVSlotSrc as TS
import OCF.Lean.YiXVStart as Start
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Zero as Z
import OCF.Lean.YiXVCan2Gamma as G
import OCF.Lean.YiXVCan2Rel as S
import OCF.Lean.YiXVCan2Sem as Sem
import OCF.Lean.YiXVCan2Domain as D

Ω₃ : L.Ordᶜ (L.suc (L.suc (L.suc L.zero)))
Ω₃ = L.Ω (L.suc (L.suc (L.suc L.zero)))

module Frame (Comp : Base (suc zero)) (B : Base (suc (suc (suc zero))))
  (zeroU : Old.Sim.U Comp zero O.Ω₁) (zeroC : H.Anchor.Closed Comp zeroU)
  (b : read (b⊥ B) ≼ L.ψ⁰ F.Ω₂)
  (s : read (bs B zero (ins (ins (ins self)))) ≼ L.ψ⁰ F.Ω₂)
  (seed : Σ (Old.Sim.U Comp (bs B (suc zero) (ins (ins self))) (F.ψ₁ F.Ω₂)) (H.Anchor.Closed Comp)) where
  E : Base (suc (suc zero))
  E = dS (suc (suc zero)) tt tt B zero
  β = bs B (suc (suc zero)) (ins self)
  nβ = ns B (suc (suc zero)) (ins self)
  χ = ψs (suc (suc zero)) tt tt E (suc (suc zero)) self β nβ
  c : ℕ → Tr (suc (suc zero))
  c = iter (λ x → χ (suc x)) zero
  rows : ℕ → Tr zero
  rows n = ψ⊥ (suc (suc zero)) tt tt E (suc (c n))
  module U = S.Rel Comp
  module V = Sem.Sem Comp E b s seed zeroU zeroC
  module Val = Sem.Value Comp E
  Gr : ℕ → L.Ordᶜ L.zero
  Gr n = L.ψ⁰ (G.Γ n)
  le : ∀ n → Gr n ≼ Gr (suc n)
  le n = Z.mono₀ (G.next n)
  dbl : ∀ n → (Gr n L.+ Gr n) ≼ Gr (suc n)
  dbl n = ≼-trans (≼l 2 (≼-refl _)) (Z.mono₀ (G.inv n))

  module Run (bounds : ∀ n → U.U (c n) (G.Γ (D.idx n))) where
    row-bound : ∀ n → read (rows n) ≼ Gr (suc (D.idx n))
    row-bound n = ≼-trans (Val.Out.bot≤ (V.upper (C.gs (G.good (D.idx n))) (U.us (bounds n)))) (Z.mono₀ (G.inv (D.idx n)))
    sums : ∀ n → read (cum rows n) ≼ Gr (suc (suc (D.idx n)))
    sums zero = ≼-trans (row-bound 0) (le 5)
    sums (suc n) = ≼-trans (plus≼ (cum rows n) (rows (suc n))
      (≼-trans (sums n) raise) (row-bound (suc n))) (dbl (suc (D.idx (suc n))))
      where
      raise = ≼-trans (le (suc (suc (D.idx n)))) (le (suc (suc (suc (D.idx n)))))
    ceiling : read (ψ⊥ (suc (suc (suc zero))) tt tt B (Ωt (suc (suc (suc zero))))) ≼ L.ψ⁰ Ω₃
    ceiling = l≼ (λ n → ≼l (suc (suc (D.idx n))) (sums n))

module Actual = Frame I.D1 T.B3 I.zeroU refl W.pre1-upper T0.actual-upper (TS.actual-upper , TS.actual-closed)
module ActualRun = Actual.Run D.bounds

pre2-upper : read (Start.pre 2) ≼ L.ψ⁰ Ω₃
pre2-upper = subst (λ x → read x ≼ L.ψ⁰ Ω₃) (sym T.pre2-form) ActualRun.ceiling
```
