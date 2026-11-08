# 完整原 base 闭包的错位接线

先把最终只缺的累计嵌入提升局部化。From 模块的前提不是任意回调
保序，而是同一个实际 Free 层号上的有界嵌入；它将由 V1/V2/V3
填写。其余运行、反馈、部分和和所有 n 的覆盖均逐字为原 rowB。
在最后实填之前，不把条件结论报告为成品高下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseWhole (S : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev; iF)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.TotalValueBuildIf using (BoundedEmbedding)
open import OCF.Align.TotalValueBuildStrict using (SV; SV-L; module N)
open import OCF.Align.TotalValueBuildEmbedding using (cumulative)
open import OCF.Align.TotalValueEmbeddingOps using (compose)
open import OCF.Align.TotalValueBuildBaseEmbedding S using (omega-embedding)
open import OCF.Align.OrdLabZUniform using (Uniform)
open import OCF.Align.ValueJudgeBase
import OCF.Align.OrdLabZLevel as P
import OCF.Align.OrdLabZNoCumsum as NC
import OCF.Align.TotalValueBuildBaseOrbit S as Orbit
import OCF.Align.TotalValueBuildBaseCoverStep S as Cover
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

read-of-level : ∀ (a : Ordᶜ zero) h → A.read (toLevel a h) ≅ a
read-of-level zero h = z≅
read-of-level (suc a) h = s≅ (read-of-level a (hs⁻ h))
read-of-level (lim f) h = l≅ (λ n → read-of-level (f n) (hl₁ h n))
read-of-level (limᵢ () f) h
read-of-level (up () x) h

module From
  (lift : ∀ {a b} → SV a → SV b → A.read a ≼ A.read b →
    BoundedEmbedding a (toLevel (P.ψ⁰ (P.Ω b)) (Uniform b))) where

  module Actual {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
    (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) where
    module B = Orbit.Actual ok env ev p
    module C = Cover.Actual ok env ev p

    advance : ∀ n k → N.γ n ≼ A.read (B.η k) →
      BoundedEmbedding (N.L n) (B.η (suc k))
    advance n k h = subst (BoundedEmbedding (N.L n)) (sym (B.step k))
      (compose (lift (SV-L n) (B.coordinate-sv k)
          (≼-trans (≅→≼ (read-of-level (N.γ n) (N.cert n))) h))
        (compose
          (omega-embedding (B.coordinate-sv k) (B.coordinate-pos k) (Uniform (B.η k))
            (λ v q → proj₂ v (suc q)) ok env
            (evη _ B.F (B.η k) (B.bound k)) (lim 0 (iF B.F)))
          (cumulative B.c (R.run (toZ (B.next (B.η k) (B.bound k)))))))

    twice : ℕ → ℕ
    twice zero = zero
    twice (suc n) = suc (suc (twice n))

    coordinates : ∀ n → N.γ n ≼ A.read (B.η (twice n))
    coordinates zero = C.initial
    coordinates (suc n) = C.next-coordinate n (suc (twice n))
      (advance n (twice n) (coordinates n))

    whole : NC.BTBOᴵ ≼ A.read
      (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p)))
    whole = l≼ (λ n → C.whole n (suc (twice n))
      (advance n (twice n) (coordinates n)))
```
