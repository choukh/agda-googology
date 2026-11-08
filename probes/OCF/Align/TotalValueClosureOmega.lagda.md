# 全部正观察输出给首值加 ω 下界

闭包不只执行一次：每个实际后续观察输出为正，所以第n个部分和
至少含首值的n个后继。取整个原轨道即得首值加ω，不假回调单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueClosureOmega where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValueClosureStrict using (suc-add)
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A
import OCF.Align.TotalValueTraceShape as T

successors : Ordᶜ zero → ℕ → Ordᶜ zero
successors a zero = a
successors a (suc n) = suc (successors a n)
plus-omega : Ordᶜ zero → Ordᶜ zero
plus-omega a = lim (successors a)
successors-mono : ∀ {a b} → a ≼ b → ∀ n → successors a n ≼ successors b n
successors-mono h zero = h
successors-mono h (suc n) = s≼s (successors-mono h n)
plus-omega-mono : ∀ {a b} → a ≼ b → plus-omega a ≼ plus-omega b
plus-omega-mono h = l≼ (λ n → ≼l n (successors-mono h n))

module Node (c : Ordᴵ) (t : Z) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z)
  (o₀ : Z) (o : (η : Ordᴵ) → c ⊑ᴵ η → Z) where
  module Tr = T.Node c t g o₀ o
  lower : ∀ a → a ≼ A.read (R.run o₀) →
    (∀ η e → suc (zero {ℓ = zero}) ≼ A.read (R.run (o η e))) →
    plus-omega a ≼ A.read (R.run (ĉᴸ c t g o₀ o))
  lower a seed pos = ≼-trans (l≼ (λ n → ≼l n (part n)))
    (≅→≼ (A.read-cong (≅ᴵ-sym Tr.shape)))
    where
    part : ∀ n → successors a n ≼ A.read (R.sum Tr.outputs n)
    part zero = seed
    part (suc n) = ≼-trans (s≼s (part n))
      (suc-add (R.sum Tr.outputs n) (Tr.outputs (suc n))
        (pos (Tr.η n) (Tr.bound n)))
```
