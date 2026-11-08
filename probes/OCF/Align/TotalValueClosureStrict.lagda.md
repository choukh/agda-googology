# 新真实闭包的第二个输出严格超过首输出

只消费第二个真实观察输出的正性，不假设任意裸回调单调。这个定理
将用于原 Q 正性与真实闭包种子覆盖，二者必须另行实填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueClosureStrict where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Align.ValueJudgeBase
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A
import OCF.Align.TotalValueTraceShape as T

left-add : ∀ a b → A.read a ≼ A.read (R.add a b)
left-add a b = ⊑→≼ (A.read a) (A.read-mono (R.prefix a b))

suc-add : ∀ a b → suc (zero {ℓ = zero}) ≼ A.read b →
  suc (A.read a) ≼ A.read (R.add a b)
suc-add a (suc b) (s≼s p) = s≼s (left-add a b)
suc-add a (lim f st) (≼l n p) = ≼l n (suc-add a (f n) p)

module Node (c : Ordᴵ) (t : Z) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z)
  (o₀ : Z) (o : (η : Ordᴵ) → c ⊑ᴵ η → Z) where
  module Tr = T.Node c t g o₀ o

  strict-first : suc (zero {ℓ = zero}) ≼ A.read (R.run (o (Tr.η zero) (Tr.bound zero))) →
    suc (A.read (R.run o₀)) ≼ A.read (R.run (ĉᴸ c t g o₀ o))
  strict-first p = ≼-trans
    (≼l 1 (suc-add (R.run o₀) (R.run (o (Tr.η zero) (Tr.bound zero))) p))
    (≅→≼ (A.read-cong (≅ᴵ-sym Tr.shape)))
```
