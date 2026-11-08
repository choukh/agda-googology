# 真实轨道的逐项方程给整树同形

本文件只使用前一文件由检查器解出的真实轨道，既不改运行器，也不
要求函数外延或任意两份步进证明相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTraceShape where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Align.TotalValueActualTrace
import OCF.Free.TotalOrbitRun as R

equality-shape : ∀ {a b : Ordᴵ} → a ≡ b → a ≅ᴵ b
equality-shape refl = ≅ᴵ-refl _

module Node (c : Ordᴵ) (t : Z) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z)
  (o₀ : Z) (o : (ζ : Ordᴵ) → c ⊑ᴵ ζ → Z) where
  actual : Trace c t g o₀ o
  actual = trace c t g o₀ o
  open Trace actual public using (η; bound; start; step; computation)

  outputs : ℕ → Ordᴵ
  outputs = λ { zero → R.run o₀ ; (suc n) → R.run (o (η n) (bound n)) }

  parts : ∀ n → part (R.run (ĉᴸ c t g o₀ o)) n ≡ R.sum outputs n
  parts zero = refl
  parts (suc n) = cong₂ R.add (parts n) refl

  shape : R.run (ĉᴸ c t g o₀ o) ≅ᴵ R.complete outputs
  shape = l≅ (λ n → equality-shape (parts n))
```
