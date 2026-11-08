# 真实私有反馈轨道的严格性归纳

消费 ActualTrace 给出的原 run 轨道，不重新定义另一条 coord。闭包
前提针对原 g/o 的实际调用；下一实例将在原 rowB 上全部填写。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildTraceStrict where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂; subst; subst₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Align.TotalValueBuildStrict using (SV; svl; Pos; ps; pl; SV-≅)
open import OCF.Align.TotalValueBuildRunStrict using (add-sv; sum-sv; add-prec; complete-sv)
open import OCF.Align.TotalValueActualTrace using (Trace; trace; part)
import OCF.Free.TotalOrbitRun as R
import OCF.Align.TotalValueTraceShape as Shape

add-pos : ∀ c d → Pos c → Pos (R.add c d)
add-pos c zero p = p
add-pos c (suc d) p = ps
add-pos c (lim f st) p = pl

module Whole (c : Ordᴵ) (t : Z) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z)
  (o₀ : Z) (o : (η : Ordᴵ) → c ⊑ᴵ η → Z)
  (cs : SV c) (cp : Pos c) (ts : SV (R.run t))
  (gs : ∀ η e → SV η → Pos η → SV (R.run (g η e)))
  (os : SV (R.run o₀))
  (og : ∀ η e → SV η → Pos η → SV (R.run (o η e)))
  (op : ∀ η e → SV η → Pos η → Σ Ordᴵ (λ d → d ≺ᴵ R.run (o η e))) where

  module Actual = Shape.Node c t g o₀ o
  open Actual public using (η; bound; start; step; computation; outputs)

  coordinate-sv : ∀ n → SV (η n)
  coordinate-pos : ∀ n → Pos (η n)
  coordinate-sv zero = subst SV (sym start) (add-sv cs ts)
  coordinate-sv (suc n) = subst SV (sym (step n))
    (add-sv cs (gs (η n) (bound n) (coordinate-sv n) (coordinate-pos n)))
  coordinate-pos zero = subst Pos (sym start) (add-pos c _ cp)
  coordinate-pos (suc n) = subst Pos (sym (step n)) (add-pos c _ cp)

  output-sv : ∀ n → SV (outputs n)
  output-sv zero = os
  output-sv (suc n) = og (η n) (bound n) (coordinate-sv n) (coordinate-pos n)

  next-pred : ∀ n → Σ Ordᴵ (λ d → d ≺ᴵ outputs (suc n))
  next-pred n = op (η n) (bound n) (coordinate-sv n) (coordinate-pos n)

  whole-sv : SV (R.run (ĉᴸ c t g o₀ o))
  whole-sv = SV-≅ Actual.shape (complete-sv outputs output-sv next-pred)
```
