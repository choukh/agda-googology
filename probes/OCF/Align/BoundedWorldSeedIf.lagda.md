# 分支包含坐标的两层证书

此证书不同于Ready的界内位置条件。它要求值自证、分支坐标膨胀、
以及递归证书。中Ω分支只在Seed0坐标上要求膨胀及递归证书；
没有要求所有raw低层树都满足Seed0。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldSeedIf where
open import Data.Unit using (⊤)
open import Data.Product using (_×_)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V; mid)

Seed0 : HB U → Set
Seed0 hz = Value hz hz hz × ⊤
Seed0 (hs a) = Value hz (hs a) (hs a) × Seed0 a
Seed0 (hl f) = Value hz (hl f) (hl f) × (∀ n → Seed0 (f n))
Seed0 (hΩ (inj₁ ()) g)
Seed0 (hΩ (inj₂ k) g) = Value hz (hΩ (inj₂ k) g) (hΩ (inj₂ k) g) ×
  ((∀ c → Value hz (up c) (g c)) × (∀ c → Seed0 (g c)))

Seed1 : HB V → Set
Seed1 hz = Value (hs hz) hz hz × ⊤
Seed1 (hs a) = Value (hs hz) (hs a) (hs a) × Seed1 a
Seed1 (hl f) = Value (hs hz) (hl f) (hl f) × (∀ n → Seed1 (f n))
Seed1 (hΩ (inj₁ (inj₁ ())) g)
Seed1 (hΩ (inj₁ (inj₂ k)) g) = Value (hs hz) (hΩ (inj₁ (inj₂ k)) g) (hΩ (inj₁ (inj₂ k)) g) ×
  ((∀ c → Value (hs hz) (up (up c)) (g c)) × (∀ c → Seed1 (g c)))
Seed1 (hΩ (inj₂ k) g) = Value (hs hz) (hΩ (inj₂ k) g) (hΩ (inj₂ k) g) ×
  ((∀ e → Seed0 e → Value (hs hz) (up e) (g e)) × (∀ e → Seed0 e → Seed1 (g e)))

record MiddlePreservation : Set where
  field
    preserve : ∀ {b a} → Seed0 b → Seed1 a → Seed0 (mid b a)
```

MiddlePreservation待真实递归实现；后续先给floor/act/加法以及实际
Whole.Model.ce的证书。标签或记号项不参与证书。
