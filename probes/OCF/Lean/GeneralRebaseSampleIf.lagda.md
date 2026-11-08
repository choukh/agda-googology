# 有证坐标域上的统一重定位接口

新采样关系把顶层坐标限制在低层自证树。编码仍是原来的一步重定位，
单调律额外携捕获槽两端自证，膨胀律携捕获槽自证；这正是新域的要求。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseSampleIf where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.RebaseLayerIf using (SampleValue)
import OCF.Lean.GeneralRebaseIf as G

module Layer (S : KS) (A : ∀ κ → E S κ → Set)
  (Q : ∀ κ → E S κ → E S κ → Set) where
  R : HB S → HB S → Set
  R = SampleValue S A Q
  A⁺ : ∀ κ → E (step S) κ → Set
  A⁺ (inj₁ κ) = A κ
  A⁺ (inj₂ _) e = R e e
  Q⁺ : ∀ κ → E (step S) κ → E (step S) κ → Set
  Q⁺ (inj₁ κ) = Q κ
  Q⁺ (inj₂ _) x y = R x y × (R x x × R y y)
  R⁺ : HB (step S) → HB (step S) → Set
  R⁺ = SampleValue (step S) A⁺ Q⁺
  enc : HB S → HB (step S) → HB (step S)
  enc = G.Layer.enc S Q

  record Comparison : Set where
    field
      mono : ∀ {a b u v} → R⁺ a b → R u v → R u u → R v v →
        R⁺ (enc u a) (enc v b)
      inflate : ∀ {a b} → R⁺ a b → ∀ m → R m m → R⁺ a (enc m b)
```

律只比较固定类型树的给定有向关系，不提供下标判等或三歧。
它没有要求一般raw坐标自证，没有修改原树、合法性或旧比较关系。
