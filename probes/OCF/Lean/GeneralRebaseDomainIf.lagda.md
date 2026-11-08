# 重定位只需坐标准入域对加法封闭

把自证域推广为任意树侧准入谓词P。顶层坐标携P，比较同时携两端P。
捕获槽随访问坐标一同增长，所以唯一新增域要求是加法封闭。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseDomainIf where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.RebaseLayerIf using (SampleValue)
import OCF.Lean.GeneralRebaseIf as G

module Layer (S : KS) (A : ∀ κ → E S κ → Set)
  (Q : ∀ κ → E S κ → E S κ → Set) (P : HB S → Set) where
  R : HB S → HB S → Set
  R = SampleValue S A Q
  A⁺ : ∀ κ → E (step S) κ → Set
  A⁺ (inj₁ κ) = A κ
  A⁺ (inj₂ _) = P
  Q⁺ : ∀ κ → E (step S) κ → E (step S) κ → Set
  Q⁺ (inj₁ κ) = Q κ
  Q⁺ (inj₂ _) x y = R x y × (P x × P y)
  R⁺ : HB (step S) → HB (step S) → Set
  R⁺ = SampleValue (step S) A⁺ Q⁺
  enc : HB S → HB (step S) → HB (step S)
  enc = G.Layer.enc S Q

  record Domain : Set where
    field
      add-closed : ∀ {a b} → P a → P b → P (a ⊞ b)
  record Comparison : Set where
    field
      mono : ∀ {a b u v} → R⁺ a b → R u v → P u → P v → R⁺ (enc u a) (enc v b)
      inflate : ∀ {a b} → R⁺ a b → ∀ m → P m → R⁺ a (enc m b)
```

没有要求P在所有raw上成立，也没有要求可判定。Domain及Comparison
须在同一P下实例化；后续用已经有原地板实例的Good，避免空前提。
