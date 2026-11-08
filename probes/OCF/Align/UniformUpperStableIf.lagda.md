# 带自证中间项的采样关系

本篇另开关系，不修改已冻结 UniformUpperIf。传递记录中间树的
VRel自证；context记录目标前缀自证，供加法闭包递归使用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformUpperStableIf where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedCompletionTerminalValueIf using (VRel; U)
open import OCF.Align.BoundedCompletionTerminalValueClosure using (floor)

data Core : HB U → HB U → Set where
  lift : ∀ {a b} → VRel a b → Core a b
  unit : Core (hs hz) floor
  succ : ∀ {a b} → Core a b → Core (hs a) (hs b)
  right : ∀ {a b} → Core a b → Core a (hs b)
  all : ∀ {f b} → (∀ n → Core (f n) b) → Core (hl f) b
  pick : ∀ {a f} n → Core a (f n) → Core a (hl f)
  omega : ∀ {f g : Cd → HB U} → (∀ {c d} → c ≤ᵛ d → Core (f c) (g d)) →
    Core (hΩ (inj₂ tt) f) (hΩ (inj₂ tt) g)
  uniform : ∀ {a g} → (∀ c → Core a (g c)) → Core a (hΩ (inj₂ tt) g)
  context : ∀ {a b} → Core a b → VRel b b → Core (hs a) (b ⊞ floor)
  through : ∀ {a b c} → VRel b b → Core a b → Core b c → Core a c
```
