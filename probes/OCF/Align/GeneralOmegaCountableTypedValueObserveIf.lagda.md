# 内部准入目标与根零的完整观察接口

内部目标保留原hs t⊲B及由它取得的合法证；根零不要求这条严格
准入。下面两个字段尚须实际实现，接口本身不计为ψ强度结果。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveIf where
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; index-bound)
open import OCF.Align.GeneralOmegaCountableTypedIf
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as Z

record FullObservation : Set₁ where
  field
    internal : ∀ B (lB : LgB B) t (ht : hs t ⊲ B)
      {ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Read B lB σ a b →
      Read t (lgB⊲ ht tt lB) (canonical t (lgB⊲ ht tt lB))
        (L.ψ (index-bound lB ht) σ a)
        (point-observe B lB t (⊲ᴮ-tr (hsuc hself) ht) b)
    root : ∀ B lB {ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Read B lB σ a b →
      L.ψ⁰ a L.≅ Z.read (point-observe B lB hz (z⊲ᴮ B) b)
```

非空输入由TypedFloor.floor-read提供所有合法B的原pointFloor；
TypedZero.root-zero已覆盖B=0的全部Read。本篇没有假定其他字段成立。
