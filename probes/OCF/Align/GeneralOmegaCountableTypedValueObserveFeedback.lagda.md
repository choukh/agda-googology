# 原typed与逐点解释器的完整反馈耦合

本辅助只组织同一个实际低层i上的无累加链；低层与source分支的
读回由调用处原分类提供。初值是已证floor-read，不是任意假设种子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveFeedback where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; iterate)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; index-bound)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedFloor using (floor-read; self)
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

module Chain (B : Cd) (lB : LgB B) (i : Cd) (hi : hs i ⊲ B)
  {ℓ} (σ : L.Simᴵ ℓ (height B lB))
  (q : height i (lgB⊲ hi tt lB) L.<ᴵ ℓ)
  (f : L.U _ (L.<→◃ q) → L.Ordᶜ ℓ)
  (g : HB (F i) → HB (F B))
  (sub : ∀ x e → Read i (lgB⊲ hi tt lB) (canonical i (lgB⊲ hi tt lB)) x e →
    Read B lB σ (f (L.into (L.<→◃ q) x)) (g e))
  (descend : ∀ x e → Read i (lgB⊲ hi tt lB) (canonical i (lgB⊲ hi tt lB)) x e →
    Read i (lgB⊲ hi tt lB) (canonical i (lgB⊲ hi tt lB))
      (L.ψ (index-bound lB hi) σ (f (L.into (L.<→◃ q) x)))
      (point-observe B lB i (⊲ᴮ-tr (hsuc hself) hi) (g e))) where
  li = lgB⊲ hi tt lB
  old : ℕ → L.Ordᶜ (height i li)
  old = iter (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.Ω (height i li))
  new : ℕ → HB (F i)
  new = iterate (λ e → point-observe B lB i (⊲ᴮ-tr (hsuc hself) hi) (g e)) (pointFloor i)
  coordinates : ∀ n → Read i li (canonical i li) (old n) (new n)
  coordinates zero = floor-read i li
  coordinates (suc n) = rc
    (L.ψ-≅ {p = q} {σ = λ r → r} {p′ = index-bound lB hi} {σ′ = σ}
      (L.≅ᴵ-refl (height i li)) (self (sub (old n) (new n) (coordinates n))))
    (descend (old n) (new n) (coordinates n))
```

coordinates覆盖所有自然数，尚待由完整观察递归实填descend；不是独立
的最终观察定理，未把本模块的参数记录作新ψ下界。
