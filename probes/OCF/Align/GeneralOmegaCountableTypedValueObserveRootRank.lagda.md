# 零根的原秩反馈完整列

本篇将原source分支递归结果组织成完整零根结果。秩零时实际same
反馈使用root的原pt；非零秩使用原pi诱导的内部路径，二者不混同。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveRootRank where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; iterate; module C)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe; point-node)
open import OCF.Lean.GeneralOmegaCountableObserveZeroPath using (zero-decision)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; index-bound)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedFloor using (floor-read; self)
open import OCF.Align.GeneralOmegaCountableTypedZero using (zero-reflect)
import OCF.Align.GeneralOmegaCountableTypedValueObserveFeedback as Fd
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as Z
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

module Rank (B : Cd) (lB : LgB B) (pt : hz ⊲ B)
  (i : Cd) (pi : hs i ⊲ B) {ℓ} (σ : L.Simᴵ ℓ (height B lB))
  (q : height i (lgB⊲ pi tt lB) L.<ᴵ ℓ)
  (f : L.U _ (L.<→◃ q) → L.Ordᶜ ℓ)
  (g : HB (F i) → HB (F B))
  (sub : ∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Read B lB σ (f (L.into (L.<→◃ q) x)) (g e))
  (low : ∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB))
      (L.ψ (index-bound lB pi) σ (f (L.into (L.<→◃ q) x)))
      (point-observe B lB i (⊲ᴮ-tr (hsuc hself) pi) (g e)))
  (root : ∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    L.ψ⁰ (f (L.into (L.<→◃ q) x)) L.≅ Z.read (point-observe B lB hz pt (g e))) where
  module Chain = Fd.Chain B lB i pi σ q f g sub low
  above-outputs : ∀ n → L.ψ⁰ (f (L.into (L.<→◃ q) (Chain.old n))) L.≅
    Z.read (point-observe B lB hz pt (g (Chain.new n)))
  above-outputs n = root (Chain.old n) (Chain.new n) (Chain.coordinates n)
```

above-outputs不改变原反馈seed，也不宣称root或low已经对所有source
实现。它供总递归的非零秩子句消费，小子树前提由递归调用填入。

```agda
import OCF.Align.GeneralOmegaCountableTypedProofRun as Proof
open import OCF.Align.GeneralOmegaCountableTypedProofIf using (proof-shape)
module ZeroRank (B : Cd) (lB : LgB B) (pt : hz ⊲ B)
  (pi : hs hz ⊲ B) {ℓ} (σ : L.Simᴵ ℓ (height B lB))
  (q : L.zero L.<ᴵ ℓ)
  (f : L.U _ (L.<→◃ q) → L.Ordᶜ ℓ)
  (g : Cd → HB (F B))
  (sub : ∀ x e → Read hz (lgB⊲ pi tt lB) (canonical hz (lgB⊲ pi tt lB)) x e →
    Read B lB σ (f (L.into (L.<→◃ q) x)) (g e))
  (root : ∀ x e → Read hz (lgB⊲ pi tt lB) (canonical hz (lgB⊲ pi tt lB)) x e →
    L.ψ⁰ (f (L.into (L.<→◃ q) x)) L.≅ Z.read (point-observe B lB hz pt (g e))) where
  li = lgB⊲ pi tt lB
  old : ℕ → L.Ordᶜ L.zero
  old = iter (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.suc L.zero)
  new : ℕ → Cd
  new = iterate (λ e → point-observe B lB hz pt (g e)) (hs hz)
  coordinates : ∀ n → Read hz li (canonical hz li) (old n) (new n)
  coordinates zero = floor-read hz li
  coordinates (suc n) = rc
    (L.≅-sym (L.ψ⁰≅ψ {p = q} {σ = λ r → r}
      (self (sub (old n) (new n) (coordinates n)))))
    (rc (L.≅-sym (L.tr⁻-≅ (proof-shape hz li tt)
      (L.ψ⁰-≅ (self (sub (old n) (new n) (coordinates n))))))
      (Proof.transport hz li tt (zero-reflect (root (old n) (new n) (coordinates n)))))
  outputs : ∀ n → L.ψ⁰ (f (L.into (L.<→◃ q) (old n))) L.≅
    Z.read (point-observe B lB hz pt (g (new n)))
  outputs n = root (old n) (new n) (coordinates n)
```
