# 原根Ω节点的完整读回

按原cl秩分解，根的same零秩与above非零秩使用各自完整轨道。
本篇只封闭Root子句，内部keep/same/above仍由总节点实现负责。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveRootNode where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; module C; classify)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe; point-node)
open import OCF.Lean.GeneralOmegaCountableObserveZeroPath using (zero-decision)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedClass using (cast; ClassLink; linked; class-link)
open import OCF.Align.GeneralOmegaCountableTypedValueObserveRecursor using (Result)
import OCF.Align.GeneralOmegaCountableTypedValueObserveRootRank as R
import OCF.Align.GeneralOmegaCountableTypedValueObserveZeroNode as ZN
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as Z

at-rank : ∀ B lB (pt : hz ⊲ B) (i : Cd) (pi : hs i ⊲ B) j
  (eq : j ≡ height i (lgB⊲ pi tt lB)) {ℓ A}
  (σ : L.Simᴵ ℓ (height B lB)) (q : j L.<ᴵ ℓ)
  (f : L.U j (L.<→◃ q) → L.Ordᶜ ℓ) (g : A → HB (F B)) (encode : HB (F i) → A)
  (sub : ∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Read B lB σ (f (L.into (L.<→◃ q) (cast (sym eq) x))) (g (encode e))) →
  (∀ x e → Read i (lgB⊲ pi tt lB) (canonical i (lgB⊲ pi tt lB)) x e →
    Result B lB σ (f (L.into (L.<→◃ q) (cast (sym eq) x))) (g (encode e))) →
  L.ψ⁰ (L.limᵢ q f) L.≅ Z.read (point-node pt (zero-decision i pi encode)
    (λ t p e → point-observe B lB t p (g e)))
at-rank B lB pt hz pi ._ refl σ q f g encode sub ih = L.l≅ Chain.outputs
  where
  module Chain = R.ZeroRank B lB pt pi σ q f (λ e → g (encode e)) sub
    (λ x e r → Result.root (ih x e r) pt)
at-rank B lB pt (hs i) pi ._ refl σ q f g encode sub ih = L.l≅ Chain.above-outputs
  where
  module Chain = R.Rank B lB pt (hs i) pi σ q f (λ e → g (encode e)) sub
    (λ x e r → Result.internal (ih x e r) (hs i) pi)
    (λ x e r → Result.root (ih x e r) pt)
at-rank B lB pt (hl h) pi ._ refl σ q f g encode sub ih = L.l≅ Chain.above-outputs
  where
  module Chain = R.Rank B lB pt (hl h) pi σ q f (λ e → g (encode e)) sub
    (λ x e r → Result.internal (ih x e r) (hl h) pi)
    (λ x e r → Result.root (ih x e r) pt)
at-rank B lB pt (hΩ () h) pi j eq σ q f g encode sub ih

root-link : ∀ B lB (pt : hz ⊲ B) {ℓ} (σ : L.Simᴵ ℓ (height B lB)) κ
  (q : rank B lB κ L.<ᴵ ℓ) {f g v} → (link : ClassLink B lB κ v) →
  (∀ x e → Coord B lB κ x e → Read B lB σ (f (L.into (L.<→◃ q) x)) (g e)) →
  (∀ x e → Coord B lB κ x e → Result B lB σ (f (L.into (L.<→◃ q) x)) (g e)) →
  L.ψ⁰ (L.limᵢ q f) L.≅ Z.read (ZN.normal-point-node pt v (λ t p e → point-observe B lB t p (g e)))
root-link B lB pt σ κ q {f} {g} (linked {i} {pi} {encode} eq feed) sub ih =
  at-rank B lB pt i pi _ eq σ q f g encode
    (λ x e r → sub _ _ (feed r)) (λ x e r → ih _ _ (feed r))

node-root : ∀ B lB {ℓ} (σ : L.Simᴵ ℓ (height B lB)) κ
  (q : rank B lB κ L.<ᴵ ℓ) {f g} →
  (∀ x e → Coord B lB κ x e → Read B lB σ (f (L.into (L.<→◃ q) x)) (g e)) →
  (∀ x e → Coord B lB κ x e → Result B lB σ (f (L.into (L.<→◃ q) x)) (g e)) →
  ∀ pt → L.ψ⁰ (L.limᵢ q f) L.≅ Z.read (point-observe B lB hz pt (hΩ κ g))
node-root B lB σ κ q {f} {g} sub ih pt rewrite
  ZN.normalize-point-node lB pt (C.cl B κ) (λ t p e → point-observe B lB t p (g e)) =
  root-link B lB pt σ κ q {f = f} {g = g} (class-link B lB κ) sub ih
```
