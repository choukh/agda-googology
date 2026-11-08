# 完整Read递归的节点边界

本篇把全部非Ω构造的原观察递归编译，并明确Ω整节点仍须提供的
字段。实例化Nodes之前不导出无条件RootObservation，也不计新值界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveRecursor where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; leftMul)
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-observe)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; index-bound)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedFloor using (floor-read)
open import OCF.Align.GeneralOmegaCountableTypedValueObserveClosure using (mul)
import OCF.Align.GeneralOmegaCountableNextValueOrbit as Pure
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as Z

record Result (B : Cd) (lB : LgB B) {ℓ} (σ : L.Simᴵ ℓ (height B lB))
  (a : L.Ordᶜ ℓ) (b : HB (F B)) : Set where
  field
    internal : ∀ t (ht : hs t ⊲ B) →
      Read t (lgB⊲ ht tt lB) (canonical t (lgB⊲ ht tt lB))
        (L.ψ (index-bound lB ht) σ a)
        (point-observe B lB t (⊲ᴮ-tr (hsuc hself) ht) b)
    root : ∀ (pt : hz ⊲ B) → L.ψ⁰ a L.≅ Z.read (point-observe B lB hz pt b)
open Result

record Nodes : Set₁ where
  field
    node : ∀ B lB {ℓ} (σ : L.Simᴵ ℓ (height B lB)) κ
      (q : rank B lB κ L.<ᴵ ℓ) {f g} → σ q ≡ bound B lB κ →
      L.limᵢ q f L.≅ L.limᵢ q f →
      (∀ x e → Coord B lB κ x e → Read B lB σ (f (L.into (L.<→◃ q) x)) (g e)) →
      (∀ x e → Coord B lB κ x e → Result B lB σ (f (L.into (L.<→◃ q) x)) (g e)) →
      Result B lB σ (L.limᵢ q f) (hΩ κ g)

module Build (nodes : Nodes) where
  build : ∀ {B lB ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Read B lB σ a b → Result B lB σ a b
  internal (build rz) t ht = floor-read t _
  root (build rz) pt = L.s≅ L.z≅
  internal (build (rs r)) t ht = rl (mul (internal (build r) t ht))
  root (build {B} {lB} (rs {b = b} r)) pt = L.l≅
    (Pure.leftC {b = point-observe B lB hz pt b} (root (build r) pt))
  internal (build (rl r)) t ht = rl (λ n → internal (build (r n)) t ht)
  root (build (rl r)) pt = L.l≅ (λ n → root (build (r n)) pt)
  internal (build {B} {lB} {σ = σ} (ro κ q eq sa r)) t ht =
    internal (Nodes.node nodes B lB σ κ q eq sa r (λ x e c → build (r x e c))) t ht
  root (build {B} {lB} {σ = σ} (ro κ q eq sa r)) pt =
    root (Nodes.node nodes B lB σ κ q eq sa r (λ x e c → build (r x e c))) pt
  internal (build (ru-s r)) t ht = internal (build r) t ht
  root (build (ru-s r)) pt = root (build r) pt
  internal (build (ru-l r)) t ht = internal (build r) t ht
  root (build (ru-l r)) pt = root (build r) pt
  internal (build (rc e r)) t ht = rc (L.ψ-≅ (L.≅ᴵ-refl _) e) (internal (build r) t ht)
  root (build (rc e r)) pt = L.≅-trans (L.ψ⁰-≅ e) (root (build r) pt)
```

Result.root量化任意原pt，故零秩反馈不需假设输入右树Rel自反或任意
路径无关。Nodes是唯一尚待封闭的整节点字段，不在本篇假定有实例。
