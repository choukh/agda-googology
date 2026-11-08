# 对加法封闭域统一证明重定位比较

证明和准入谓词P的具体来源无关。Ω处需要的捕获槽证据由add-closed
给出，其余结构递归直接消费源关系，不从比较反演Good。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseDomainRun where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.RebaseLayerIf using (vz; vs; vr; vl; vli; vo; vor)
open import OCF.Lean.RebaseLayerClosure using (add; prefix)
open import OCF.Lean.GeneralRebaseSampleRun using (right)
import OCF.Lean.GeneralRebaseDomainIf as I

module Layer (S : KS) (A : ∀ κ → E S κ → Set)
  (Q : ∀ κ → E S κ → E S κ → Set) (P : HB S → Set)
  (D : I.Layer.Domain S A Q P) where
  open I.Layer S A Q P
  open Domain D using (add-closed)

  mono : ∀ {a b u v} → R⁺ a b → R u v → P u → P v → R⁺ (enc u a) (enc v b)
  mono vz uv pu pv = vz
  mono (vs p) uv pu pv = vs (mono p uv pu pv)
  mono (vr p) uv pu pv = vr (mono p uv pu pv)
  mono (vl p) uv pu pv = vl (λ n → mono (p n) uv pu pv)
  mono (vli n p) uv pu pv = vli n (mono p uv pu pv)
  mono (vo {κ = inj₁ κ} p) uv pu pv = vo (λ x y xy → mono (p x y xy) uv pu pv)
  mono {u = u} {v} (vo {κ = inj₂ _} p) uv pu pv = vo λ x y xy →
    let uv′ = add uv (proj₁ xy)
        pu′ = add-closed pu (proj₁ (proj₂ xy))
        pv′ = add-closed pv (proj₂ (proj₂ xy))
    in mono (p (u ⊞ x) (v ⊞ y) (uv′ , pu′ , pv′)) uv′ pu′ pv′
  mono (vor {κ = inj₁ κ} p) uv pu pv = vor (λ e se → mono (p e se) uv pu pv)
  mono {v = v} (vor {κ = inj₂ _} p) uv pu pv = vor λ e se →
    mono (p (v ⊞ e) (add-closed pv se)) (prefix uv e) pu (add-closed pv se)

  inflate : ∀ {a b} → R⁺ a b → ∀ m → P m → R⁺ a (enc m b)
  inflate vz m pm = vz
  inflate (vs p) m pm = vs (inflate p m pm)
  inflate (vr p) m pm = vr (inflate p m pm)
  inflate (vl p) m pm = vl (λ n → inflate (p n) m pm)
  inflate (vli n p) m pm = vli n (inflate p m pm)
  inflate (vo {κ = inj₁ κ} p) m pm = vo (λ x y xy → inflate (p x y xy) m pm)
  inflate (vo {κ = inj₂ _} p) m pm = vo λ x y xy →
    let py = add-closed pm (proj₂ (proj₂ xy))
    in inflate (p x (m ⊞ y) (right m (proj₁ xy) , proj₁ (proj₂ xy) , py)) (m ⊞ y) py
  inflate (vor {κ = inj₁ κ} p) m pm = vor (λ e se → inflate (p e se) m pm)
  inflate (vor {κ = inj₂ _} p) m pm = vor λ e se →
    inflate (p (m ⊞ e) (add-closed pm se)) (m ⊞ e) (add-closed pm se)

  instance-comparison : Comparison
  instance-comparison = record { mono = mono; inflate = inflate }
```
