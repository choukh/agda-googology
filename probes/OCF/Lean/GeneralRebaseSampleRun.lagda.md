# 自证捕获槽足以保存准入域

顶层访问坐标从e变成b⊞e；两者的低层自证由加法闭包给出。
完整证明覆盖Ω配对与准入域统一右规则，未把后者换回全raw规则。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseSampleRun where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.RebaseLayerIf using (SampleValue; vz; vs; vr; vl; vli; vo; vor)
open import OCF.Lean.RebaseLayerClosure using (add; prefix)
import OCF.Lean.GeneralRebaseSampleIf as I

relabel : ∀ {S A A′ Q Q′ a b} →
  (∀ κ e → A′ κ e → A κ e) → (∀ κ x y → Q′ κ x y → Q κ x y) →
  SampleValue S A Q a b → SampleValue S A′ Q′ a b
relabel ad to vz = vz
relabel ad to (vs p) = vs (relabel ad to p)
relabel ad to (vr p) = vr (relabel ad to p)
relabel ad to (vl p) = vl (λ n → relabel ad to (p n))
relabel ad to (vli n p) = vli n (relabel ad to p)
relabel ad to (vo {κ = κ} p) = vo (λ x y xy → relabel ad to (p x y (to κ x y xy)))
relabel ad to (vor {κ = κ} p) = vor (λ e se → relabel ad to (p e (ad κ e se)))

right : ∀ {S A Q} (a : HB S) {b c} → SampleValue S A Q b c →
  SampleValue S A Q b (a ⊞ c)
right a vz = vz
right a (vs p) = vs (right a p)
right a (vr p) = vr (right a p)
right a (vl p) = vl (λ n → right a (p n))
right a (vli n p) = vli n (right a p)
right a (vo p) = vo (λ x y xy → right a (p x y xy))
right a (vor p) = vor (λ e se → right a (p e se))

module Layer (S : KS) (A : ∀ κ → E S κ → Set)
  (Q : ∀ κ → E S κ → E S κ → Set) where
  open I.Layer S A Q

  mono : ∀ {a b u v} → R⁺ a b → R u v → R u u → R v v →
    R⁺ (enc u a) (enc v b)
  mono vz uv uu vv = vz
  mono (vs p) uv uu vv = vs (mono p uv uu vv)
  mono (vr p) uv uu vv = vr (mono p uv uu vv)
  mono (vl p) uv uu vv = vl (λ n → mono (p n) uv uu vv)
  mono (vli n p) uv uu vv = vli n (mono p uv uu vv)
  mono (vo {κ = inj₁ κ} p) uv uu vv = vo (λ x y xy → mono (p x y xy) uv uu vv)
  mono {u = u} {v} (vo {κ = inj₂ _} p) uv uu vv = vo λ x y xy →
    let uv′ = add uv (proj₁ xy)
        uu′ = add uu (proj₁ (proj₂ xy))
        vv′ = add vv (proj₂ (proj₂ xy))
    in mono (p (u ⊞ x) (v ⊞ y) (uv′ , uu′ , vv′)) uv′ uu′ vv′
  mono (vor {κ = inj₁ κ} p) uv uu vv = vor (λ e se → mono (p e se) uv uu vv)
  mono {v = v} (vor {κ = inj₂ _} p) uv uu vv = vor λ e se →
    mono (p (v ⊞ e) (add vv se)) (prefix uv e) uu (add vv se)

  inflate : ∀ {a b} → R⁺ a b → ∀ m → R m m → R⁺ a (enc m b)
  inflate vz m sm = vz
  inflate (vs p) m sm = vs (inflate p m sm)
  inflate (vr p) m sm = vr (inflate p m sm)
  inflate (vl p) m sm = vl (λ n → inflate (p n) m sm)
  inflate (vli n p) m sm = vli n (inflate p m sm)
  inflate (vo {κ = inj₁ κ} p) m sm = vo (λ x y xy → inflate (p x y xy) m sm)
  inflate (vo {κ = inj₂ _} p) m sm = vo λ x y xy →
    let sy = add sm (proj₂ (proj₂ xy))
    in inflate (p x (m ⊞ y) (right m (proj₁ xy) , proj₁ (proj₂ xy) , sy)) (m ⊞ y) sy
  inflate (vor {κ = inj₁ κ} p) m sm = vor (λ e se → inflate (p e se) m sm)
  inflate (vor {κ = inj₂ _} p) m sm = vor λ e se →
    inflate (p (m ⊞ e) (add sm se)) (m ⊞ e) (add sm se)

  instance-comparison : Comparison
  instance-comparison = record { mono = mono; inflate = inflate }
```

这一层的证明不使用传递，也没有从有向关系反演任意端点自证。
下一步实际运行器必须独立证明它访问的坐标确实有这些证据。
