# 加法重定位保有向值关系

这里直接消费完整 Value1，包括中Ω统一右规则；没有要求任意raw树自相关。
所有结论是固定树类型的值关系，不判定下标或更新槽。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldRebaseRun where
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; prefix-rel; right-rel)
open import OCF.Align.BoundedWorldRebaseIf

mono : ∀ {a b u v} → Value (hs hz) a b → Value hz u v →
  Value (hs hz) (enc u a) (enc v b)
mono vz uv = vz
mono (vs p) uv = vs (mono p uv)
mono (vr p) uv = vr (mono p uv)
mono (vl p) uv = vl (λ n → mono (p n) uv)
mono (vli n p) uv = vli n (mono p uv)
mono (vo {κ = inj₁ (inj₁ ())} p) uv
mono (vo {κ = inj₁ (inj₂ _)} p) uv = vo (λ x y xy → mono (p x y xy) uv)
mono {u = u} {v} (vo {κ = inj₂ _} p) uv =
  vo (λ x y xy → mono (p (u ⊞ x) (v ⊞ y) (add-rel uv xy)) (add-rel uv xy))
mono (vor {κ = inj₁ (inj₁ ())} p) uv
mono (vor {κ = inj₁ (inj₂ _)} p) uv = vor (λ c → mono (p c) uv)
mono {v = v} (vor {κ = inj₂ _} p) uv =
  vor (λ e → mono (p (v ⊞ e)) (prefix-rel uv e))

inflate : ∀ {a b} → Value (hs hz) a b → ∀ m → Value (hs hz) a (enc m b)
inflate vz m = vz
inflate (vs p) m = vs (inflate p m)
inflate (vr p) m = vr (inflate p m)
inflate (vl p) m = vl (λ n → inflate (p n) m)
inflate (vli n p) m = vli n (inflate p m)
inflate (vo {κ = inj₁ (inj₁ ())} p) m
inflate (vo {κ = inj₁ (inj₂ _)} p) m = vo (λ x y xy → inflate (p x y xy) m)
inflate (vo {κ = inj₂ _} p) m =
  vo (λ x y xy → inflate (p x (m ⊞ y) (right-rel m xy)) (m ⊞ y))
inflate (vor {κ = inj₁ (inj₁ ())} p) m
inflate (vor {κ = inj₁ (inj₂ _)} p) m = vor (λ c → inflate (p c) m)
inflate (vor {κ = inj₂ _} p) m = vor (λ e → inflate (p (m ⊞ e)) (m ⊞ e))
```

中Ω配对使用两份坐标加法关系；中Ω统一右规则使用捕获槽到其右加坐标
的前缀关系。此证明不需要函数外延，也没有把 Same 当成任意折叠同余。
