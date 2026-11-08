# 一步重定位的统一有向比较

所有种类结构与坐标关系共用一个证明。加法的三个关系律按关系推导
证明，顶层 Ω 配对与统一右规则分别消费这些律，不消去任意 Ω 坐标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseRun where
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedCompletionUniformIf using (TreeValue; vz; vs; vr; vl; vli; vo; vor)
import OCF.Lean.GeneralRebaseIf as I

restrict-coordinates : ∀ {S Q Q′ a b} →
  (∀ κ x y → Q′ κ x y → Q κ x y) → TreeValue S Q a b → TreeValue S Q′ a b
restrict-coordinates to vz = vz
restrict-coordinates to (vs p) = vs (restrict-coordinates to p)
restrict-coordinates to (vr p) = vr (restrict-coordinates to p)
restrict-coordinates to (vl p) = vl (λ n → restrict-coordinates to (p n))
restrict-coordinates to (vli n p) = vli n (restrict-coordinates to p)
restrict-coordinates to (vo {κ = κ} p) =
  vo (λ x y xy → restrict-coordinates to (p x y (to κ x y xy)))
restrict-coordinates to (vor p) = vor (λ c → restrict-coordinates to (p c))

prefix : ∀ {S Q a b} → TreeValue S Q a b → ∀ c → TreeValue S Q a (b ⊞ c)
prefix p hz = p
prefix p (hs c) = vr (prefix p c)
prefix p (hl f) = vli 0 (prefix p (f 0))
prefix p (hΩ κ g) = vor (λ c → prefix p (g c))

right : ∀ {S Q} (a : HB S) {b c} → TreeValue S Q b c → TreeValue S Q b (a ⊞ c)
right a vz = vz
right a (vs p) = vs (right a p)
right a (vr p) = vr (right a p)
right a (vl p) = vl (λ n → right a (p n))
right a (vli n p) = vli n (right a p)
right a (vo p) = vo (λ x y xy → right a (p x y xy))
right a (vor p) = vor (λ c → right a (p c))

add : ∀ {S Q a b c d} → TreeValue S Q a b → TreeValue S Q c d →
  TreeValue S Q (a ⊞ c) (b ⊞ d)
add p vz = prefix p _
add p (vs q) = vs (add p q)
add p (vr q) = vr (add p q)
add p (vl q) = vl (λ n → add p (q n))
add p (vli n q) = vli n (add p q)
add p (vo q) = vo (λ x y xy → add p (q x y xy))
add p (vor q) = vor (λ c → add p (q c))

module Layer (S : KS) (Q : ∀ κ → E S κ → E S κ → Set) where
  open I.Layer S Q

  mono : ∀ {a b u v} → R⁺ a b → R u v → R⁺ (enc u a) (enc v b)
  mono vz uv = vz
  mono (vs p) uv = vs (mono p uv)
  mono (vr p) uv = vr (mono p uv)
  mono (vl p) uv = vl (λ n → mono (p n) uv)
  mono (vli n p) uv = vli n (mono p uv)
  mono (vo {κ = inj₁ κ} p) uv = vo (λ x y xy → mono (p x y xy) uv)
  mono {u = u} {v} (vo {κ = inj₂ _} p) uv =
    vo (λ x y xy → mono (p (u ⊞ x) (v ⊞ y) (add uv xy)) (add uv xy))
  mono (vor {κ = inj₁ κ} p) uv = vor (λ e → mono (p e) uv)
  mono {v = v} (vor {κ = inj₂ _} p) uv =
    vor (λ e → mono (p (v ⊞ e)) (prefix uv e))

  inflate : ∀ {a b} → R⁺ a b → ∀ m → R⁺ a (enc m b)
  inflate vz m = vz
  inflate (vs p) m = vs (inflate p m)
  inflate (vr p) m = vr (inflate p m)
  inflate (vl p) m = vl (λ n → inflate (p n) m)
  inflate (vli n p) m = vli n (inflate p m)
  inflate (vo {κ = inj₁ κ} p) m = vo (λ x y xy → inflate (p x y xy) m)
  inflate (vo {κ = inj₂ _} p) m =
    vo (λ x y xy → inflate (p x (m ⊞ y) (right m xy)) (m ⊞ y))
  inflate (vor {κ = inj₁ κ} p) m = vor (λ e → inflate (p e) m)
  inflate (vor {κ = inj₂ _} p) m = vor (λ e → inflate (p (m ⊞ e)) (m ⊞ e))

  instance-comparison : Comparison
  instance-comparison = record { mono = mono; inflate = inflate }
```

证明直接对给定有向推导递归；没有从单向关系抽取端点自反。不同的底层
S 不新增证明子句。此结果尚不说明任意多槽折叠都消费同一编码。
