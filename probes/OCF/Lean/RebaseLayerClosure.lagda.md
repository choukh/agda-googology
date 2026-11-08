# 有证采样关系的传递与原生成算子闭包

传递的vor/vo情形实际消费目标坐标的Admit，再在同一点配对。
这只修复本结构关系的组合问题，不宣称高层序数值不能自反。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerClosure where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.RebaseLayerIf
open import OCF.Align.BoundedWorldCoverIf using (act)

diagonal : ∀ c κ e → Admit c κ e → Coord c κ e e
diagonal hz (inj₁ ()) e a
diagonal hz (inj₂ _) e a = ≤-refl e
diagonal (hs c) (inj₁ κ) e a = diagonal c κ e a
diagonal (hs c) (inj₂ _) e a = a , a , a
diagonal (hl f) (n , κ) e a = diagonal (f n) κ e a
left : ∀ c κ {x y} → Coord c κ x y → Admit c κ x
left hz (inj₁ ()) p
left hz (inj₂ _) p = tt
left (hs c) (inj₁ κ) p = left c κ p
left (hs c) (inj₂ _) p = proj₁ (proj₂ p)
left (hl f) (n , κ) p = left (f n) κ p

compose : ∀ c {a b d} → Value c a b → Value c b d → Value c a d
compose c vz q = vz
compose c p (vr q) = vr (compose c p q)
compose c p (vli n q) = vli n (compose c p q)
compose c p (vor q) = vor (λ e se → compose c p (q e se))
compose c (vl p) q = vl (λ n → compose c (p n) q)
compose c (vs p) (vs q) = vs (compose c p q)
compose c (vr p) (vs q) = vr (compose c p q)
compose c (vli n p) (vl q) = compose c p (q n)
compose c (vo {κ = κ} p) (vo q) = vo (λ x z xz →
  compose c (p x x (diagonal c κ x (left c κ xz))) (q x z xz))
compose c (vor {κ = κ} p) (vo q) = vor (λ z sz →
  compose c (p z sz) (q z z (diagonal c κ z sz)))

prefix : ∀ {S A Q a b} → SampleValue S A Q a b → ∀ d → SampleValue S A Q a (b ⊞ d)
prefix p hz = p
prefix p (hs d) = vr (prefix p d)
prefix p (hl f) = vli 0 (prefix p (f 0))
prefix p (hΩ κ g) = vor (λ e se → prefix p (g e))
add : ∀ {S A Q a b c d} → SampleValue S A Q a b → SampleValue S A Q c d →
  SampleValue S A Q (a ⊞ c) (b ⊞ d)
add p vz = prefix p _
add p (vs q) = vs (add p q)
add p (vr q) = vr (add p q)
add p (vl q) = vl (λ n → add p (q n))
add p (vli n q) = vli n (add p q)
add p (vo q) = vo (λ x y xy → add p (q x y xy))
add p (vor q) = vor (λ e se → add p (q e se))
repeat : ∀ {S A Q a b} → SampleValue S A Q a b → ∀ n →
  SampleValue S A Q (mul a n) (mul b n)
repeat p zero = p
repeat p (suc n) = add (repeat p n) p
positive : ∀ {S A Q} (a : HB S) → SampleValue S A Q (hs hz) (act a)
positive hz = vs vz
positive (hs a) = vli 0 (positive a)
positive (hl f) = vli 0 (positive (f 0))
positive (hΩ κ g) = vor (λ e se → positive (g e))
act-mono : ∀ {S A Q a b} → SampleValue S A Q a b → SampleValue S A Q (act a) (act b)
act-mono {b = b} vz = positive b
act-mono (vs p) = vl (λ n → vli n (repeat (act-mono p) n))
act-mono (vr p) = vli 0 (act-mono p)
act-mono (vl p) = vl (λ n → act-mono (p n))
act-mono (vli n p) = vli n (act-mono p)
act-mono (vo p) = vo (λ x y xy → act-mono (p x y xy))
act-mono (vor p) = vor (λ e se → act-mono (p e se))
```

这里没有从单向关系提取端点自证。需要自证时，必须由具体生成闭包
另行给出；后续原fold的采样证明也仍需这项信息。
