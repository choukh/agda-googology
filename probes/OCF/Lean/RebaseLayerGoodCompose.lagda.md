# 递归Good采样关系的全层传递

目标坐标的准入为Good。vor/vo直接消费这一证书，vo/vo从配对的
左端Good取对角；不要求raw全域自证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerGoodCompose where
open import OCF.Lean.CRwBase
open import OCF.Lean.RebaseLayerIf using (vz; vs; vr; vl; vli; vo; vor)
open import OCF.Lean.RebaseLayerGoodIf
open import OCF.Lean.RebaseLayerGoodDomain using (diagonal; left)
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

```
