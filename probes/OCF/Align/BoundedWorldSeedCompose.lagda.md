# 第零原生层的有向合成

只合成固定Native0上的值关系。Ω坐标是Cd，取同一中间坐标时使用
Cd值序自反；没有对任意高层坐标假定Value自证或三歧。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldSeedCompose where
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Align.BoundedCompletionUniformIf

trans0 : ∀ {a b c} → Value hz a b → Value hz b c → Value hz a c
trans0 vz q = vz
trans0 p (vr q) = vr (trans0 p q)
trans0 p (vli n q) = vli n (trans0 p q)
trans0 p (vor q) = vor (λ c → trans0 p (q c))
trans0 (vl p) q = vl (λ n → trans0 (p n) q)
trans0 (vs p) (vs q) = vs (trans0 p q)
trans0 (vr p) (vs q) = vr (trans0 p q)
trans0 (vli n p) (vl q) = trans0 p (q n)
trans0 (vo {κ = inj₁ ()} p) q
trans0 (vo {κ = inj₂ _} p) (vo q) = vo (λ x z xz → trans0 (p x x (≤-refl x)) (q x z xz))
trans0 (vor {κ = inj₁ ()} p) q
trans0 (vor {κ = inj₂ _} p) (vo q) = vor (λ z → trans0 (p z) (q z z (≤-refl z)))
```
