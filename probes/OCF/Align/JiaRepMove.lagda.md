# 关系式码树对应：搬运与提升

只增加关系保持定理，不改变 `JiaBase` 的树或分支域。
Ω 情况中，目标低层输入先按反方向搬回；只搬运已有的对应证据，
没有为任意原始输入寻找码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRepMove where

open import OCF.Align.EboLeanDef using (T)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase
open import OCF.Align.JiaFold using (lift)
open import OCF.Align.JiaRep
open RelLayer using (rz; rs; rl; ro)

module Map
  {ℓ : T}
  {L L′ : ∀ j → Below j ℓ → Set}
  {R : ∀ j p → L j p → T → Set}
  {R′ : ∀ j p → L′ j p → T → Set}
  (m : ∀ j p → L′ j p → L j p)
  (mr : ∀ j p {y d} → R′ j p y d → R j p (m j p y) d)
  where

  keeps : ∀ {x c} → RelLayer.Rel ℓ L R x c →
    RelLayer.Rel ℓ L′ R′ (mapTree m x) c
  keeps rz = rz
  keeps (rs r) = rs (keeps r)
  keeps (rl e r) = rl e (λ n → keeps (r n))
  keeps (ro {j} {p} e r) = ro e (λ q → keeps (r (mr j p q)))

rep-coe : ∀ {ℓ} (a a′ : Acc′ ℓ) {x c} → Rep a x c → Rep a′ (coe a a′ x) c
rep-coe (acc h) (acc h′) = Map.keeps
  (λ { j (below nj p) → coe (h′ nj p) (h nj p) })
  (λ { j (below nj p) r → rep-coe (h′ nj p) (h nj p) r })

rep-lift : ∀ {i ℓ} (ai : Acc′ i) (aℓ : Acc′ ℓ) (p : Below i ℓ) {x c} →
  Rep ai x c → Rep aℓ (lift ai aℓ p x) c
rep-lift (acc hi) (acc hℓ) p rz = rz
rep-lift (acc hi) (acc hℓ) p (rs r) = rs (rep-lift (acc hi) (acc hℓ) p r)
rep-lift (acc hi) (acc hℓ) p (rl e r) = rl e (λ n → rep-lift (acc hi) (acc hℓ) p (r n))
rep-lift (acc hi) (acc hℓ) p (ro {j} {p = q} e r) = ro e
  (λ s → rep-lift (acc hi) (acc hℓ) p
    (r (rep-coe (hℓ (normal q) (smaller (below-trans q p)))
                (hi (normal q) (smaller q)) s)))
```
