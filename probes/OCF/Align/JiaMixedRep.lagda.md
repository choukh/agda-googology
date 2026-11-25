# 混合树族的逐项对应与搬运

正规子句继续只约束已有关系的 raw 输入，不提供 raw 到码的函数。
奇异子句对携码输入逐 fsT 约束。零、后继、ℕ 极限的精度与旧 Rep 相同。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaMixedRep where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([])
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.EboLeanDef using (T; sucT; cof; cω; cΩ; fsn; fsT)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaMixedBase

module RelLayer
  (ℓ : T)
  (Low₀ : ∀ j → Below j ℓ → Set)
  (RepLow₀ : ∀ j p → Low₀ j p → T → Set)
  where

  data Rel : Layer.Tree ℓ Low₀ → T → Set where
    rz : Rel Layer.z []
    rs : ∀ {x c} → Rel x c → Rel (Layer.s x) (sucT c)
    rl : ∀ {f c} → cof c ≡ cω →
      (∀ n → Rel (f n) (fsn c n)) → Rel (Layer.l f) c
    rr : ∀ {j p f c} → cof c ≡ cΩ j →
      (∀ {y d} → RepLow₀ j p y d → Rel (f y) (fsT c d)) →
      Rel (Layer.r p f) c
    rq : ∀ {j} {p : Below j ℓ} {f : CodeArg j → Layer.Tree ℓ Low₀} {c} → cof c ≡ cΩ j →
      (∀ d → Rel (f d) (fsT c (code d))) → Rel (Layer.q {j = j} p f) c

Rep : ∀ {ℓ} (a : Acc′ ℓ) → Tree ℓ a → T → Set
RepLow : ∀ ℓ (a : Acc′ ℓ) j p → Low ℓ a j p → T → Set
Rep {ℓ} a = RelLayer.Rel ℓ (Low ℓ a) (RepLow ℓ a)
RepLow ℓ (acc h) j (below nj p) = Rep (h nj p)

open RelLayer using (rz; rs; rl; rr; rq)

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
  keeps (rr {j} {p} e r) = rr e (λ q → keeps (r (mr j p q)))
  keeps (rq e r) = rq e (λ d → keeps (r d))

rep-coe : ∀ {ℓ} (a a′ : Acc′ ℓ) {x c} → Rep a x c → Rep a′ (coe a a′ x) c
rep-coe (acc h) (acc h′) = Map.keeps
  (λ { j (below nj p) → coe (h′ nj p) (h nj p) })
  (λ { j (below nj p) r → rep-coe (h′ nj p) (h nj p) r })

rep-lift : ∀ {i ℓ} (ai : Acc′ i) (aℓ : Acc′ ℓ) (p : Below i ℓ) {x c} →
  Rep ai x c → Rep aℓ (lift ai aℓ p x) c
rep-lift (acc hi) (acc hℓ) p rz = rz
rep-lift (acc hi) (acc hℓ) p (rs r) = rs (rep-lift (acc hi) (acc hℓ) p r)
rep-lift (acc hi) (acc hℓ) p (rl e r) = rl e (λ n → rep-lift (acc hi) (acc hℓ) p (r n))
rep-lift (acc hi) (acc hℓ) p (rr {j} {p = q} e r) = rr e
  (λ s → rep-lift (acc hi) (acc hℓ) p
    (r (rep-coe (hℓ (normal q) (smaller (below-trans q p)))
                (hi (normal q) (smaller q)) s)))
rep-lift (acc hi) (acc hℓ) p (rq e r) = rq e (λ d → rep-lift (acc hi) (acc hℓ) p (r d))
```

没有把正规子句的前提换成 CodeArg，也没有对全 raw 输入填 Rep。
本篇只证明关系可定义且搬运保持；新版 ψ 的闭合另有义务。
