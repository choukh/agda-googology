# 有限observer的遗传坐标关系接口

高层分支同余由证书明确给出：两个相关低层坐标产生相关源子树。
Rel n不是所有raw树的自反关系；0层才能自动退化为Same。各目标与
反馈层仍消费原Within n m的共同有限上界，不引入新层号比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteRelIf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaFiniteObserveIf
open import OCF.Lean.GeneralOmegaFiniteObserveRun using (observe)

data Trees {S : KS} (Q : ∀ κ → E S κ → E S κ → Set) : HB S → HB S → Set where
  rz : Trees Q hz hz
  rs : ∀ {a b} → Trees Q a b → Trees Q (hs a) (hs b)
  rl : ∀ {f g} → (∀ i → Trees Q (f i) (g i)) → Trees Q (hl f) (hl g)
  ro : ∀ {κ f g} → (∀ {c d} → Q κ c d → Trees Q (f c) (g d)) → Trees Q (hΩ κ f) (hΩ κ g)

mutual
  Rel : ∀ n → HB (F n) → HB (F n) → Set
  Rel n = Trees (Coord n)
  Coord : ∀ n κ → E (F n) κ → E (F n) κ → Set
  Coord zero ()
  Coord (suc n) (inj₁ κ) = Coord n κ
  Coord (suc n) (inj₂ _) = Rel n

record RelObserver : Set where
  field
    floor-related : ∀ n → Rel n (floor n) (floor n)
    observe-related : ∀ {n m a b} (p : Within n m) → Rel n a b →
      Rel m (observe p a) (observe p b)
```

Trees的Q先作为参数给定；Coord只在有限层结构下降，故不会将同一
关系负递归地放入Ω域。后续必须提供原floor与真实反馈实例。
