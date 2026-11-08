# 可数高度观察器的遗传坐标关系

Rel B的Ω分支要求相关低层坐标产生相关源子树。Coord只沿原Cd高度
结构下降：后继新kind取低层Rel，旧kind递归，并层保留原分量编号。
不把不同路径拷贝当作相等，也不把任意raw树声明为自相关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRelIf where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)

data Trees {S : KS} (Q : ∀ κ → E S κ → E S κ → Set) : HB S → HB S → Set where
  rz : Trees Q hz hz
  rs : ∀ {a b} → Trees Q a b → Trees Q (hs a) (hs b)
  rl : ∀ {f g} → (∀ n → Trees Q (f n) (g n)) → Trees Q (hl f) (hl g)
  ro : ∀ {κ f g} → (∀ {a b} → Q κ a b → Trees Q (f a) (g b)) → Trees Q (hΩ κ f) (hΩ κ g)

mutual
  Rel : ∀ B → HB (F B) → HB (F B) → Set
  Rel B = Trees (Coord B)
  Coord : ∀ B κ → E (F B) κ → E (F B) κ → Set
  Coord hz ()
  Coord (hs B) (inj₁ κ) = Coord B κ
  Coord (hs B) (inj₂ _) = Rel B
  Coord (hl f) (n , κ) = Coord (f n) κ
  Coord (hΩ () f) κ

record RelObserver : Set₁ where
  field
    floor-related : ∀ B → Rel B (floor B) (floor B)
    observe-related : ∀ B lB t pt {a b} → Rel B a b →
      Rel t (observe B lB t pt a) (observe B lB t pt b)
```

observe-related只比较同一原B、lB、t、pt的两次运行。原floor全族
必须由构造实际实填；跨高度或跨路径的推广不包含在本接口内。
