# 可完成的有向结构模拟

与普通值序不同，此关系没有任意ℕ左消去：空极限不能据每枝为零
而模拟零。它保留逐点极限与右选项，使目标0的完成运输有结构依据。
层与坐标递归只沿原Cd；观察比较固定共同合法B及目标路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRegularCompareIf where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

data SimTree (S : KS) (Q : ∀ κ → E S κ → E S κ → Set) : HB S → HB S → Set where
  sz : ∀ {b} → SimTree S Q hz b
  ss : ∀ {a b} → SimTree S Q a b → SimTree S Q (hs a) (hs b)
  sr : ∀ {a b} → SimTree S Q a b → SimTree S Q a (hs b)
  sl : ∀ {f g} → (∀ n → SimTree S Q (f n) (g n)) → SimTree S Q (hl f) (hl g)
  sli : ∀ {a f} n → SimTree S Q a (f n) → SimTree S Q a (hl f)
  so : ∀ {κ f g} → (∀ {a b} → Q κ a b → SimTree S Q (f a) (g b)) → SimTree S Q (hΩ κ f) (hΩ κ g)
  sor : ∀ {a κ g} → (∀ e → SimTree S Q a (g e)) → SimTree S Q a (hΩ κ g)
Sim : ∀ B → HB (F B) → HB (F B) → Set
Coordinate : ∀ B κ → E (F B) κ → E (F B) κ → Set
Sim B = SimTree (F B) (Coordinate B)
Coordinate hz ()
Coordinate (hs B) (inj₁ κ) = Coordinate B κ
Coordinate (hs B) (inj₂ _) = Sim B
Coordinate (hl f) (n , κ) = Coordinate (f n) κ
Coordinate (hΩ () f) κ

record StructuralComparison : Set₁ where
  field
    floor-self : ∀ B → Sim B (floor B) (floor B)
    compare : ∀ B lB t pt {a b} → Sim B a b →
      Sim t (observe B lB t pt a) (observe B lB t pt b)
    complete : ∀ {a b} → Sim hz a b → leg a ≤ᵛ leg b
```

这不是对裸高度的比较，也不蕴含两个已知同值的高度能互相模拟。
完整字段将由原地板和原观察器实例化，不修改Γ或其完成。
