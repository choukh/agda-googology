# Good坐标域的对角与端点

对角字段由实际Good的自证分量给出；不要求raw全域自反。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseLayerGoodDomain where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.RebaseLayerGoodIf
open import OCF.Lean.RebaseLayerGoodClosure using (self)
diagonal : ∀ c κ e → Admit c κ e → Coord c κ e e
diagonal hz (inj₁ ()) e a
diagonal hz (inj₂ _) e a = ≤-refl e
diagonal (hs c) (inj₁ κ) e a = diagonal c κ e a
diagonal (hs c) (inj₂ _) e a = self c a , a , a
diagonal (hl f) (n , κ) e a = diagonal (f n) κ e a
left : ∀ c κ {x y} → Coord c κ x y → Admit c κ x
left hz (inj₁ ()) p
left hz (inj₂ _) p = tt
left (hs c) (inj₁ κ) p = left c κ p
left (hs c) (inj₂ _) p = proj₁ (proj₂ p)
left (hl f) (n , κ) p = left (f n) κ p
right : ∀ c κ {x y} → Coord c κ x y → Admit c κ y
right hz (inj₁ ()) p
right hz (inj₂ _) p = tt
right (hs c) (inj₁ κ) p = right c κ p
right (hs c) (inj₂ _) p = proj₂ (proj₂ p)
right (hl f) (n , κ) p = right (f n) κ p
```
