# 具体LH坐标确为低层合法对象

泛型KS本身没有“坐标是树”的字段。本篇对实际LH种类逐层取出低层
原树、低世界与合法性；每个有界坐标因此携带可递归的低层Object及View。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexViewCoordinate where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (lvl)
open import OCF.Lean.HigherIndexViewIf
import OCF.Lean.HigherIndexViewRun as V

raw : ∀ x κ → E (Lv x) κ → HB (Lv (lvl x κ))
raw lz () e
raw (ls x) (inj₁ κ) e = raw x κ e
raw (ls x) (inj₂ _) e = e
raw (ll f) (n , κ) e = raw (f n) κ e
raw (lΩ k g) (inj₁ _ , inj₁ κ) e = raw k κ e
raw (lΩ k g) (inj₁ _ , inj₂ _) e = e
raw (lΩ k g) (inj₂ d , κ) e = raw (g d) κ e

world : ∀ x κ → Wd (Lv x) → Wd (Lv (lvl x κ))
world lz () W
world (ls x) (inj₁ κ) W = world x κ (proj₁ W)
world (ls x) (inj₂ _) W = proj₁ W
world (ll f) (n , κ) W = world (f n) κ (W n)
world (lΩ k g) (inj₁ u , inj₁ κ) W = world k κ (proj₁ (W (inj₁ u)))
world (lΩ k g) (inj₁ u , inj₂ _) W = proj₁ (W (inj₁ u))
world (lΩ k g) (inj₂ d , κ) W = world (g d) κ (W (inj₂ d))

world-legal : ∀ x κ {W} → LgW (Lv x) W → LgW (Lv (lvl x κ)) (world x κ W)
world-legal lz () l
world-legal (ls x) (inj₁ κ) l = world-legal x κ (proj₁ l)
world-legal (ls x) (inj₂ _) l = proj₁ l
world-legal (ll f) (n , κ) l = world-legal (f n) κ (l n)
world-legal (lΩ k g) (inj₁ u , inj₁ κ) l = world-legal k κ (proj₁ (l (inj₁ u)))
world-legal (lΩ k g) (inj₁ u , inj₂ _) l = proj₁ (l (inj₁ u))
world-legal (lΩ k g) (inj₂ d , κ) l = world-legal (g d) κ (l (inj₂ d))

coordinate-legal : ∀ x κ {W e} → LgW (Lv x) W → Bd (Lv x) κ e W → LgB (raw x κ e)
coordinate-legal lz () l p
coordinate-legal (ls x) (inj₁ κ) l p = coordinate-legal x κ (proj₁ l) p
coordinate-legal (ls x) (inj₂ _) l p = lgB⊲ p (proj₁ l) (proj₂ l)
coordinate-legal (ll f) (n , κ) l p = coordinate-legal (f n) κ (l n) p
coordinate-legal (lΩ k g) (inj₁ u , inj₁ κ) l p = coordinate-legal k κ (proj₁ (l (inj₁ u))) p
coordinate-legal (lΩ k g) (inj₁ u , inj₂ _) l p = lgB⊲ p (proj₁ (l (inj₁ u))) (proj₂ (l (inj₁ u)))
coordinate-legal (lΩ k g) (inj₂ d , κ) l p = coordinate-legal (g d) κ (l (inj₂ d)) p

module At (x : LH) (W : Wd (Lv x)) (lw : LgW (Lv x) W) (κ : K (Lv x)) where
  module Lower = V.View (Lv (lvl x κ)) (world x κ W) (world-legal x κ lw)
  object : E (Bounded (Lv x) W lw) κ → Lower.Object
  object (e , bd) = raw x κ e , coordinate-legal x κ lw bd
  view : ∀ e → Lower.Shape
  view e = Lower.view (object e)
  value-view : ∀ e → _
  value-view e = Lower.value-view (object e)
```

坐标界仍是W中的原界，不存在任意两裸坐标的比较。这里没有把低层
restricted值等同于其原raw值；低层也用同一内部View约定。
