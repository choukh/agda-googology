# 同形高度的异层坐标与原Γ接口

两边高度无需字面共同上界，也不比较其裸值；Same逐构造配对高度，
并层编号保持相同。真正观察仍分别在各自完整合法source界内分类。
Ω枝只接受递归低层关系给出的异坐标证据，不假任意raw函数保Same。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableShapeIf where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)

map-K : ∀ {a b : Cd} → Same a b → K (F a) → K (F b)
map-K zz ()
map-K (ss p) (inj₁ κ) = inj₁ (map-K p κ)
map-K (ss p) (inj₂ u) = inj₂ u
map-K (ll p) (n , κ) = n , map-K (p n) κ
map-K (oo {κ = ()} p) κ

data HTrees (S T : KS) (k : K S → K T)
  (Q : ∀ κ → E S κ → E T (k κ) → Set) : HB S → HB T → Set where
  tz : HTrees S T k Q hz hz
  ts : ∀ {a b} → HTrees S T k Q a b → HTrees S T k Q (hs a) (hs b)
  tl : ∀ {f g} → (∀ n → HTrees S T k Q (f n) (g n)) → HTrees S T k Q (hl f) (hl g)
  to : ∀ {κ f g} → (∀ {a b} → Q κ a b → HTrees S T k Q (f a) (g b)) →
    HTrees S T k Q (hΩ κ f) (hΩ (k κ) g)
Tree : ∀ {a b : Cd} → Same a b → HB (F a) → HB (F b) → Set
Coord : ∀ {a b : Cd} (p : Same a b) κ → E (F a) κ → E (F b) (map-K p κ) → Set
Tree {a} {b} p = HTrees (F a) (F b) (map-K p) (Coord p)
Coord zz ()
Coord (ss p) (inj₁ κ) = Coord p κ
Coord (ss p) (inj₂ _) = Tree p
Coord (ll p) (n , κ) = Coord (p n) κ
Coord (oo {κ = ()} p) κ

record CanonicalObserverShape : Set₁ where
  field
    preserve : ∀ {a b : Cd} (p : Same a b) {x y} → Tree (leg-same p) x y →
      Same (observe (leg a) (Lg-leg a) hz (z⊲ᴮ (leg a)) x)
        (observe (leg b) (Lg-leg b) hz (z⊲ᴮ (leg b)) y)
record GammaShape : Set where
  field
    preserve-Γ : ∀ {a b : Cd} → Same a b → Same (Γ a) (Γ b)
```

观察接口固定原canonical leg与Lg-leg，不量化两份任意合法证明。
尚待分类器与合法步进的对应证明；异层地板证书将实际填入原Γ输入。
