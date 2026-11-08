# 原树与实际路径一起比较

RoutedPos的自反构造只对同一个树-路径对自身成立。它不是任意Path证明
相等律，也不把逐点相同的函数路由当作字面相等。其余构造继承实际子路径。
这是一项可能严格的树侧证书；原θ是否满足须单独检验。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedRoutedIf where
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf using (Path)
open import OCF.Align.BoundedNativeZeroWorld using (seed)
open import OCF.Align.BoundedNativeReadyGood using (Coord)
open import OCF.Align.BoundedNativeReadyMixed using (shared; Mixed)

data RoutedPos (B : Cd) (v : Wd (Native hz)) :
  (a : HB Source) → Path B a → (b : HB Source) → Path B b → Set where
  self : ∀ a p → RoutedPos B v a p a p
  sucR : ∀ {a b pa pb} → RoutedPos B v a pa b pb → RoutedPos B v a pa (hs b) pb
  limR : ∀ {a f pa pf} n → RoutedPos B v a pa (f n) (pf n) →
    RoutedPos B v a pa (hl f) pf
  omegaR : ∀ {a c κ g pa pc pg e} → Bd (Native c) κ e (seed c v) →
    RoutedPos B v a pa (g e) (pg e tt) →
    RoutedPos B v a pa (hΩ (inj₂ c , κ) g) (pc , pg)

forget : ∀ {B v a pa b pb} → RoutedPos B v a pa b pb → a ⊲[ shared v ] b
forget (self a p) = hself
forget (sucR p) = hsuc (forget p)
forget (limR n p) = hlim n (forget p)
forget (omegaR e p) = hLim e (forget p)

RoutedGood : ∀ B (h : HB Source) → Path B h → Set
RoutedGood B hz p = ⊤
RoutedGood B (hs h) p = RoutedGood B h p
RoutedGood B (hl f) p =
  (∀ {v} → LgW (Native hz) v → ∀ n → RoutedPos B v (f n) (p n) (f (suc n)) (p (suc n))) ×
  (∀ n → RoutedGood B (f n) (p n))
RoutedGood B (hΩ (inj₁ _ , κ) g) p = ⊥
RoutedGood B (hΩ (inj₂ c , κ) g) (pc , pg) =
  (∀ {v e d} → LgW (Native hz) v → Bd (Native c) κ e (seed c v) →
    Bd (Native c) κ d (seed c v) → Pr (Native c) κ (seed c v) e d →
    RoutedPos B v (g e) (pg e tt) (g d) (pg d tt)) ×
  (∀ e → Coord c κ e → RoutedGood B (g e) (pg e tt))

mixed : ∀ B h p → RoutedGood B h p → Mixed B h
mixed B hz p l = tt
mixed B (hs h) p l = mixed B h p l
mixed B (hl f) p (st , l) = (λ lv n → forget (st lv n)) , (λ n → mixed B (f n) (p n) (l n))
mixed B (hΩ (inj₁ _ , κ) g) p ()
mixed B (hΩ (inj₂ c , κ) g) (pc , pg) (mo , l) =
  pc , (λ lv e d r → forget (mo lv e d r)) , (λ e le → mixed B (g e) (pg e tt) (l e le))
```

Ω位置规则只取当前字面种类界内坐标，Ω单调的两坐标明确共用该界。
接口不引用折叠输出，不把目标值大小藏进证书，也没有路径判等操作。
