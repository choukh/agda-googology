# 原折叠保持带路由的位置与相干证书

不另写运行器；下列定理的输出逐字使用原R.fold。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedRoutedRun where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldIf using (Path)
import OCF.Align.BoundedNativeFoldRun as R
open R using (Decision; keep; same; above; decide)
open import OCF.Align.BoundedNativeZeroWorld using (seed)
open import OCF.Align.BoundedNativeReadyGood
import OCF.Align.BoundedNativeReadyCoord as C
open import OCF.Align.BoundedNativeReadySeedView using (seed-view)
open import OCF.Align.BoundedNativeViewIf using (View; module Laws)
open import OCF.Align.BoundedNativeReadyFold using (repeat-good; diagonal-good)
open import OCF.Align.BoundedRoutedIf

module Node (B : Cd) (lB : LgB B) (t : Cd) (pt : t ⊲ B)
  (c : Cd) (κ : K (Native c)) (g : E (Native c) κ → HB Source)
  (pc : c ⊲ B) (pg : ∀ e → Data.Unit.⊤ → Path B (g e)) where
  result : Decision B t (E (Native c) κ) → HB (Native t)
  result (keep j fr) = hΩ j (λ e → R.fold B lB t pt (g (fr e)) (pg (fr e) tt))
  result (same to) = diagonal
    (λ e → R.fold B lB t pt (g (to e)) (pg (to e) tt))
    (λ e → R.fold B lB t pt (g (to e)) (pg (to e) tt))
  result (above i pi ti to) = diagonal
    (λ e → R.fold B lB i (⊲ᴮ-tr (hsuc hself) pi) (g (to e)) (pg (to e) tt))
    (λ e → R.fold B lB t pt (g (to e)) (pg (to e) tt))

  equation : R.fold B lB t pt (hΩ (inj₂ c , κ) g) (pc , pg) ≡
    result (decide pt lB (raise pc (classify c κ)))
  equation with decide pt lB (raise pc (classify c κ))
  ... | keep j fr = refl
  ... | same to = refl
  ... | above i pi ti to = refl

  mono : ∀ {v a pa e} → LgW (Native hz) v →
    RoutedGood B (hΩ (inj₂ c , κ) g) (pc , pg) →
    Bd (Native c) κ e (seed c v) → RoutedPos B v a pa (g e) (pg e tt) →
    (∀ d → Coord c κ d → ∀ {a pa} → RoutedPos B v a pa (g d) (pg d tt) →
      R.fold B lB t pt a pa ⊲[ seed t v ] R.fold B lB t pt (g d) (pg d tt)) →
    (D : Decision B t (E (Native c) κ)) → Laws.For (seed t v) (seed c v) κ D →
    R.fold B lB t pt a pa ⊲[ seed t v ] result D
  mono lv (mo , lg) be p ih (keep j fr) (fw , pr , back) with back _ be
  ... | d , refl , bd = hLim bd (ih _ (C.admitted c κ lv be) p)
  mono lv (mo , lg) be p ih (same to) (bs , upper) =
    ⊲ᴮ-tr (ih _ (C.admitted c κ lv be) p)
      (⊲ᴮ-tr (ih _ (C.admitted c κ lv bs) (mo lv be bs (upper _ be))) (hlim 0 hself))
  mono lv (mo , lg) be p ih (above i pi ti to) (bs , upper) =
    ⊲ᴮ-tr (ih _ (C.admitted c κ lv be) p)
      (⊲ᴮ-tr (ih _ (C.admitted c κ lv bs) (mo lv be bs (upper _ be))) (hlim 0 hself))

position : ∀ B lB t pt {v a pa} (h : HB Source) (p : Path B h) →
  LgW (Native hz) v → RoutedGood B h p → RoutedPos B v a pa h p →
  R.fold B lB t pt a pa ⊲[ seed t v ] R.fold B lB t pt h p
position B lB t pt h p lv l (self .h .p) = hself
position B lB t pt (hs h) p lv l (sucR q) =
  ⊲ᴮ-tr (position B lB t pt h p lv l q) (hlim 0 hself)
position B lB t pt (hl f) p lv (st , l) (limR n q) = hlim n (position B lB t pt (f n) (p n) lv (l n) q)
position B lB t pt (hΩ (inj₂ c , κ) g) (pc , pg) lv l@(mo , lg) (omegaR be q) =
  subst (λ x → R.fold B lB t pt _ _ ⊲[ seed t _ ] x) (sym (Node.equation B lB t pt c κ g pc pg))
  (Node.mono B lB t pt c κ g pc pg lv l be q
    (λ d ld r → position B lB t pt (g d) (pg d tt) lv (lg d ld) r)
    (decide pt lB (raise pc (classify c κ)))
    (View.node-laws (seed-view lB c pc t pt _) κ))
```

```agda
module GoodNode (B : Cd) (lB : LgB B) (t : Cd) (pt : t ⊲ B)
  (c : Cd) (κ : K (Native c)) (g : E (Native c) κ → HB Source)
  (pc : c ⊲ B) (pg : ∀ e → Data.Unit.⊤ → Path B (g e)) where
  open Node B lB t pt c κ g pc pg using (result)

  preserve : RoutedGood B (hΩ (inj₂ c , κ) g) (pc , pg) →
    (∀ y py e → Coord c κ e → Good y (R.fold B lB y py (g e) (pg e tt))) →
    (D : Decision B t (E (Native c) κ)) →
    (∀ v → Laws.For (seed t v) (seed c v) κ D) → C.Allowed (Coord c κ) D → Good t (result D)
  preserve (mo , lg) ih (keep j fr) laws allowed =
    (λ {v} lv be bd r →
      let fw = proj₁ (laws v)
          pr = proj₁ (proj₂ (laws v))
      in position B lB t pt (g (fr _)) (pg (fr _) tt) lv
        (lg _ (C.admitted c κ lv (fw _ bd)))
        (mo lv (fw _ be) (fw _ bd) (pr _ _ be bd r))) ,
    (λ e le → ih t pt (fr e) (allowed e le))
  preserve (mo , lg) ih (same to) laws allowed =
    diagonal-good t t _ _ (λ e le → ih t pt (to e) (allowed e le))
      (λ e le → ih t pt (to e) (allowed e le))
  preserve (mo , lg) ih (above i pi ti to) laws allowed =
    diagonal-good i t _ _ (λ e le → ih i (⊲ᴮ-tr (hsuc hself) pi) (to e) (allowed e le))
      (λ e le → ih t pt (to e) (allowed e le))

good : ∀ B lB t pt h p → RoutedGood B h p → Good t (R.fold B lB t pt h p)
good B lB t pt hz p l = tt
good B lB t pt (hs h) p l = repeat-good t _ (good B lB t pt h p l)
good B lB t pt (hl f) p (st , l) =
  (λ lv n → position B lB t pt (f _) (p _) lv (l _) (st lv n)) ,
  (λ n → good B lB t pt (f n) (p n) (l n))
good B lB t pt (hΩ (inj₁ _ , κ) g) p ()
good B lB t pt (hΩ (inj₂ c , κ) g) (pc , pg) l@(mo , lg) =
  subst (Good t) (sym (Node.equation B lB t pt c κ g pc pg))
    (GoodNode.preserve B lB t pt c κ g pc pg l
      (λ y py e le → good B lB y py (g e) (pg e tt) (lg e le))
      (decide pt lB (raise pc (classify c κ)))
      (λ v → View.node-laws (seed-view lB c pc t pt v) κ)
      (C.component c κ pc pt lB))
```

position与good对所有共同合法B下的源分量、目标和反馈递归统一成立。
条件是实际Path索引的RoutedGood；不能用不带路由的Mixed代替。
