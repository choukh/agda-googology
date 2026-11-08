# 全部实际分量地板的固定路由实例

本篇直接使用原component-path以及原flL地板。它不是另造玩具树容器：
对任意可数原生分量、共同界和目标，给前篇条件定理的可满足实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedRoutedFloor where
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLay using (_⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedNativeZeroWorld using (seed)
open import OCF.Align.BoundedNativeReadyGood using (Good; floor-good)
open import OCF.Align.BoundedNativeReadyMixed using (put)
open import OCF.Align.BoundedNativeFloor using (component-path)
open import OCF.Align.BoundedRoutedIf
import OCF.Align.BoundedRoutedRun as Proof
import OCF.Align.BoundedNativeFoldRun as R

put-position : ∀ c B (pc : c ⊲ B) {v a b} → a ⊲[ seed c v ] b →
  RoutedPos B v (put c a) (component-path c B pc a) (put c b) (component-path c B pc b)
put-position c B pc {a = a} hself = self _ _
put-position c B pc (hsuc p) = sucR (put-position c B pc p)
put-position c B pc (hlim n p) = limR n (put-position c B pc p)
put-position c B pc (hLim e p) = omegaR e (put-position c B pc p)

put-good : ∀ c B (pc : c ⊲ B) a → Good c a →
  RoutedGood B (put c a) (component-path c B pc a)
put-good c B pc hz l = tt
put-good c B pc (hs a) l = put-good c B pc a l
put-good c B pc (hl f) (st , l) =
  (λ lv n → put-position c B pc (st lv n)) , (λ n → put-good c B pc (f n) (l n))
put-good c B pc (hΩ κ g) (mo , l) =
  (λ lv e d p → put-position c B pc (mo lv e d p)) ,
  (λ e le → put-good c B pc (g e) (l e le))

floor-routed : ∀ c B (pc : c ⊲ B) →
  RoutedGood B (put c (flL (ls lz ⊕L upL lz c)))
    (component-path c B pc (flL (ls lz ⊕L upL lz c)))
floor-routed c B pc = put-good c B pc _ (floor-good c)

floor-output-good : ∀ c B lB (pc : c ⊲ B) t pt →
  Good t (R.fold B lB t pt (put c (flL (ls lz ⊕L upL lz c)))
    (component-path c B pc (flL (ls lz ⊕L upL lz c))))
floor-output-good c B lB pc t pt = Proof.good B lB t pt _ _ (floor-routed c B pc)
```

这给全部分量的真实非恒定地板、所有合法共同界和所有目标的实例。
不要求它们的跨位置路由彼此相等；同一分量实例内部固定pc。
原θ混合的component-path随前驱位置组合，不能由本实例自动取得其RoutedGood。
