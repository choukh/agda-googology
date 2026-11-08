# 零分量的实际全目标视图与位置定理

base-kind明确选取的投影始终可构造。本篇不给其他rank路径偷偷加相干，
只证明原Native0分量的全部树在原运行器下保位置与合法。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeViewBase where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldIf
open import OCF.Align.BoundedNativeFoldRun using (fold)
open import OCF.Align.BoundedNativeViewIf

project : ∀ t → Wd (Native t) → Wd (Native hz)
project hz W = W
project (hs t) W = project t (proj₁ W)
project (hl f) W = project (f 0) (W 0)
project-legal : ∀ t {W} → LgW (Native t) W → LgW (Native hz) (project t W)
project-legal hz l = l
project-legal (hs t) l = project-legal t (proj₁ l)
project-legal (hl f) l = project-legal (f 0) (l 0)

back-bd : ∀ t κ {W e} → Bd (Native t) (base-kind t κ) e W →
  Bd (Native hz) κ (base-fr t κ e) (project t W)
back-bd hz κ b = b
back-bd (hs t) κ b = back-bd t κ b
back-bd (hl f) κ b = back-bd (f 0) κ b
forward-bd : ∀ t κ {W e} → Bd (Native hz) κ e (project t W) →
  Bd (Native t) (base-kind t κ) (base-to t κ e) W
forward-bd hz κ b = b
forward-bd (hs t) κ b = forward-bd t κ b
forward-bd (hl f) κ b = forward-bd (f 0) κ b
back-pr : ∀ t κ {W e d} → Pr (Native t) (base-kind t κ) W e d →
  Pr (Native hz) κ (project t W) (base-fr t κ e) (base-fr t κ d)
back-pr hz κ p = p
back-pr (hs t) κ p = back-pr t κ p
back-pr (hl f) κ p = back-pr (f 0) κ p

base-view : ∀ {B} (lB : LgB B) (pc : hz ⊲ B) t (pt : t ⊲ B) W → View lB hz pc t pt W
base-view lB pc t pt W = record
  { input-world = project t W
  ; legal-world = project-legal t
  ; node-laws = λ κ → (λ e b → back-bd t κ b) ,
      (λ e d be bd p → back-pr t κ p) ,
      (λ a b → base-to t κ a , base-frto t κ a , forward-bd t κ b) }

place : HB (Native hz) → HB Source
place = ι (inj₂ hz)
path : ∀ B a → Path B (place a)
path B hz = tt
path B (hs a) = path B a
path B (hl f) = λ n → path B (f n)
path B (hΩ κ g) = z⊲ᴮ B , (λ c a → path B (g c))

module Actual (B : Cd) (lB : LgB B) (t : Cd) (pt : t ⊲ B) where
  run : HB (Native hz) → HB (Native t)
  run a = fold B lB t pt (place a) (path B a)

  position : ∀ {a b W} → a ⊲[ project t W ] b → run a ⊲[ W ] run b
  position hself = hself
  position (hsuc p) = ⊲ᴮ-tr (position p) (hlim 0 hself)
  position (hlim n p) = hlim n (position p)
  position {a} {hΩ κ g} {W} (hLim {c = c} b p) =
    hLim (forward-bd t κ b)
      (subst (λ e → run a ⊲[ W ] run (g e)) (sym (base-frto t κ c)) (position p))

  legal : ∀ a → LgB a → LgB (run a)
  legal hz l = tt
  legal (hs a) l = LegalSum.sum-legal (Native t) _ (λ n → legal a l)
  legal (hl f) (st , l) = (λ n → position (st n)) , (λ n → legal (f n) (l n))
  legal (hΩ κ g) (mo , l) =
    (λ lw b b′ p → position (mo (project-legal t lw) (back-bd t κ b) (back-bd t κ b′) (back-pr t κ p))) ,
    (λ lw b → legal (g _) (l (project-legal t lw) (back-bd t κ b)))
```

Actual.run直接使用原fold和原Source分量。位置律对所有目标world成立；
合法性只在原LgB要求的地方消费合法world。并不包含新rank坍缩反馈。
