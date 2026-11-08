# 原cl、along与带共同界分类保持坐标关系

所有路径都逐构造保留。along的逆坐标从目标关系回到实际低层Rel；
nw的编码再送进原source种类。pick只消费已在同一合法B比较所得的
路径结果，本篇不建立额外高度三歧或证明无关性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRelClass where
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableRelIf

along-good : ∀ {i t} (p : hs i ⊲ t) {a b} →
  Coord t (C.along p) a b → Rel i (C.frA p a) (C.frA p b)
along-good hself r = r
along-good (hsuc p) r = along-good p r
along-good (hlim n p) r = along-good p r
along-good (hLim {κ = ()} b p) r

ClGood : ∀ {B κ} → C.Cl {S⊥} B κ → Set
ClGood (C.bas () to)
ClGood {B} {κ} (C.nw i p to) = ∀ {a b} → Rel i a b → Coord B κ (to a) (to b)
cl-good : ∀ B κ → ClGood (C.cl B κ)
cl-good hz ()
cl-good (hs B) (inj₁ κ) with C.cl B κ | cl-good B κ
... | C.bas () to | p
... | C.nw i pi to | p = p
cl-good (hs B) (inj₂ _) r = r
cl-good (hl f) (n , κ) with C.cl (f n) κ | cl-good (f n) κ
... | C.bas () to | p
... | C.nw i pi to | p = p
cl-good (hΩ () f) κ

Good : ∀ {B t A} → (A → A → Set) → C.Dc F B t A → Set
Good {t = t} Q (C.keep κ fr) = ∀ {a b} → Coord t κ a b → Q (fr a) (fr b)
Good {t = t} Q (C.same to) = ∀ {a b} → Rel t a b → Q (to a) (to b)
Good Q (C.above i p q to) = ∀ {a b} → Rel i a b → Q (to a) (to b)

pick-good : ∀ {B t i A} (Q : A → A → Set) (to : HB (F i) → A)
  (to-good : ∀ {a b} → Rel i a b → Q (to a) (to b))
  (pi : hs i ⊲ B) (r : (t ⊲ hs i) ⊎ (hs i ⊲ t)) → Good Q (C.pick S⊥ to pi r)
pick-good Q to good pi (inj₂ p) r = good (along-good p r)
pick-good Q to good pi (inj₁ hself) r = good r
pick-good Q to good pi (inj₁ (hsuc hself)) r = good r
pick-good Q to good pi (inj₁ (hsuc (hsuc p))) r = good r
pick-good Q to good pi (inj₁ (hsuc (hlim n p))) r = good r
pick-good Q to good pi (inj₁ (hsuc (hLim {κ = ()} b p))) r

class-good : ∀ B lB t pt κ → Good (Coord B κ) (classify B lB t pt κ)
class-good B lB t pt κ with C.cl B κ | cl-good B κ
... | C.bas () to | p
... | C.nw i pi to | p = pick-good (Coord B κ) to p pi (cmpB pi pt _ lB)
```
