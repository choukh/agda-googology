# Ω_Ω 种子的全部字段仍在纯可数层

本篇只按树结构证明种子的字段形状，原表示与前缀表示各给一份。
Small 沿第一位置向下封闭；因此前轮 omega-fields 给出的字段界足够，
无需给任意 Raw 0 输入补码。后面的按需检查可以统一处理所有合法支，
不只检查导致 no-gamma-seed 的 ηa 支。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiDSeed where

open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All as A using ()
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
import OCF.Align.YiCtxStep as S
import OCF.Align.YiCtxFork as W
import OCF.Align.YiRTransport as R
open import OCF.Align.YiRCountable
  using (Small; small-zero; small-suc; small-lim; Fields;
         raw0-small; omega-fields; raw0-omega-fields; small-no-field)
open import OCF.Align.YiSpinePrefix using (add; Ωprefix)
open import OCF.Align.YiDBase

small-position : ∀ {x y} → CP x y → Small y → Small x
small-position V.self s = s
small-position (V.suc p) (small-suc s) = small-position p s
small-position (V.lim n p) (small-lim s) = small-position p (s n)
small-position (V.fst p) ()

small-pred : ∀ {x} → Small (F.suc x) → Small x
small-pred (small-suc s) = s

SmallFields : F.LF → Set
SmallFields t = ∀ {k} → K.Field k t → Small k

small-fields : ∀ {t} → Small t → SmallFields t
small-fields s f = ⊥-elim (small-no-field s f)

bounded-small-fields : ∀ {B t} → Small B → Fields B t → SmallFields t
bounded-small-fields s bound f = small-pred (small-position (bound f) s)

omega-small-fields : ∀ x → Small x → SmallFields (V.Ω̂ x)
omega-small-fields x s = bounded-small-fields s (omega-fields x s)

node-small-fields : ∀ {k c t g} → Small k → SmallFields t →
  (∀ η e → SmallFields (g η e)) → SmallFields (F.lc k c t g)
node-small-fields sk st sg K.at = sk
node-small-fields sk st sg (K.in-index p) = small-fields sk p
node-small-fields sk st sg (K.in-first p) = st p
node-small-fields sk st sg (K.in-branch η e p) = sg η e p

small-add : ∀ {x y} → Small x → Small y → Small (V._+ᴸ_ x y)
small-add sx small-zero = sx
small-add sx (small-suc sy) = small-suc (small-add sx sy)
small-add sx (small-lim sy) = small-lim (λ n → small-add sx (sy n))

add-small-fields : ∀ x y → SmallFields x → SmallFields y →
  SmallFields (V._+ᴸ_ x y)
add-small-fields x F.zero sx sy = sx
add-small-fields x (F.suc y) sx sy (K.in-suc p) =
  add-small-fields x y sx (λ f → sy (K.in-suc f)) p
add-small-fields x (F.lim f) sx sy (K.in-lim n p) =
  add-small-fields x (f n) sx (λ q → sy (K.in-lim n q)) p
add-small-fields x (F.lc k c t g) sx sy K.at = sy K.at
add-small-fields x (F.lc k c t g) sx sy (K.in-index p) = sy (K.in-index p)
add-small-fields x (F.lc k c t g) sx sy (K.in-first p) =
  add-small-fields x t sx (λ q → sy (K.in-first q)) p
add-small-fields x (F.lc k c t g) sx sy (K.in-branch η e p) =
  add-small-fields x (g η e) sx (λ q → sy (K.in-branch η e q)) p

one-small : Small (Y.tree W.one)
one-small = small-suc small-zero

ν-fields : SmallFields (Y.tree R.ν)
ν-fields = omega-small-fields (Y.tree W.one) one-small

seed-fields : SmallFields (Y.tree R.seed-tree)
seed-fields = node-small-fields small-zero ν-fields
  (λ η e → omega-small-fields (V.up F.zero η) (raw0-small η))

νp seedp : Y.Level
νp = Ωprefix W.one
seedp = Ωprefix νp

νp-fields : SmallFields (Y.tree νp)
νp-fields = add-small-fields (Y.tree W.one) (Y.tree R.ν)
  (small-fields one-small) ν-fields

omega-νp-fields : SmallFields (V.Ω̂ (Y.tree νp))
omega-νp-fields = node-small-fields small-zero
  (omega-small-fields (F.suc (F.suc F.zero)) (small-suc one-small))
  (λ η e → omega-small-fields (V._+ᴸ_ (Y.tree W.one) (V.up F.zero η))
    (small-add one-small (raw0-small η)))

seedp-fields : SmallFields (Y.tree seedp)
seedp-fields = add-small-fields (Y.tree νp) (V.Ω̂ (Y.tree νp))
  νp-fields omega-νp-fields

prefix-context : K.Ctx (νp ∷ Y.zero ∷ [])
prefix-context = K.ctx (Y.suc νp)
  (V.suc V.self A.∷ V.suc (zero-position (Y.tree νp)) A.∷ A.[])

-- D 可以来自任何运行；仅要求排除 Small 派发对当前 Ω 目标的需求。
seed-check : ∀ {D} →
  (∀ {x} → Small x → D x (Y.tree R.ν) → ⊥) →
  InvD D (R.ν ∷ Y.zero ∷ []) R.seed-tree
seed-check exclude = demanded R.seed-context λ where
  f (here refl) d → ⊥-elim (exclude (small-suc (seed-fields f)) d)
  f (there (here refl)) d → zero-common (dispatch R.seed-tree f)
  f (there (there ())) d

prefix-seed-check : ∀ {D} →
  (∀ {x} → Small x → D x (Y.tree νp) → ⊥) →
  InvD D (νp ∷ Y.zero ∷ []) seedp
prefix-seed-check exclude = demanded prefix-context λ where
  f (here refl) d → ⊥-elim (exclude (small-suc (seedp-fields f)) d)
  f (there (here refl)) d → zero-common (dispatch seedp f)
  f (there (there ())) d
```

seed-check 与 prefix-seed-check 的排除前提由下一篇冻结 Actual 的定理实填，
不把“字段 Small”本身当作树上可判定全序，也没有 γ 保持结论。
