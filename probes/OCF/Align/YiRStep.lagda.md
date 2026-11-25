# 起点与原 Ω_Ω 的分支相对路径

旧全树单界证据可以转成新路径证据，但新证据不反过来要求旧的全局界。
原 Ω_Ω 的每个零层合法分支独立选择读回树作新界，因此第五轮的两个字段
不再需要互相比：它们各自在自己的分支上下文中。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRStep where

open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import OCF.Align.LevelFixCore using (LF; Raw; Gd)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (CP; CP-tr; Legal)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
import OCF.Align.YiCtxStep as S
open import OCF.Align.YiRBase
open import OCF.Align.YiRCountable using (Fields; raw0-omega-fields)

fields-path : ∀ B t → Fields (Y.tree B) t → Path B t
fields-path B F.zero p = tt
fields-path B (F.suc t) p = fields-path B t (λ f → p (K.in-suc f))
fields-path B (F.lim f) p = λ n → fields-path B (f n) (λ q → p (K.in-lim n q))
fields-path B (F.lc k c t g) p = p K.at ,
  fields-path B t (λ f → p (K.in-first f)) ,
  (λ η e → B , V.self , fields-path B (g η e) (λ f → p (K.in-branch η e f)))

of-global : ∀ {E current} → K.Inv E current → InvR E current
of-global {current = current} i = relative (K.context i)
  (fields-path (K.bound (K.context i)) (Y.tree current) (K.field-pos i))

start : InvR (Y.zero ∷ []) S.Ω₁
start = of-global S.start

coordinate : (η : Raw F.zero) → Gd F.zero (V.cO F.zero) η → Y.Level
coordinate η e = Y.level (V.up F.zero η) (V.lgl→Legal F.zero tt η (proj₂ e))

coordinate-after-one : ∀ η e → CP (F.suc F.zero) (Y.tree (coordinate η e))
coordinate-after-one η e = V.cp→CP F.zero (proj₁ e)

branch-path : ∀ η e → Path (coordinate η e) (V.Ω̂ (V.up F.zero η))
branch-path η e = fields-path (coordinate η e) (V.Ω̂ (V.up F.zero η)) (raw0-omega-fields η)

ΩΩ : Y.Level
ΩΩ = Y.Ω S.Ω₁

omega-omega : Path (Y.suc Y.zero) (Y.tree ΩΩ)
omega-omega = V.self , path start ,
  (λ η e → coordinate η e , coordinate-after-one η e , branch-path η e)

omega-omega-inv : InvR (Y.zero ∷ []) ΩΩ
omega-omega-inv = relative (K.context S.start) omega-omega

branch-legal : ∀ {k c t g} → Legal (F.lc k c t g) → ∀ η e → Legal (g η e)
branch-legal (lk , first , mono , same , lt , lg) η e = lg η e

-- 给真正选中的分支运输整个环境。B′由该支的证据计算，不给其它支公共界。
enter : ∀ {E k c t g} (lawful : Legal (F.lc k c t g)) →
  (i : InvR E (Y.level (F.lc k c t g) lawful)) → ∀ η e →
  InvR E (Y.level (g η e) (branch-legal lawful η e))
enter lawful i η e with proj₂ (proj₂ (path i)) η e
... | B′ , p , q = relative (S.raise-ctx (context i) B′ p) q
```
