# 复合上下文中的动态搬运

新签名分别保留旧分量标签和新界分量标签。旧标签的上下文取复合，
不识别不同路径证明。世界关系若有增长证书就显式使用；没有证书时，
只对新世界的投影证明搬运，不反向求世界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedGrowthRun where
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL; pw; lgpw)
open import OCF.Lean.BoundedContextRun
open import OCF.Lean.BoundedContextTree
open import OCF.Lean.BoundedGrowthIf
import OCF.Lean.ContextPullback as CP

pw-compose : ∀ {T S R} (a : Ctx T S) (b : Ctx S R) W →
  pw (compose a b) W ≡ pw b (pw a W)
pw-compose a here W = refl
pw-compose a (viaS b) W rewrite pw-compose a b W = refl
pw-compose a (viaL b i) W rewrite pw-compose a b W = refl

module Grow (P k : LH) (w : Wd (Lv k)) (B C : HB (Lv k)) (r : B ⊲[ w ] C) where
  module Old = Family P k w B
  module Fresh = Family P k w C
  q = path-context P k r
  I = Old.I ⊎ Fresh.I
  F : I → KS
  F (inj₁ i) = Old.F i
  F (inj₂ i) = Fresh.F i
  ctx : ∀ i → Ctx Fresh.T (F i)
  ctx (inj₁ i) = compose q (Old.ctx i)
  ctx (inj₂ i) = Fresh.ctx i
  module New = CP.Pull F Fresh.T ctx

  bd-old : ∀ i κ {e W} → Bd New.S (inj₁ i , κ) e W →
    Bd Old.S (i , κ) e (pw q W)
  bd-old i κ {e} {W} = subst (λ v → Bd (Old.F i) κ e v) (pw-compose q (Old.ctx i) W)
  bd-new : ∀ i κ {e W} → Bd Old.S (i , κ) e (pw q W) →
    Bd New.S (inj₁ i , κ) e W
  bd-new i κ {e} {W} b rewrite pw-compose q (Old.ctx i) W = b
  pr-old : ∀ i κ {e e′ W} → Pr New.S (inj₁ i , κ) W e e′ →
    Pr Old.S (i , κ) (pw q W) e e′
  pr-old i κ {e} {e′} {W} = subst (λ v → Pr (Old.F i) κ v e e′) (pw-compose q (Old.ctx i) W)

  move : HB Old.S → HB New.S
  move hz = hz
  move (hs a) = hs (move a)
  move (hl f) = hl (λ n → move (f n))
  move (hΩ (i , κ) f) = hΩ (inj₁ i , κ) (λ c → move (f c))

  move-position : ∀ {a b W} → a ⊲[ pw q W ] b → move a ⊲[ W ] move b
  move-position hself = hself
  move-position (hsuc p) = hsuc (move-position p)
  move-position (hlim n p) = hlim n (move-position p)
  move-position {b = hΩ (i , κ) f} (hLim b p) = hLim (bd-new i κ b) (move-position p)

  move-legal : ∀ a → LgB a → LgB (move a)
  move-legal hz l = l
  move-legal (hs a) l = move-legal a l
  move-legal (hl f) (st , l) = (λ n → move-position (st n)) , (λ n → move-legal (f n) (l n))
  move-legal (hΩ (i , κ) f) (mo , l) =
    (λ lw b b′ p → move-position (mo (lgpw q lw) (bd-old i κ b) (bd-old i κ b′) (pr-old i κ p))) ,
    (λ lw b → move-legal (f _) (l (lgpw q lw) (bd-old i κ b)))

  witnessed-position : ∀ {W a b} (v : WorldGrowth P k w B C r W) →
    a ⊲[ W ] b → move a ⊲[ WorldGrowth.future v ] move b
  witnessed-position v p = move-position (⊲ᴮ↑ (WorldGrowth.extends v) p)

  result : HB Old.S → HB Fresh.T
  result a = New.embed (move a)
  result-legal : ∀ a → LgB a → LgB (result a)
  result-legal a l = New.embed-legal _ (move-legal a l)
```

`witnessed-position` 消费真实旧世界增长证书；`move-legal` 则对每个新
合法世界使用其旧世界投影。二者没有混同。尚无任意 Ω 路径世界扩张器。
