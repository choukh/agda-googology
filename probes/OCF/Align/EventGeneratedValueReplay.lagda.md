# 保留高反馈事件的全重放关系

HistLow 的遗忘高事件律只适用于低界；动态节点种类会读取 κ₁ 界，
这里改用完整同步事件表。每个实际事件仍只比较同一个有证 kind 的
payload Shape，不使用事件相等。结论保留两个原重放槽，不取底支。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedValueReplay where

open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import OCF.Align.CumReadCF using (Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)
open import OCF.Align.EventReturnValueEvent using (EventShape; same-kind)
open import OCF.Align.EventReturnReplay using (add-shape)
open import OCF.Align.EventReturnCtxValueIf using (R₂)
import OCF.Align.EventReturnCtxValueRun as V₂
open import OCF.Align.EventReturnCtxIf using (R₁)
import OCF.Align.EventReturnCtxActual as V₁

data HistoryShape : Hist → Hist → Set where
  nil : HistoryShape [] []
  cons : ∀ {e e′ H H′} → EventShape e e′ → HistoryShape H H′ →
    HistoryShape (e ∷ H) (e′ ∷ H′)

up-shape : ∀ {x y : H₀} → Shape x y → Shape (up x) (up y)
up-shape sz = sz
up-shape (ss p) = ss (up-shape p)
up-shape (sl p) = sl (λ n → up-shape (p n))
up-shape (so p) = so (λ e → up-shape (p e))

replay : ∀ κ {H H′} → HistoryShape H H′ →
  Shape (rp H (proj₁ κ) (proj₂ κ)) (rp H′ (proj₁ κ) (proj₂ κ))
replay κ nil = sz
replay (_ , hself) (cons (same-kind _ hself lx ly p) q) =
  add-shape (replay (_ , hself) q) p
replay (_ , hself) (cons (same-kind _ (hsuc hself) lx ly p) q) =
  add-shape (replay (_ , hself) q) (up-shape p)
replay (_ , hsuc hself) (cons {H = H} {H′ = H′} (same-kind _ hself lx ly p) q) =
  replay (_ , hsuc hself) {H} {H′} q
replay (_ , hsuc hself) (cons (same-kind _ (hsuc hself) lx ly p) q) =
  add-shape (replay (_ , hsuc hself) q) p

event₀ : ∀ {a H H′ x y} (la : Lg a) → R₁ a H H′ x y →
  EventShape (evRB κ₀ {a , H} (la , tt) x) (evRB κ₀ {a , H′} (la , tt) y)
event₀ la p = same-kind hz (hsuc hself) (Lg-rd₁ (la , tt) hz _ tt)
  (Lg-rd₁ (la , tt) hz _ tt) (V₁.observe la p sz)

event₁ : ∀ {a H H′ x y} (la : Lg a) → R₂ a H H′ x y →
  EventShape (evRB κ₁ {a , H} (la , tt) x) (evRB κ₁ {a , H′} (la , tt) y)
event₁ la p = same-kind (hs hz) hself (Lg-rd₂ (la , tt) hz _ tt)
  (Lg-rd₂ (la , tt) hz _ tt) (V₂.observe la p sz)
```

`event₁` 消费真实第二层输出的关系，不能由仅知低界相关来替代。
这样新高事件的 payload 确由原 RB 读回决定，未把它换成地板或常数。
