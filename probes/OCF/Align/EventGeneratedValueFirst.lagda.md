# 原高事件首反馈的结构参数耦合

对任意合法最高层、源层、回调、状态及两份完整相关历史，第一
κ₁ 格读取状态的原第二层输出，再追加其 RB 事件。不是只求值 n1，
也不是把新高槽擦成零。下一格仍需要真实输出关系，本文不略去。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedValueFirst where

open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Align.CumReadCF using (Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnCodeIf using (Shape; sz)
open import OCF.Align.EventReturnValueEvent using (HistLow; empty; forget-left)
open import OCF.Align.EventReturnCtxValueIf using (R₂; ra; rz)
open import OCF.Align.EventGeneratedValueReplay
import OCF.Align.EvFoldClosed as Closed
import OCF.Align.EvFoldNew as New
import OCF.Align.EventReturnCtxValueActual as Action

module At (Λ : Ht) (lΛ : LgB Λ)
  (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ) (o₂ : ∀ {w} → hs (hs hz) ⊲[ w ] Λ) where
  module R = Closed.At Λ lΛ o₁ o₂
  module N = New.Top Λ lΛ o₁ o₂
  module A = Action.At Λ lΛ o₁ o₂
  open R

  first : ∀ {a H ly} (ac : AccY ly) (u : Bu ly (a , H)) (la : Lg a) →
    LW ly (a , H) → D ly (a , H) → St (a , H) → Hist
  first ac u la ll w Y = hc (κcε ac κ₁ u ≤rf (la , tt) ll Act w Y zero)

  first-related : ∀ {a H H′ ly} (ac ac′ : AccY ly)
    (u : Bu ly (a , H)) (u′ : Bu ly (a , H′)) (la : Lg a)
    (ll : LW ly (a , H)) (ll′ : LW ly (a , H′))
    (w : D ly (a , H)) (w′ : D ly (a , H′))
    (Y : St (a , H)) (Y′ : St (a , H′)) →
    HistoryShape H H′ → R₂ a H H′ (z₂ Y) (z₂ Y′) →
    HistoryShape (first ac u la ll w Y) (first ac′ u′ la ll′ w′ Y′)
  first-related ac ac′ u u′ la ll ll′ w w′ Y Y′ histories states =
    cons (event₁ la states) histories

  entered : ∀ {a H} → Lg a → St (a , H)
  entered la = Y₀ ⊕⟨ (la , tt) ⟩ Stp Y₀

  entered-related : ∀ {a H H′} (la : Lg a) →
    R₂ a H H′ (z₂ (entered {H = H} la)) (z₂ (entered {H = H′} la))
  entered-related la = ra rz (A.step-related la {Y = Y₀} {Y′ = Y₀} rz)

  -- 原 Ωd 的 n1 前缀进入闭包时正是这个状态形状。
  entered-first : ∀ {a H H′ ly} (ac ac′ : AccY ly)
    (u : Bu ly (a , H)) (u′ : Bu ly (a , H′)) (la : Lg a)
    (ll : LW ly (a , H)) (ll′ : LW ly (a , H′))
    (w : D ly (a , H)) (w′ : D ly (a , H′)) → HistoryShape H H′ →
    HistoryShape (first ac u la ll w (entered la))
                 (first ac′ u′ la ll′ w′ (entered la))
  entered-first ac ac′ u u′ la ll ll′ w w′ p =
    first-related ac ac′ u u′ la ll ll′ w w′ (entered la) (entered la) p (entered-related la)

  entered-high : ∀ {a H} (la : Lg a) →
    New.HasH (proj₁ (RB κ₁ {a , H} (la , tt) (z₂ (entered la))))
  entered-high la = N.first-new (la , tt) Y₀ Y₀

  entered-event : ∀ {a} → Lg a → Ev
  entered-event {a} la = evRB κ₁ {a , []} (la , tt) (z₂ (entered la))

  low-erasure : ∀ {a} (la : Lg a) → HistLow (entered-event la ∷ []) []
  low-erasure la = forget-left _ _ empty

  has-no-zero : ∀ {x : H₁} → New.HasH x → Shape x hz → ⊥
  has-no-zero h sz = h

  -- 实际新事件可以在低重放中遗忘，但不能在高重放中冒充底支。
  high-not-erased : ∀ {a} (la : Lg a) →
    Shape (rp (entered-event la ∷ []) (hs hz) hself) (rp [] (hs hz) hself) → ⊥
  high-not-erased la = has-no-zero
    (New.has-⊞ hz (proj₁ (RB κ₁ (la , tt) (z₂ (entered la)))) (entered-high la))

  -- 接口消费这个全 κ 结论，而不只消费 κ₀ 的低重放。
  first-replay : ∀ κ {a H H′ ly} (ac ac′ : AccY ly)
    (u : Bu ly (a , H)) (u′ : Bu ly (a , H′)) (la : Lg a)
    (ll : LW ly (a , H)) (ll′ : LW ly (a , H′))
    (w : D ly (a , H)) (w′ : D ly (a , H′)) → HistoryShape H H′ →
    Shape (rp (first ac u la ll w (entered la)) (proj₁ κ) (proj₂ κ))
          (rp (first ac′ u′ la ll′ w′ (entered la)) (proj₁ κ) (proj₂ κ))
  first-replay κ ac ac′ u u′ la ll ll′ w w′ p =
    replay κ (entered-first ac ac′ u u′ la ll ll′ w w′ p)

module Concrete = At Closed.three tt (hsuc (hsuc hself)) (hsuc hself)
```

这些不是新序数高度界。下一轮若采用生成域证明，需要对原回调
产生的异层 ni 坐标、Ai/BNi 的上下文及 Chn/κcε 的后继状态建立
同一关系闭包；不能把 first-related 的状态前提循环当成已满足。
