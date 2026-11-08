# 原共同可数界内的输出前缀位置

这条定理只比较原a与a⊞b在同一个观察器中的完整输出。它直接递归
右项b，Ω处取真实首反馈或保留种类的bot分支，不把源第一位置或
一般值序送过观察器。累计地板的相邻输出因而有原目标树的位置步进。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObservePrefix where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤s; ≤l; ≤Ω)
open import OCF.Lean.Fold1Base using (≤-refl)

prefix-position : ∀ B (lB : LgB B) t (pt : t ⊲ B) a b {w : Wd (F t)} →
  observe B lB t pt a ⊲[ w ] observe B lB t pt (a ⊞ b)
prefix-position B lB t pt a hz = hself
prefix-position B lB t pt a (hs b) = hlim 1 (prefix-position B lB t pt a b)
prefix-position B lB t pt a (hl f) = hlim zero (prefix-position B lB t pt a (f zero))
prefix-position B lB t pt a (hΩ κ f) {w} with classify B lB t pt κ
... | C.keep κ′ fr = hLim (botBd (F t) κ′ w)
  (prefix-position B lB t pt a (f (fr (bot (F t) κ′))))
... | C.same to = hlim zero (prefix-position B lB t pt a (f (to (floor t))))
... | C.above r pr tr to = hlim zero (prefix-position B lB t pt a (f (to (floor r))))

position-value : ∀ {S : KS} {a b : HB S} {w} → a ⊲[ w ] b → a ≤ᵛ b
position-value hself = ≤-refl _
position-value (hsuc p) = ≤s (position-value p)
position-value (hlim n p) = ≤l n (position-value p)
position-value (hLim {c = c} e p) = ≤Ω c (position-value p)

prefix-value : ∀ B (lB : LgB B) t (pt : t ⊲ B) a b →
  observe B lB t pt a ≤ᵛ observe B lB t pt (a ⊞ b)
prefix-value B lB t pt a b = position-value
  (prefix-position B lB t pt a b {w = bot-world t})
  where
  bot-world : ∀ t → Wd (F t)
  bot-world hz = tt
  bot-world (hs t) = bot-world t , hz
  bot-world (hl f) = λ n → bot-world (f n)
  bot-world (hΩ () f)

limit-step : ∀ f (lf : LgB (hl f)) t (pt : t ⊲ hl f) n {w : Wd (F t)} →
  observe (hl f) lf t pt (C.ΣT S⊥ (hs hz) f n) ⊲[ w ]
  observe (hl f) lf t pt (C.ΣT S⊥ (hs hz) f (suc n))
limit-step f lf t pt n = prefix-position (hl f) lf t pt (C.ΣT S⊥ (hs hz) f n) _
```

position-value仅将已经构造的目标位置读成值界；不是说观察器保持
源位置。limit-step不附带每个输出项合法或完成保值结论，也不将
孤立的右组件自动读作完整累计输出的下界。
