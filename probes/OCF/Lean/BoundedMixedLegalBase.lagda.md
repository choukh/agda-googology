# 有限动作归纳的基层：任意前缀后的旧层作用

前缀保持为实际源树，仍用原Fold，不新建解释器。这里只证明递归基，
不是把全n任务退回第一项；更高反馈生成坐标的单调字段尚待证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedMixedLegalBase where
open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (T; P)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.BoundedMixedLegalIf

module Action (A : HB S) where
  run : HB (T hz) → HB (T hz)
  run c = Fold.fold hz (z⊲ᴮ _) (A ⊞ put zero c)

  position : ∀ {a b W} → a ⊲[ W ] b → run a ⊲[ W ] run b
  position hself = hself
  position (hsuc p) = ⊲ᴮ-tr (position p) (hlim zero hself)
  position (hlim n p) = hlim n (position p)
  position (hLim b p) = hLim b (position p)

  legal : LgB (Fold.fold hz (z⊲ᴮ _) A) → ∀ c → LgB c → LgB (run c)
  legal lA hz l = lA
  legal lA (hs c) l = LegalSum.sum-legal (T hz) _ (λ n → legal lA c l)
  legal lA (hl f) (st , l) = (λ n → position (st n)) , (λ n → legal lA (f n) (l n))
  legal lA (hΩ κ g) (mo , l) =
    (λ lw b b′ p → position (mo lw b b′ p)) ,
    (λ lw b → legal lA (g _) (l lw b))

module Initial = Action hz

initial-legal : ∀ c → LgB c → LgB (Initial.run c)
initial-legal c l = Initial.legal tt c l
```

position对所有目标world成立，未借用其合法性；legal只在原LgB要求的
Ω分支处使用合法world。前缀前提可由A=hz及已有第一部分和分别实例化。
