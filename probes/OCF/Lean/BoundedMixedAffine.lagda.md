# 同层反馈坐标的固定前缀动作

顶层坐标回灌若只遇到保留种类，其动作应归约到下面的统一变换。
定义及定理对任意种类结构、任意前缀成立，不按有限层逐站添加。
本篇不假设原运行器已经等于该动作；实际分类桥必须另证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedMixedAffine where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)

module Action (S : KS) (a : HB S) where
  run : HB S → HB S
  run hz = a
  run (hs c) = Ops.repeat S (run c)
  run (hl f) = hl (λ n → run (f n))
  run (hΩ κ g) = hΩ κ (λ e → run (g e))

  position : ∀ {c d W} → c ⊲[ W ] d → run c ⊲[ W ] run d
  position hself = hself
  position (hsuc p) = ⊲ᴮ-tr (position p) (hlim zero hself)
  position (hlim n p) = hlim n (position p)
  position (hLim b p) = hLim b (position p)

  legal : LgB a → ∀ c → LgB c → LgB (run c)
  legal la hz l = la
  legal la (hs c) l = LegalSum.sum-legal S _ (λ n → legal la c l)
  legal la (hl f) (st , l) = (λ n → position (st n)) , (λ n → legal la (f n) (l n))
  legal la (hΩ κ g) (mo , l) =
    (λ lw b b′ p → position (mo lw b b′ p)) ,
    (λ lw b → legal la (g _) (l lw b))

  chain : ℕ → HB S
  chain zero = hs hz
  chain (suc n) = chain n ⊞ run (chain n)

  legal-chain : LgB a → ∀ n → LgB (chain n)
  legal-chain la zero = tt
  legal-chain la (suc n) = Lg-⊞ (chain n) (run (chain n))
    (legal-chain la n) (legal la (chain n) (legal-chain la n))

  chain-step : ∀ n {W} → chain n ⊲[ W ] chain (suc n)
  chain-step n = ⊞-fst (chain n) (run (chain n))
```

坐标可以包含 S 的全部 Ω 种类。position 不读世界合法性，legal 只在
原 LgB 要求的分支处使用合法世界。实际最高反馈目标的种类是否全部
保留，以及其隐式路径是否与本篇坐标类型一致，仍由运行器桥验收。
