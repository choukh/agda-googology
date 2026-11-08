# 含旧 Ω 坐标的实际分支作用保合法

直接证明实际 act 的性质，不替换折叠定义，不用函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenLegalBase where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.FrozenOmegaClosed using (U; w)
open import OCF.Lean.FrozenLegalIf
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)

act-position : ∀ {a b v} → a ⊲[ v ] b → act a ⊲[ v ] act b
act-position hself = hself
act-position (hsuc p) = ⊲ᴮ-tr (act-position p) (hlim 0 hself)
act-position (hlim n p) = hlim n (act-position p)
act-position (hLim e p) = hLim e (act-position p)

act-legal : ∀ c → LgB c → LgB (act c)
act-legal hz l = tt
act-legal (hs c) l = LegalSum.sum-legal (SafeTw U w hz) _ (λ n → act-legal c l)
act-legal (hl f) (s , l) = (λ n → act-position (s n)) , (λ n → act-legal (f n) (l n))
act-legal (hΩ κ g) (s , l) =
  (λ lw e e′ p → act-position (s lw e e′ p)) ,
  (λ lw e → act-legal (g _) (l lw e))

instance-action : BaseAction
instance-action = record { position = act-position ; legal = act-legal }
```
