# 真实中间输出合法：不经过末层兜底

本篇补上 `FrozenOmegaClosed.intermediate` 的直接合法性。
依赖实际含旧 Ω 的分支作用，而非以最低层 total-fold 反推。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.FrozenLegalClosed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenOmegaIf
open import OCF.Lean.FrozenOmegaRun using (chain; diagonal)
open import OCF.Lean.FrozenOmegaClosed using (U; w; M; input; intermediate; module F)
open import OCF.Lean.FrozenLegalIf
open import OCF.Lean.FrozenLegalBase
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)

module _ {S : KS} {v : Wd S} {m : HB S} where
  erase-position : ∀ {a b V} → a ⊲[ V ] b → erase {S} {v} {m} a ⊲[ V ] erase b
  erase-position hself = hself
  erase-position (hsuc p) = hsuc (erase-position p)
  erase-position (hlim n p) = hlim n (erase-position p)
  erase-position (hLim e p) = hLim e (erase-position p)

  erase-legal : ∀ a → LgB a → LgB (erase {S} {v} {m} a)
  erase-legal hz l = tt
  erase-legal (hs a) l = erase-legal a l
  erase-legal (hl f) (s , l) = (λ n → erase-position (s n)) , (λ n → erase-legal (f n) (l n))
  erase-legal (hΩ (κ , p) g) (s , l) =
    (λ lw e e′ q → erase-position (s lw e e′ q)) ,
    (λ lw e → erase-legal (g _) (l lw e))

next : HB U → HB U
next c = erase (act c)
next-legal : ∀ c → LgB c → LgB (next c)
next-legal c l = erase-legal (act c) (act-legal c l)

orbit-legal : ∀ n → LgB (chain {B = SafeTw U w hz} next n)
orbit-legal zero = tt
orbit-legal (suc n) = Lg-⊞ (chain {B = SafeTw U w hz} next n) (next (chain {B = SafeTw U w hz} next n))
  (orbit-legal n) (next-legal (chain {B = SafeTw U w hz} next n) (orbit-legal n))

safe-intermediate-legal : LgB (F.fold hz (z⊲ᴮ M) input)
safe-intermediate-legal = LegalSum.sum-legal (SafeTw U w hz) _
  (λ n → act-legal (chain {B = SafeTw U w hz} next n) (orbit-legal n))

intermediate-legal : LgB intermediate
intermediate-legal = erase-legal (F.fold hz (z⊲ᴮ M) input) safe-intermediate-legal
```

该结论只覆盖上一轮的实际闭项及其 base 分支族。没有通用受限树保合法
定理，也没有大小定理；固定可入分量 1 的限制依旧。
