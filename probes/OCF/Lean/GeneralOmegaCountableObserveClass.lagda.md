# 共同可数界上的实际分类与合法地板

先检验分类实际可用而非空记录。ω高度的同一组件给同层坍缩和原样
保留两例；两后继高度另给在上分支。地板合法性对全部Cd高度成立，
不假设不同sup分量之间能逐点比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObserveClass where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.LHRecFl using (Lg-up; up-⊲; Lg-ι)

floor-legal : ∀ B → LgB (floor B)
sum-legal : ∀ f n → LgB (C.ΣT S⊥ (hs hz) f n)
floor-legal hz = tt
floor-legal (hs B) =
  (λ lw b b′ p → up-⊲ p) ,
  (λ {W} {c} lw b → Lg-up c (lgB⊲ b (proj₁ lw) (proj₂ lw)))
floor-legal (hl f) =
  (λ n → ⊞-fst (C.ΣT S⊥ (hs hz) f n) (ι (suc n) (floor (f (suc n))))) , sum-legal f
floor-legal (hΩ () f)
sum-legal f zero = Lg-ι zero (floor (f zero)) (floor-legal (f zero))
sum-legal f (suc n) = Lg-⊞ _ _ (sum-legal f n)
  (Lg-ι (suc n) (floor (f (suc n))) (floor-legal (f (suc n))))

num : ℕ → Cd
num zero = hz
num (suc n) = hs (num n)
num-legal : ∀ n → LgB (num n)
num-legal zero = tt
num-legal (suc n) = num-legal n
omega : Cd
omega = hl num
omega-legal : LgB omega
omega-legal = (λ n → hsuc hself) , num-legal

omega-same : classify omega omega-legal hz (hlim 1 (hsuc hself)) (1 , inj₂ tt) ≡ C.same (λ c → c)
omega-same = refl
omega-keep : classify omega omega-legal (hs hz) (hlim 1 hself) (1 , inj₂ tt) ≡ C.keep (inj₂ tt) (λ c → c)
omega-keep = refl
finite-above : classify (hs (hs hz)) tt hz (hsuc (hsuc hself)) (inj₂ tt) ≡
  C.above (hs hz) hself (hsuc hself) (λ c → c)
finite-above = refl
```

这些是编译等式，不是有限测试；它们仅示范共享接口分派可满足。
floor-legal覆盖整个高度族，旧typed限层逐点floor的值关系仍未证明。
