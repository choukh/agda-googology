# 树侧判据: `Z` 读成观察树

> 不含记号. `OCF.Free.Prefix` 那一份 `Z` 的 `rd`. 工具, 不是定理. 见 [TreeJudgeObs](TreeJudgeObs.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeJudgeRead where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Level using (Ordᴵ; _⊑ᴵ_; ⊑ᴵ-refl; ⊑ᴵ-trans; Sim→⊑ᴵ)
import OCF.Free.Level as FL
open import OCF.Align.TreeJudgeObs using (Obs; o0; os; ol; oc)

toN : Ordᴵ → ℕ
toN FL.zero = 0
toN (FL.suc a) = suc (toN a)
toN (FL.lim f s) = toN (f 1)

iterᴵ : Ordᴵ → ℕ → Ordᴵ
iterᴵ c zero = c
iterᴵ c (suc k) = FL.suc (iterᴵ c k)

up⊑ : ∀ {c} k → c ⊑ᴵ iterᴵ c k
up⊑ {c} zero = ⊑ᴵ-refl
up⊑ (suc k) = ⊑ᴵ-trans (up⊑ k) (Sim→⊑ᴵ (λ q → FL.suc q))

rd : Z → Obs
rd Z.zero = o0
rd (Z.suc x) = os (rd x)
rd (Z.lim f) = ol (λ n → rd (f n))
rd (Z.ĉᴸ c t₀ g o₀ o) = oc (toN c) (rd t₀) (rd o₀) (λ k → rd (o (iterᴵ c k) (up⊑ k)))
```
