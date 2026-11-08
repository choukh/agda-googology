# 只保留可数树完成，不导入整塔折叠

本篇按原 CRw 的同一递归方程提供部分和、leg、第一位置合法性和 FGH。
不导入 CRw 的世界实例、塔折叠或路径闭包。原文件只读。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Free.LiteralCompletion where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase

Σ₀ : (ℕ → Cd) → ℕ → Cd
Σ₀ f zero = f 0
Σ₀ f (suc n) = Σ₀ f n ⊞ f (suc n)

leg : Cd → Cd
leg hz = hz
leg (hs a) = hs (leg a)
leg (hl f) = hl (Σ₀ (λ n → leg (f n)))
leg (hΩ () g)

Lg-leg : ∀ a → LgB (leg a)
Lg-sum : ∀ f n → LgB (Σ₀ (λ k → leg (f k)) n)
Lg-leg hz = tt
Lg-leg (hs a) = Lg-leg a
Lg-leg (hl f) = (λ n → ⊞-fst (Σ₀ (λ k → leg (f k)) n) (leg (f (suc n)))) , Lg-sum f
Lg-leg (hΩ () g)
Lg-sum f zero = Lg-leg (f 0)
Lg-sum f (suc n) = Lg-⊞ _ (leg (f (suc n))) (Lg-sum f n) (Lg-leg (f (suc n)))

iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f a zero = a
iter f a (suc n) = f (iter f a n)

FGH : Cd → ℕ → ℕ
FGH hz n = suc n
FGH (hs a) n = iter (FGH a) n n
FGH (hl f) n = FGH (f n) n
FGH (hΩ () g) n
```
