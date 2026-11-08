# 阶段覆盖是充分条件，不是一般值比较的必要条件

本文件给出非空的显式反例，防止终点验收把“每站落在某个候选分支”
偷偷升级成必要条件。两棵树都有值 ω，但其中一棵的每个顶层分支都是 ω，
另一棵的每个顶层分支都是有限数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaTargetCofinal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Align.Level using (Ordᶜ; zero; suc; lim)
open import OCF.Align.Value using
  (_≼_; _≈ᵛ_; l≼; ≼l; ≼-refl; ≼-trans; s≼s⁻; s≼0)

fin : ℕ → Ordᶜ zero
fin zero = zero
fin (suc n) = suc (fin n)

omega : Ordᶜ zero
omega = lim fin

repeated : ℕ → Ordᶜ zero
repeated _ = omega

same-value : lim repeated ≈ᵛ lim fin
same-value = l≼ (λ _ → ≼-refl omega) , ≼l 0 (≼-refl omega)

finite-gap : ∀ n → suc (fin n) ≼ fin n → ⊥
finite-gap zero p = s≼0 p
finite-gap (suc n) p = finite-gap n (s≼s⁻ p)

omega-not-finite : ∀ n → omega ≼ fin n → ⊥
omega-not-finite n p = finite-gap n
  (≼-trans (≼l (suc n) (≼-refl (fin (suc n)))) p)

no-stage-cover : (∀ n → Σ ℕ (λ k → repeated n ≼ fin k)) → ⊥
no-stage-cover c with c 0
... | k , p = omega-not-finite k p
```

反例否定的是一般的“极限值比较推出整支覆盖”命题，不声称 EBO 各站
在任何候选上都无覆盖。它说明 `LambdaTarget.Lower` 的定义域应保留
整个候选，不能无证明地换成 `StageCover`。这不要求改变任何候选定义。
