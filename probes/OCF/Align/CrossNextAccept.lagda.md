# 跨段, 下一步: 验收 (记号只在本文件)

> 入口 [CrossNext](CrossNext.lagda.md). 记号一侧的事实, 用来写 "闭合的链不够" 那个判断. **树与记号之间没有定理.**
>
> - `fs-2 n`: $\psi_0(\Omega_u+\Omega_u)[n]=\psi_0(\Omega_u+\Omega_{\psi_1(\gamma_n)})$, $\gamma_0=1$, $\gamma_{n+1}=\psi_0(\Omega_u+\Omega_{\psi_1(\gamma_n)})$. 链依赖项: 与 `CrossMAccept` 的 `fs-ψΩ` 的 $\gamma$ 不是同一条.
>
> 比较器: 定理, 只比记号的项. 盲区: 不说树.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossNextAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.EBO using (T; ψ; Ωt; natT; fsn)
open import OCF.Align.CrossMAccept using (u; ψ₀; ψ₁)

t₂ : T
t₂ = ψ [] (ψ u [] ∷ ψ u [] ∷ []) ∷ []

γ₂ : ℕ → T
γ₂ zero = natT 1
γ₂ (suc n) = ψ [] (ψ u [] ∷ ψ (ψ₁ (γ₂ n)) [] ∷ []) ∷ []

fs-2 : ∀ n → fsn t₂ n ≡ ψ [] (ψ u [] ∷ ψ (ψ₁ (γ₂ n)) [] ∷ []) ∷ []
fs-2 zero = refl
fs-2 (suc n) = cong (λ z → ψ [] (ψ u [] ∷ ψ (ψ₁ z) [] ∷ []) ∷ []) (fs-2 n)
```
