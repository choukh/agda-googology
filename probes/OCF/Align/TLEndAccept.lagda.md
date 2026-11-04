# 世界内的构造有没有封顶 (五): 事后对照, 记号只在本文件

> 入口 [TLEnd](TLEnd.lagda.md). **时间线:** 这个文件在 `TLEndCap`, `TLEndNeg`, `TLEndWord`, `TLEndTop` 编译之后才写. 这一轮没有再打开 `EBO`, 但上一轮 (`TLOneAccept`) 已经读过 `fs-1`, `fs-2`, `lt-b`, 所以类的选择不是盲的. **树与记号之间没有定理.** 比较器 `refl`, 只比写明的闭项.
>
> 对照的问题: 判断里 `Cap` 不超过 $\psi_0(\Omega_u\cdot2)$. 这里只核对记号一侧: 回灌一步对应的项 $\psi_0(\Omega_u+\Omega_{\psi_1(x)})$ 在 $\psi_0(\Omega_u\cdot2)$ 之下, $x$ 取几个闭项.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLEndAccept where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EBO using (T; ψ; natT; fsn; cmpᵀ; lt)
open import OCF.Align.CrossMAccept using (u; ψ₀; ψ₁; tψΩ; tψΩ1)
open import OCF.Align.CrossNextAccept using (t₂)

-- ψ₀(Ω_u + Ω_{ψ₁(x)})
fd : T → T
fd x = ψ [] (ψ u [] ∷ ψ (ψ₁ x) [] ∷ []) ∷ []

lt₀ : cmpᵀ tψΩ (fd (natT 1)) ≡ lt
lt₀ = refl

lt₁ : cmpᵀ (fd (natT 1)) t₂ ≡ lt
lt₁ = refl

-- x 取 ψ₀(Ω_u) 自己: 喂闭包点一次
lt₂ : cmpᵀ (fd tψΩ) t₂ ≡ lt
lt₂ = refl

-- 再喂一次
lt₃ : cmpᵀ (fd (fd tψΩ)) t₂ ≡ lt
lt₃ = refl

-- 这些都低于 ψ₀(Ω_{u+1}) 的第 1 项
lt₄ : cmpᵀ t₂ (fsn tψΩ1 1) ≡ lt
lt₄ = refl
```
