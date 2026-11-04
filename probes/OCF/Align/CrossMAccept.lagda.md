# 跨段: 验收 (记号只在本文件)

> 入口 [CrossM](CrossM.lagda.md). 记号一侧的事实, 用来写读法; **没有标签, 树与记号之间没有定理.**
>
> - `fs-ψΩ n` (定理, 只关于记号): $\psi_0(\Omega_{\psi_1(\Omega)})[n]=\psi_0(\Omega_{\psi_1(\gamma_n)})$, 其中 $\gamma_0=1$, $\gamma_{n+1}=\psi_0(\Omega_{\psi_1(\gamma_n)})$. 也就是说, 记号的基本列就是 "高度 $\mapsto$ 第 0 行" 的回灌链, 与 $\gamma$-链的形状相同.
> - `cofψ₁Ω`: 下标 $\psi_1(\Omega)$ 的共尾度是 $\Omega_1$; `cof-top`: 整个项的共尾度是 $\omega$ (规则 6).
> - `fs-ψΩ1-0`, `fs-ψΩ1-1`: 下一个项 $\psi_0(\Omega_{\psi_1(\Omega)+1})$ 的基本列不是这条链: 走的是 $\Omega_{\psi_1(\Omega)}$ 上的折叠, 第 1 项是 $\psi_0(\psi_{u}(\Omega_u))$, 下标 $u=\psi_1(\Omega)$ 字面地出现. 这正是节点不在 `Q` 里时拿不到的东西 (判断).
>
> **比较器与盲区.** `fs-ψΩ` 只比记号的项. 树的第 $n$ 个分支是 $C_n$ 上的第 0 行, 高度的值 $\lVert C_n\rVert$ 只是沿 `Fix` 与输出互相共尾 (定理), 不等于 $\omega^{\gamma_n}$; 树的基本列与记号不逐项一致. 所以这里 **没有** `Lab`, 只支持读法的形状: 同一条回灌链, 同一个闭包点 (判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.EBO using (T; ψ; 𝟏; Ωt; Ωs; natT; sucT; cof; cω; cΩ; fsn)

one : T
one = natT 1

Ω₁ : T
Ω₁ = Ωs []

ψ₀ ψ₁ : T → T
ψ₀ a = ψ [] a ∷ []
ψ₁ a = ψ one a ∷ []

u : T
u = ψ₁ Ω₁

tψΩ : T
tψΩ = ψ₀ (Ωt u)

γ : ℕ → T
γ zero = natT 1
γ (suc n) = ψ₀ (Ωt (ψ₁ (γ n)))

cofψ₁Ω : cof u ≡ cΩ []
cofψ₁Ω = refl

cof-top : cof tψΩ ≡ cω
cof-top = refl

fs-ψΩ : ∀ n → fsn tψΩ n ≡ ψ₀ (Ωt (ψ₁ (γ n)))
fs-ψΩ zero = refl
fs-ψΩ (suc n) = cong (λ z → ψ₀ (Ωt (ψ₁ z))) (fs-ψΩ n)
```

## §2 下一个项

```agda
tψΩ1 : T
tψΩ1 = ψ₀ (Ωs u)

-- 第 0 项是 ψ₀(Ω_u)
fs-ψΩ1-0 : fsn tψΩ1 0 ≡ ψ₀ (Ωt u)
fs-ψΩ1-0 = refl

-- 第 1 项: 把 Ω_u 折叠进去, 下标 u 字面出现
fs-ψΩ1-1 : fsn tψΩ1 1 ≡ ψ₀ (ψ u (Ωt u) ∷ [])
fs-ψΩ1-1 = refl
```
