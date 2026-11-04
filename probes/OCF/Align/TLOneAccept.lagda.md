# `tH` 实验 (六): 验收, 记号只在本文件

> 入口 [TLOne](TLOne.lagda.md). **时间线:** 这个文件在 `TLOneDef`, `TLOneLeaf`, `TLOneThm` 编译之后才写; 写它之前没有打开过 `CrossMAccept`, `CrossNextAccept`, `EBO`. **只有关于记号的定理, 树与记号之间没有定理** (`no-val-T⊤` 说前驱结构验收在这一站就过不了; 序数值验收在这一站也没有参照物).
>
> 记 $u$ = `ψ₁ Ω₁` $=\Omega^2$. 下面的 `<` 是记号的 `cmpᵀ` 算出来的, 比较器 `refl`, 对写明的几个闭项, 不是对一切项.
>
> | 定理 | 陈述 |
> | --- | --- |
> | `fs-0`, `fs-1`, `fs-2′` | $\psi_0(\Omega_{u+1})$ 的前三项: $\psi_0(\Omega_u)$, $\psi_0(\psi_u(\Omega_u))$, $\psi_0(\psi_u(\psi_u(\Omega_u)))$ |
> | `lt-a`, `lt-b`, `lt-c`, `lt-d` | $\psi_0(\Omega_u)<\psi_0(\Omega_u+\Omega_u)<\psi_0(\psi_u(\Omega_u))<\psi_0(\Omega_{u+1})$ |
> | `lt-3` | $\psi_0(\Omega_u\cdot 3)<\psi_0(\psi_u(\Omega_u))$ |
> | `fs-2` (在 `CrossNextAccept`) | $\psi_0(\Omega_u+\Omega_u)$ 是 $y\mapsto\psi_0(\Omega_u+\Omega_{\psi_1(y)})$ 的闭包 |
>
> **这些定理支持的判断 (判断, 不是定理).** 见 [TLOne](TLOne.lagda.md) 的读法一节: 世界内的原则版都不超过 $\psi_0(\Omega_u\cdot 2)$, 这低于 $\psi_0(\Omega_{u+1})$ 基本列的第 1 项.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOneAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EBO using (T; ψ; Ωt; Ωs; natT; fsn; cmpᵀ; lt)
open import OCF.Align.CrossMAccept using (u; ψ₀; ψ₁; tψΩ; tψΩ1)
open import OCF.Align.CrossNextAccept using (t₂)

Ωᵤ : T
Ωᵤ = Ωt u

ψᵤ : T → T
ψᵤ a = ψ u a ∷ []

fs-0 : fsn tψΩ1 0 ≡ ψ₀ Ωᵤ
fs-0 = refl

fs-1 : fsn tψΩ1 1 ≡ ψ₀ (ψᵤ Ωᵤ)
fs-1 = refl

fs-2′ : fsn tψΩ1 2 ≡ ψ₀ (ψᵤ (ψᵤ Ωᵤ))
fs-2′ = refl

lt-a : cmpᵀ tψΩ t₂ ≡ lt
lt-a = refl

lt-b : cmpᵀ t₂ (fsn tψΩ1 1) ≡ lt
lt-b = refl

lt-c : cmpᵀ (fsn tψΩ1 1) tψΩ1 ≡ lt
lt-c = refl

lt-d : cmpᵀ t₂ tψΩ1 ≡ lt
lt-d = refl

t₃ : T
t₃ = ψ [] (ψ u [] ∷ ψ u [] ∷ ψ u [] ∷ []) ∷ []

lt-3 : cmpᵀ t₃ (fsn tψΩ1 1) ≡ lt
lt-3 = refl
```
