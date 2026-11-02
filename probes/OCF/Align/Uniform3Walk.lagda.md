# 统一形 (三) 的决定性小实验: 失败路径上的界

> 接 [OmegaSqA](OmegaSqA.lagda.md) §5. 这是决定修正是否值得做的最便宜的实验, 在移植任何标签理论之前做: 在**具体的**极限层号上比较 Uniform2 与 Uniform3 的折叠, 看路径 $[0,1,0,0,0]$ 之后的后继行第 2 份副本的弹栈的界. 全部 `refl`.
>
> 结论: 旧折叠的界是 $L_1+1$ (OmegaSqA 的 `MxL`), 新折叠的界是 $1$; 第 2 份副本的首个链点的层号 ($\psi_0(\Omega_\Omega+\Omega)$ 的层号) 不小于 $1$, 证书的 `d₀` 可满足. 沿途的树形 (`kl`, 第 1 份副本的 `kc 1`) 不变: 修正只改第 $\ge2$ 份副本读到的底地板.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform3Walk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Ordˢ; Ωˢ; kind; kl; kc; walkˢ)
import OCF.Align.Uniform2Base as U2
import OCF.Align.Uniform3Base as U3
```

## §1 层号: 路径 $[0,1,0,0,0]$ 到 $0$

$L_5=\omega$ (第 0 项是 $0$), $L_4=L_3=\dots$ 是常序列的极限 (退化序列正是字面证据问题的来源): $L_1[0]=L_2$, $L_2[1]=L_3$, $L_3[0]=L_4$, $L_4[0]=\omega$, $\omega[0]=0$.

```agda
L₄ L₃ L₂ L₁ : Ordᴵ
L₄ = Mlev ωᴵ ωᴵ ⊑ᴵ-refl
L₃ = Mlev L₄ L₄ ⊑ᴵ-refl
L₂ = Mlev L₃ L₃ ⊑ᴵ-refl
L₁ = Mlev L₂ L₂ ⊑ᴵ-refl

0<L₁ : zero <ᴵ L₁
0<L₁ = lim 0 (lim 1 (lim 0 (lim 0 (lim 1 zero))))

ℓ : Ordᴵ
ℓ = suc L₁

σ₁ : Simᴵ (suc zero) ℓ
σ₁ zero = suc 0<L₁
σ₁ (suc ())

σ₂ : Simᴵ (suc L₁) ℓ
σ₂ q = q
```

## §2 分支 $\psi_\Omega(\Omega_{L_1})$, 目标 $0$

```agda
br₂ : Ordˢ zero
br₂ = U2.fold 1 (U2.fk L₁) (λ e q → e (suc q)) (U2.Ω̂A 0) (Ωˢ L₁) U2.∅ᴿ (tt , (σ₁ , σ₂)) (suc 0<L₁)

br₃ : Ordˢ zero
br₃ = U3.fold 1 (U3.fk L₁) (λ e q → e (suc q)) (U3.Ω̂A 0) (Ωˢ L₁) U3.∅ᴿ (tt , (σ₁ , σ₂)) (suc 0<L₁)

path : ℕ → List ℕ
path m = 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ m ∷ []

-- Uniform2: 第 2 份副本的闭包的界是 L₁+1 (OmegaSqA §5 的 `MxL`)
_ : kind (walkˢ br₂ (path 2)) ≡ kc (suc L₁)
_ = refl

-- Uniform3: 地板在每个 up (self n) 处换成紧的; 到第 0 层地板是 fz, 界是 1
_ : kind (walkˢ br₃ (path 2)) ≡ kc (suc zero)
_ = refl

-- 第 3 份同样
_ : kind (walkˢ br₃ (path 3)) ≡ kc (suc zero)
_ = refl
```

**树形不变.** 沿途都是 $\omega$-极限, 第 1 份副本在旧底地板上 (`repA` 的设计), 两种折叠一致.

```agda
_ : kind (walkˢ br₂ (0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ br₃ (0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ br₂ (0 ∷ 1 ∷ 0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ br₃ (0 ∷ 1 ∷ 0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ br₂ (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ br₃ (0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ br₂ (path 1)) ≡ kc (suc zero)
_ = refl
_ : kind (walkˢ br₃ (path 1)) ≡ kc (suc zero)
_ = refl
```
