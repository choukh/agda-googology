# 统一形 (四): $\psi_0(\Omega_{\Omega+2})$ 的决定性实验

> 接 [Uniform3OmegaPlus1](Uniform3OmegaPlus1.lagda.md) §6. 只在现行的塔上做最小扩展, 与 EBO 逐路径对照. 结论先说:
>
> 1. **记号侧 (§1, 全部 `refl`).** $\psi_0(\Omega_{\Omega+2})[n]=\psi_0(\gamma_n)$, $\gamma_0=\Omega_{\Omega+1}$, $\gamma_{k+1}=\psi_{\Omega+1}(\gamma_k)$. $\psi_{\Omega+1}(\Omega_{\Omega+1})$ 走 `eq`: 共尾度仍是 $\Omega_{\Omega+1}$, 基本列逐点.
> 2. **(A) 是真的 (§2, 编译否定).** 朴素帧 `Ψ₁ᶰ Y d P = Y (suc d) (Ω⁺ ∅ᵀ d) P` 上 $\psi_0(\psi_{\Omega+1}(1))[2]$ 的第 2 份链点没有前一份. 路径 `[2,1,0,0,1]`: EBO 是 $\psi_0(\Omega_{\Omega+1}+\psi_\Omega(\Omega_{\Omega+1}))$, 实参的共尾度是 $\Omega_{\Omega+1}$, 树给 `kc one` (实参共尾度 $\Omega_1$, 字面是 $\psi_0(\Omega_{\Omega+1}+\Omega_\Omega)$).
> 3. **(B) 是真的 (§2, 编译否定).** $\psi_0(\psi_{\Omega+1}(\Omega_{\Omega+1}))[1]$ 应为 $\psi_0(\psi_{\Omega+1}(\psi_\Omega(\psi_{\Omega+1}(\Omega_\Omega))))$, 树的链点缺内层的 $\psi_{\Omega+1}$. 路径 `[1,0,0,1]`: EBO 的实参共尾度是 $\omega$, 树给 `kc one`.
> 4. **还有 (C), 任务单没有预言.** 把塔的底换成 `Sym` (`A⁺`) 只修第一层. (A) 的根源是 `fold (suc d)` 的后继子句 `repA`: $\psi_{\Omega+1}(a+1)$ 的第 $m$ 份在**值层**重放同一个帧, 而第 $m$ 份的链要含前 $m-1$ 份. 换成符号前缀之后, 尾巴 $\psi_\Omega(Z)$ 作用在 $\psi_{\Omega+1}$ 头的帧上时, `Ω̂A` 里的同一条后继子句又在值层重复, 要修就得让 $Z$ 作用于 `A⁺` 的塔; 而链点 $\psi_\Omega(W+\cdots)$ 含前缀 $W$, 于是 $W$ 也要能作用于 `A⁺`, 可 `A⁺` 的底正是 $W$ 的类型. 这是一个非良基的域方程 (纸面, §3). 编译证据: `S²ᶰ` (§2).
>
> **裁决: 帧式 (CPS) 的塔在 $\psi_{\Omega+1}$ 上是设计层的失败, 不是局部缺口.** 替代方案不再是塔, 见 [Uniform4Base](Uniform4Base.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4Expt where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; walkˢ; kind; kl; kc)
import OCF.Align.EBO as E
open E using (T; PT; fsn; fsT; cof; cω; cΩ; Ωt; 𝟏; sucT) renaming (ψ to ψᵗ)
open import OCF.Align.StandardOmega using (walk)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.OmegaExpBase using (γW; gtW)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import OCF.Align.OmegaPlus1Base using (Ω⁺¹)
open import OCF.Align.Uniform3Base
open import OCF.Align.Uniform3OmegaPlus1 using (module OmegaPlus)
open OmegaPlus using (Ω⁺)
```

## §1 记号侧

```agda
Ω⁺² : PT
Ω⁺² = ψᵗ (sucT (sucT Ωᵗ)) []

t₂ : T
t₂ = ψ₀ᵗ (Ω⁺² ∷ [])

ψ₁ : T → T
ψ₁ ζ = ψᵗ (sucT Ωᵗ) ζ ∷ []

_ : cof (Ω⁺² ∷ []) ≡ cΩ (sucT Ωᵗ)
_ = refl

γ₂ : ℕ → T
γ₂ = γW [] (Ω⁺² ∷ []) (sucT Ωᵗ)

fs-t₂ : ∀ n → fsn t₂ n ≡ ψ₀ᵗ (γ₂ n)
fs-t₂ n = gtW [] [] Ω⁺² [] (sucT Ωᵗ) refl refl n

_ : γ₂ 1 ≡ ψ₁ (Ω⁺¹ ∷ [])
_ = refl
_ : γ₂ 2 ≡ ψ₁ (ψ₁ (Ω⁺¹ ∷ []))
_ = refl

-- ψ₁(Ω⁺) 穿透 (eq): 共尾度 Ω_{Ω+1}, 基本列逐点
_ : cof (ψ₁ (Ω⁺¹ ∷ [])) ≡ cΩ Ωᵗ
_ = refl
_ : ∀ θ → fsT (ψ₁ (Ω⁺¹ ∷ [])) θ ≡ ψ₁ θ
_ = λ θ → refl

_ : walk t₂ (1 ∷ 0 ∷ []) ≡ ψ₀ᵗ (ψ₁ (ΩΩ ∷ []))
_ = refl
_ : walk t₂ (1 ∷ 0 ∷ 0 ∷ 0 ∷ []) ≡ ψ₀ᵗ (ψ₁ (𝟏 ∷ []))
_ = refl
_ : walk t₂ (1 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ []) ≡ ψ₀ᵗ (Ω⁺¹ ∷ Ω⁺¹ ∷ [])
_ = refl
_ : walk t₂ (1 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ []) ≡ ψ₀ᵗ (Ω⁺¹ ∷ ψΩᵗ (Ω⁺¹ ∷ ΩΩ ∷ []))
_ = refl
_ : walk t₂ (1 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ []) ≡ ψ₀ᵗ (Ω⁺¹ ∷ ψΩᵗ (Ω⁺¹ ∷ []))
_ = refl
_ : cof (walk t₂ (1 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ cω
_ = refl

-- (B) 的路径: ψ₀(ψ₁(Ω⁺))[1] = ψ₀(ψ₁(ψ_Ω(ψ₁(Ω_Ω))))
_ : walk t₂ (1 ∷ 1 ∷ []) ≡ ψ₀ᵗ (ψ₁ (ψΩᵗ (ψ₁ (ΩΩ ∷ []))))
_ = refl
_ : walk t₂ (1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ []) ≡ ψ₀ᵗ (ψ₁ (ψΩᵗ (Ω⁺¹ ∷ [])))
_ = refl
_ : cof (walk t₂ (1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ cω
_ = refl
```

实参的共尾度 (树的 `kc` 对应实参共尾度 $\Omega_1$):

```agda
_ : cof (ψ₁ (ψΩᵗ (Ω⁺¹ ∷ []))) ≡ cω
_ = refl
_ : cof (Ω⁺¹ ∷ ψΩᵗ (Ω⁺¹ ∷ [])) ≡ cω
_ = refl
_ : cof (ψ₁ (ΩΩ ∷ [])) ≡ cΩ []
_ = refl
```

## §2 朴素的帧 (现行塔上最小的扩展)

```agda
Bᶰ : ∀ d → A (suc d) (fz ⊔ fk zero)
Bᶰ d = Ω⁺ ∅ᵀ d

Ψ₁ᶰ : ∀ {φ} → Sym φ → Sym ((fz ⊔ fk zero) ⊔ φ)
Ψ₁ᶰ Y d P = Y (suc d) (Bᶰ d) P

one : Ordᴵ
one = suc zero

ev₀ : Ev one (fz ⊔ fk zero)
ev₀ = tt , (λ q → q)

-- ψ₀(ψ₁(ψ₁(0))) = ψ₀(ψ₁(Ω⁺)), 树
Tᶰ : Ordˢ zero
Tᶰ = ψᵀ (Ψ₁ᶰ (Ψ₁ᶰ ∅ᵀ)) {i = zero} {ℓ = one} (tt , ((tt , (λ q → q)) , ((tt , (λ q → q)) , tt))) zero

-- (B): 第 1 个链点缺内层的 ψ₁
_ : kind Tᶰ ≡ kl
_ = refl
_ : kind (walkˢ Tᶰ (1 ∷ [])) ≡ kc one
_ = refl
_ : kind (walkˢ Tᶰ (1 ∷ 0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ Tᶰ (1 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ kc one
_ = refl

one₀ᵗ : Ordˢ zero
one₀ᵗ = Ord₊ˢ.suc Ord₊ˢ.zero

-- (A): ψ₀(ψ₁(1))
Sᶰ : Ordˢ zero
Sᶰ = ψᵀ (Ψ₁ᶰ (tlᵀ (flo zero) (cvFlo zero) one₀ᵗ)) {i = zero} {ℓ = one} (tt , ((tt , (λ q → q)) , tt)) zero

_ : kind Sᶰ ≡ kl
_ = refl
_ : kind (walkˢ Sᶰ (2 ∷ 1 ∷ [])) ≡ kc one
_ = refl
_ : kind (walkˢ Sᶰ (2 ∷ 1 ∷ 0 ∷ 0 ∷ [])) ≡ kl
_ = refl
_ : kind (walkˢ Sᶰ (2 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ kc one
_ = refl

-- (C): 把 Ω⁺ 当算子用, 第 2 份仍在值层重复, 哪怕尾巴是 Ω_Ω 而不是 tlᵀ
S²ᶰ : Ordˢ zero
S²ᶰ = ψᵀ (Ψ₁ᶰ (Ψ ∅ᵀ)) {i = zero} {ℓ = one} (tt , ((tt , (λ q → q)) , ((λ q → q) , tt))) zero

_ : walk (ψ₀ᵗ (ψ₁ (ΩΩ ∷ []))) (0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ []) ≡ ψ₀ᵗ (Ω⁺¹ ∷ ψΩᵗ (Ω⁺¹ ∷ []))
_ = refl
_ : kind (walkˢ S²ᶰ (0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ kc one
_ = refl
```

## §3 为什么不是局部缺口 (纸面)

设 $C(z)=W+\psi_{\Omega+1}(\zeta+z)$ 是 "洞" 的上下文. $\psi_i(C(\Omega_{\Omega+1}))$ 的链是 $\delta_{k+1}=\psi_\Omega(C(\delta_k))$, 所以 (B) 只要求上下文 $C$ 在元层是函数 `Sym → Sym`. 难的是 (A): $\psi_{\Omega+1}(a+1)[m]=\psi_{\Omega+1}(a)\cdot m$, 第 $j$ 份的上下文是 $C_j(z)=C(\psi_{\Omega+1}(a)\cdot(j-1)+\psi_{\Omega+1}(z))$, 依赖**运行时**的树 $a$ (它是 $\Omega_\eta$ 走出来的, 不能在构造项时展开). 这有三种写法, 都不行:

- 值层重复 (现行 `repA`): §2 的编译否定.
- 前缀走 `Sym` (`A⁺ 0 = Sym`, `A⁺ (d+1) = A⁺ d → A⁺ d`): $F\in$ `A⁺ 1` 的第二份输入是符号项, 第一层对了. 但 $F+\psi_\Omega(Z)$ 要 $Z$ 作用在 $F$ 上, 而 `Ψ Z` 的基是 `Ω̂A`, 它的折叠对 $F$ 的值做 `repA`. 要 $Z$ 作用于 `A⁺` 的塔, 也就是 $Z\in$ `Sym⁺ = ∀ d → A⁺ (d+1)`; $Z$ 含 $W$, $W$ 是 `A⁺ 0` 的输入, 所以 `A⁺ 0` 要含 `Sym⁺`: 循环.
- 分层 (`Tᵐ⁺¹` 作用于以 `Tᵐ` 为底的塔): 第 $n$ 个链点要 $W$ 在第 $m+n$ 层, 后继子句的第 $j$ 份要输入比输出高; 输入要对一切 $n$ 成立, 回到循环. 我没有证明别的分层都不行.

三条都来自同一件事: Church 编码下 $\psi_\Omega(\cdot)$ 的值不能被折叠, 只能作用. 解决办法是不要 Church 编码: $\psi_\Omega(t)$ 直接是一棵数据树, 加法在数据层, 见 [Uniform4Base](Uniform4Base.lagda.md).
