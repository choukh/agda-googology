# 新树的证书: 验收 (与 EBO 比较)

> **验收节.** 记号只在本文件. 结论写在 [LvCert](LvCert.lagda.md).
>
> 这里的 `refl` 是有限测试. `c-low`, `c-fs` 比较的是否定结果里的那两个点: 记号说第 0 点确实低于 $\tau$, 所以 [LvCertNeg](LvCertNeg.lagda.md) 的界是树的定义的问题, 不是记号的问题.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvCertAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Prefix using (toZ)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ)
open import OCF.Align.Correspond using (Lab)
import OCF.Align.EBO as E
open E using (T; PT; fsn; natT; sucT; cmpᵀ; lt; eq; gt; Ωt) renaming (ψ to ψᵗ)
open import OCF.Align.Uniform3Base using (ψ₀ᵗ)
open import OCF.Align.Uniform4Head using (Ωp)
open import OCF.Align.Uniform5Wall using (Ω·2; ΩΩ·2; t₁)
open import OCF.Align.UniformLvBase
open import OCF.Align.UniformLvTree using (T₀)
open import OCF.Align.LvCertNeg using (c₀; cfD; noCert₂)
```

## §1 否定的两个点

$W=\Omega_{\Omega\cdot2}$. $\tau=\psi_0(W+\Omega_{\Omega+1})$ 是外层闭包的第 0 个链点; `tHd` $=\psi_0(W+\psi_\Omega(\Omega_{\Omega+1}))$ 是目标 $\Omega$ 下那份 $W$ 的闭包的第 0 个链点. 记号说后者低于前者. 而树的界要它高于前者.

```agda
Ω+1 : T
Ω+1 = sucT (Ωp ∷ [])

W⁺ : T → T
W⁺ a = ψ₀ᵗ (ΩΩ·2 ∷ a)

τ₀ tHd : T
τ₀  = W⁺ (ψᵗ Ω+1 [] ∷ [])
tHd = W⁺ (ψᵗ (Ωp ∷ []) (ψᵗ Ω+1 [] ∷ []) ∷ [])

c-low : cmpᵀ tHd τ₀ ≡ lt
c-low = refl

-- 记号里目标 Ω 之下的 Ω_{Ω·2}: 第 0 个元不看 τ
tIn : T
tIn = W⁺ (ψᵗ (Ωp ∷ []) (ΩΩ·2 ∷ []) ∷ [])

c-fs : cmpᵀ (fsn tIn 0) τ₀ ≡ lt
c-fs = refl
```

## §2 没有 `Lab`

`Lab` 要 `forceᴺ`, `forceᴺ` 要证书. 所以 $\psi_0(\Omega_{\Omega\cdot2+1})$ 在这棵树上没有标签可说; 这也是切片的正对照.

```agda
noLab : (G : Goodᴺ (toZ (T₀ c₀ cfD))) → Lab (forceᴺ _ G) t₁ → ⊥
noLab G _ = noCert₂ cfD G
```
