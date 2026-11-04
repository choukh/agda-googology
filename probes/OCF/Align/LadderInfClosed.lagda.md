# 高度抽象: 闭项与有限测试

> **判决: HOLDS (闭项无假设; 有限测试明说).** 结论写在 [LadderInf](LadderInf.lagda.md). 仿 [LadderMonoClosed](LadderMonoClosed.lagda.md).
>
> 1. **闭项, 无假设.** `T₀∞` ($\psi_0(\Omega_{\psi_1(1)})$), `T₁∞` ($\psi_0(\Omega_{\psi_1(1)+1})$), `T₂Ω` ($\psi_0(\Omega_{\psi_1(1)+\Omega})$), 及它们的 `FGH`. 读法: `T₀∞` 由 `anchor` 支持, 后两个只是判断.
> 2. **有限测试 (不是证明):** §2 的 `refl`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Force using (forceᴺ; forceᴺ-HS)
open import OCF.Align.LadderInfTop using (∞)
open import OCF.Align.LadderInfTop2 using (top)
open import OCF.Align.LadderInfCert using (G∞; G₂)

T₀∞ : Ordᶜ zero
T₀∞ = forceᴺ _ (G∞ zero)

T₁∞ : Ordᶜ zero
T₁∞ = forceᴺ _ (G∞ (suc zero))

T₂Ω : Ordᶜ zero
T₂Ω = forceᴺ _ (G₂ 1 zero)

HS₀∞ : HS T₀∞
HS₀∞ = forceᴺ-HS _ (G∞ zero)

HS₁∞ : HS T₁∞
HS₁∞ = forceᴺ-HS _ (G∞ (suc zero))

HS₂Ω : HS T₂Ω
HS₂Ω = forceᴺ-HS _ (G₂ 1 zero)

fgh₀∞ fgh₁∞ fgh₂Ω : ℕ → ℕ
fgh₀∞ = FGH T₀∞
fgh₁∞ = FGH T₁∞
fgh₂Ω = FGH T₂Ω
```

## §2 有限测试

只在几个具体输入上算值, 不是证明.

```agda
FS : Ordᶜ zero → ℕ → Ordᶜ zero
FS (lim f) n = f n
FS (suc x) n = x
FS x       n = x

data Sh : Set where
  sz ss sl : Sh

sh : Ordᶜ zero → Sh
sh zero    = sz
sh (suc _) = ss
sh (lim _) = sl
sh _       = sz

_ : fgh₀∞ 0 ≡ 1
_ = refl

_ : sh T₀∞ ≡ sl
_ = refl

_ : sh T₁∞ ≡ sl
_ = refl

_ : sh T₂Ω ≡ sl
_ = refl
```
