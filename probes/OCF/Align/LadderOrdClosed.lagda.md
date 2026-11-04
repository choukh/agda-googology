# 序数高度: 闭项, FGH, 有限测试

> **判决: HOLDS (闭项无假设; 有限测试明说; 读法是判断).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 仿 [LadderInfClosed](LadderInfClosed.lagda.md).
>
> 1. **第一个跨过 `HS₂` 的高度** 是码 `ω·ᶜ 1` 的顶 `end`, 值 $\omega\cdot2$. `Tω·2 = forceᴺ _ (Gω·2 zero)`. 读作 $\psi_0(\Omega_{\Omega\cdot\omega\cdot2})=\psi_0(\Omega_{\psi_1(1)\cdot 2})$ (判断, 没有标签).
> 2. **检查点:** `Tω²` ($\psi_0(\Omega_{\Omega\cdot\omega^2})$), `Tω^ω`, `Tε₀`. 读法同样是判断.
> 3. **`T-feed`:** 输出回灌作高度: $\eta_0=\omega$, $\eta_{n+1}=\lceil$ `Tᵒ` $\eta_n$ 的计值 $\rceil$, $\eta_*=$ `cl η`. 无条件. 读作不动点 $\eta=\psi_0(\Omega_{\Omega\cdot\eta})$ 一带 (判断; `⌈_⌉` 只保证不低).
> 4. **有限测试 (不是证明):** §2 的 `refl`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Force using (forceᴺ; forceᴺ-HS)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode
open import OCF.Align.LadderOrdCert

-- M 的第 α 行
Tᶜ : Code → Ordᴵ → Ordᶜ zero
Tᶜ M α = forceᴺ _ (Gᵒ M α)

HSᶜ : ∀ M α → HS (Tᶜ M α)
HSᶜ M α = forceᴺ-HS _ (Gᵒ M α)

fghᶜ : Code → Ordᴵ → ℕ → ℕ
fghᶜ M α = FGH (Tᶜ M α)

Tω·2 Tω² Tω^ω Tε₀ : Ordᶜ zero
Tω·2 = Tᶜ (ω·ᶜ 1) zero
Tω²  = Tᶜ ω²ᶜ zero
Tω^ω = Tᶜ ω^ωᶜ zero
Tε₀  = Tᶜ ε₀ᶜ zero

fghω·2 fghω² fghω^ω fghε₀ : ℕ → ℕ
fghω·2 = FGH Tω·2
fghω²  = FGH Tω²
fghω^ω = FGH Tω^ω
fghε₀  = FGH Tε₀

-- 输出回灌作高度
ηₙ : ℕ → Code
ηₙ zero = ωᶜ
ηₙ (suc n) = ⌈ lvG (Gᵒ (ηₙ n) zero) ⌉

η* : Code
η* = cl ηₙ

T-feed : Ordᶜ zero
T-feed = Tᶜ η* zero

fgh-feed : ℕ → ℕ
fgh-feed = FGH T-feed
```

## §2 有限测试

只在几个具体输入上算值, 不是证明.

```agda
data Sh : Set where
  sz ss sl : Sh

sh : Ordᶜ zero → Sh
sh zero    = sz
sh (suc _) = ss
sh (lim _) = sl
sh _       = sz

_ : fghω·2 0 ≡ 1
_ = refl

_ : fghω² 0 ≡ 1
_ = refl

_ : fghε₀ 0 ≡ 1
_ = refl

_ : fghω·2 1 ≡ 2
_ = refl

_ : fghω² 1 ≡ 2
_ = refl

_ : fghε₀ 1 ≡ 2
_ = refl

_ : sh Tω·2 ≡ sl
_ = refl

_ : sh Tω² ≡ sl
_ = refl

_ : sh Tω^ω ≡ sl
_ = refl

_ : sh Tε₀ ≡ sl
_ = refl

_ : sh T-feed ≡ sl
_ = refl
```
