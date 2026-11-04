> **机械克隆, 验收用.** 由 `LadderInfAgree` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 实例与原来的树

> **判决: HOLDS (编译过, 无条件).** 结论写在 [LadderInf](LadderInf.lagda.md). 这里只有定理, 没有假设.
>
> 1. **`agree-ℕ`:** 实例 ℕ 的证书与 [LadderNFMain](LadderNFMain.lagda.md) 的证书计值 $\cong$, 对一切 $m$, $\alpha$; FGH 逐点相等 (`fgh-ℕ`).
> 2. **`agree-fin`:** 实例 ℕ∪{∞} 的有限部分也一样.
> 3. **`anchor`:** $T_\omega$ (`LadderNFTree`) 与实例 ℕ∪{∞} 的 $\dot\Omega_\infty\,0$ 的值 $\cong$. 所以 `ql F` 这一行确实是已经验收过的 $\psi_0(\Omega_{\psi_1(1)})$: `forceᴺ-∞0`, `fgh-∞0`. 用的是 `D-self`: $\iota_{\downarrow\infty}(\dot\Omega_n\,0)$ 在 $\infty$ 上的值就是 $\dot\Omega_n\,0$ 在 $n$ 上的值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfWAgree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (toZ)
open import OCF.Align.LadderNFWEq using (_≈ᴿ_; _≅ˢ_; ≅ˢ-trans; toZ-≅; z≅; l≅; sucR; wkR; lᶻ)
open import OCF.Align.LadderNFWFloor using (Ev; fz)
open import OCF.Align.LadderNFWForce using (Goodᴺ; forceᴺ; forceᴺ-≅)
open import OCF.Align.LadderNFWBase using (r∅)
open import OCF.Align.LadderNFWFT using (Fl)
import OCF.Align.LadderNFWTree as N
import OCF.Align.LadderNFWMain as NM
import OCF.Align.LadderMonoWMain as MM
open import OCF.Align.LadderInfWNat using (HSℕ)
open import OCF.Align.LadderInfWTop using (HS∞; fin; ∞; inf)
import OCF.Align.LadderInfWTree
import OCF.Align.LadderInfWMain
import OCF.Align.LadderInfWDn
import OCF.Align.LadderInfWDnSelf
import OCF.Align.LadderInfWBridge as Bℕ
import OCF.Align.LadderInfWBridgeTop as B∞
module Tℕ = OCF.Align.LadderInfWTree HSℕ
module T∞ = OCF.Align.LadderInfWTree HS∞
module Iℕ = OCF.Align.LadderInfWMain HSℕ
module I∞ = OCF.Align.LadderInfWMain HS∞
module D∞ = OCF.Align.LadderInfWDn HS∞
module S∞ = OCF.Align.LadderInfWDnSelf HS∞
```

## §1 实例 ℕ 给回原来的树

```agda
agree-ℕ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (NM.GᴺTᵠ m α ev z) ≅ forceᴺ _ (Iℕ.GᴺTᵠ m α ev z)
agree-ℕ m α ev z = forceᴺ-≅ (toZ-≅ (Bℕ.bridge m α α (≅ᴵ-refl α) ev z ev z z≅)) _ _

fgh-ℕ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → FGH (forceᴺ _ (NM.GᴺTᵠ m α ev z)) n ≡ FGH (forceᴺ _ (Iℕ.GᴺTᵠ m α ev z)) n
fgh-ℕ m α ev z = FGH-≅ (agree-ℕ m α ev z)

agree-fin : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (NM.GᴺTᵠ m α ev z) ≅ forceᴺ _ (I∞.GᴺTᵠ (fin m) α ev z)
agree-fin m α ev z = forceᴺ-≅ (toZ-≅ (B∞.bridge m α α (≅ᴵ-refl α) ev z ev z z≅)) _ _
```

## §2 $\dot\Omega_\infty\,0$ 就是 $T_\omega$

```agda
e-step : ∀ i → T∞.Eh (fin 0) ∞ T∞.w₀ (T∞.cap (T∞.κ Fl) (fin i) fz)
e-step i j h r = T∞.κ-cap (fin i) (λ _ → tt) j (T∞.ok₀ j)

step : ∀ i → N.Tᵠ i zero ≈ᴿ T∞.ψ̄ᵠ T∞.ok₀ (e-step i) (T∞.ι↓ {α = zero} (inf i) (T∞.Ω̇ (fin i) zero))
step i ev p ev′ p′ ei =
  ≅ˢ-trans (B∞.bridge i zero zero z≅ ev p ev′ p′ ei)
           (D∞.D→≈ᵠ (S∞.D-self (inf i)) T∞.ok₀ (λ j h r → T∞.ok₀ j) T∞.ok₀ (e-step i) ev′ p′ ev′ p′ (≅ᴵ-refl _))

go : ∀ i → N.Tωn i ≈ᴿ T∞.ψ̄ᵠ T∞.ok₀ (λ j h r → T∞.ok₀ j) (T∞.rowL fin inf (λ j → T∞.Ω̇ (fin j)) i)
go zero ev p ev′ p′ ei = sucR (wkR (λ _ → tt) (λ _ → tt) r∅) ev p tt p′ ei
go (suc i) = step i

anchor : N.Tω ≈ᴿ T∞.Tᵠ ∞ zero
anchor ev p ev′ p′ ei = l≅ (λ i → go i ev p ev′ p′ ei)

forceᴺ-∞0 : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → forceᴺ _ (MM.GᴺTω ev z) ≅ forceᴺ _ (I∞.GᴺTᵠ ∞ zero ev z)
forceᴺ-∞0 ev z = forceᴺ-≅ (toZ-≅ (anchor ev z ev z z≅)) _ _

fgh-∞0 : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → FGH (forceᴺ _ (MM.GᴺTω ev z)) n ≡ FGH (forceᴺ _ (I∞.GᴺTᵠ ∞ zero ev z)) n
fgh-∞0 ev z = FGH-≅ (forceᴺ-∞0 ev z)
```
