# 跨高度单调 (四): $\psi_0(\Omega_{\Omega\cdot\omega})$ 的闭项与 FGH

> 结论写在 [LadderMono](LadderMono.lagda.md). 仿 [OCF/Free/Closed](../Free/Closed.lagda.md).
>
> 1. **`Tω₀ : Ordᶜ zero`, `fgh = FGH Tω₀`: 闭项, 无假设.** 树由 `Tω` 计值, 证书 `certᵀ` 由 `GᴺTω` 给出. 按 [LadderMonoAccept](LadderMonoAccept.lagda.md) 的验收读作 $\psi_0(\Omega_{\Omega\cdot\omega})$; 本文件的闭包不知道这个标签.
> 2. **定理 `Tω₀-indep`, `fgh-indep`:** 换一组求值环境, 树只差一个 $\cong$, FGH 逐点相等.
> 3. **有限测试 (不是证明):** §2 的 `refl`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderMonoClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (z≅; toZ-≅; _≅ᶻ_; lᶻ)
open import OCF.Free.Floor using (Ev; ∼ᶠ-refl)
open import OCF.Free.Force using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderNFTree using (Tω; Tωn; Tᵠ; ok₀)
open import OCF.Align.LadderNFRel using (R→≈ᵠ; RΩ̇; rs; rz)
open import OCF.Align.LadderMonoMain using (GᴺTω)
```

## §1 闭项

```agda
ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

certᵀ : Goodᴺ (toZ (Tω ev₀ zero))
certᵀ = GᴺTω ev₀ zero

Tω₀ : Ordᶜ zero
Tω₀ = forceᴺ _ certᵀ

HSᵀ : HS Tω₀
HSᵀ = forceᴺ-HS _ certᵀ

levelᵀ : Ordᴵ
levelᵀ = toLevel Tω₀ HSᵀ

fgh : ℕ → ℕ
fgh = FGH Tω₀

Tωn-indep : ∀ n {ℓ ℓ′} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) (ev′ : Ev ℓ′ Fl) (p′ : zero <ᴵ ℓ′) → toZ (Tωn n ev p) ≅ᶻ toZ (Tωn n ev′ p′)
Tωn-indep zero    ev p ev′ p′ = toZ-≅ (R→≈ᵠ (rs (∼ᶠ-refl Fl) (λ i ()) rz) ok₀ (λ i h r → ok₀ i) ok₀ (λ i h r → ok₀ i) ev p ev′ p′ z≅)
Tωn-indep (suc n) ev p ev′ p′ = toZ-≅ (R→≈ᵠ (RΩ̇ n z≅) ok₀ (λ i h r → ok₀ i) ok₀ (λ i h r → ok₀ i) ev p ev′ p′ z≅)

Tω₀-indep : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Tω₀ ≅ forceᴺ _ (GᴺTω ev z)
Tω₀-indep ev z = forceᴺ-≅ (lᶻ (λ n → Tωn-indep n ev₀ zero ev z)) certᵀ (GᴺTω ev z)

fgh-indep : ∀ {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) n → fgh n ≡ FGH (forceᴺ _ (GᴺTω ev z)) n
fgh-indep ev z = FGH-≅ (Tω₀-indep ev z)
```

## §2 有限测试

下面只在几个具体输入上算值, 不是证明. **注.** `fgh 2` 的 `refl` 检查在 170 秒内没有结果; 这条是没有结果, 不是否定.

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

_ : fgh 0 ≡ 1
_ = refl

_ : fgh 1 ≡ 2
_ = refl

_ : sh Tω₀ ≡ sl
_ = refl

_ : sh (FS Tω₀ 0) ≡ sl
_ = refl

_ : sh (FS Tω₀ 1) ≡ sl
_ = refl

_ : sh (FS Tω₀ 2) ≡ sl
_ = refl
```
