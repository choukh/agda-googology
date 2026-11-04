# 带紧读法的闭项

> 不含记号. 结论写在 [NoKCert](NoKCert.lagda.md). 与 [LevelNoKFold](LevelNoKFold.lagda.md) 换成 [NoKCertTree](NoKCertTree.lagda.md) 的 `Tn` (`owk` 一行), `Tc-id` 换成 `Tc-of`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCertTc where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Align.LevelFixCore using (LF)
open import OCF.Align.LevelFixVal
open import OCF.Align.LevelNoKU
open import OCF.Align.LevelNoKFold using (O; rb; T⁰)
open import OCF.Align.NoKCertTree XF using (Tn)
open import OCF.Align.NoKCertRd

-- ψ_n(Ω_x), 带紧读法
Tψᵗ : (x : LF) → Legal x → Cnt x → (n : ℕ) → T⁰ n
Tψᵗ x w v n = Tn (toU x) (Cf-toU x w) (Tc-of x w v) n

x̂ᵗ : ∀ n → T⁰ 0
x̂ᵗ n = Tψᵗ (tw n) (Legal-tw n) (cnt-tw n) 0

ψ₀Λᵗ : T⁰ 0
ψ₀Λᵗ = Tψᵗ Λ Legal-Λ cnt-Λ 0
```
