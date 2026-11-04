# 验收: 不累加的 $\psi_0(\Omega_\Omega)$

> **验收文件.** 读 `NoCumsum`, `Label`. 判决: **基本列验收, HOLDS.** `T⁰≅ : fr T⁰ ≅ BTBOᴵ`, 所以 `label-T⁰ : Lab (fr T⁰) (E.EBOψ 2)` (`Lab-≅`). 基本列与带标签的树逐项 $\cong$, 这比序数值验收强, FGH 逐点相同 (`fgh⁰`).
>
> 对照累加的 `Tᶜ`: 只有序数值验收, 第 1 项就严格更大 (`CumUpAcceptVal.term₁-strict`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumAcceptOmega where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.Level
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Align.Value using (_≈ᵛ_; ≅→≼)
open import Data.Product using (_,_)
open import OCF.Align.BTBOValNeg using (HS-≅)
open import OCF.Align.BTBOFullLv using (SV-L; pos-L; z<SV)
import OCF.Align.EBO as E
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Label using (BTBO-label)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.CumUpAcceptSim using (Ix; iz; is; il; Ix-r; fr; Y-sim)
open import OCF.Align.NoCumLit using (rd; _≈ᴬ_; z≈; s≈; l≈; Ord₀)
open import OCF.Align.NoCumOmega using (T⁰; ys⁰; cell; η; wη; tie)

Ix-rd : ∀ (y : Ord₀) (h : HS (fr y)) → Ix (rd y) (toLevel (fr y) h)
Ix-rd FL.zero h = iz
Ix-rd (FL.suc a) h = is (Ix-rd a (hs⁻ h))
Ix-rd (FL.lim f) h = il (λ n → Ix-rd (f n) (hl₁ h n))
Ix-rd (FL.limᵢ () f) h
Ix-rd (FL.up () x) h

Ix-≈ : ∀ {a b ℓ} → a ≈ᴬ b → Ix b ℓ → Ix a ℓ
Ix-≈ z≈ iz = iz
Ix-≈ (s≈ e) (is d) = is (Ix-≈ e d)
Ix-≈ (l≈ h) (il d) = il (λ n → Ix-≈ (h n) (d n))

term : ∀ n → fr (ys⁰ n) ≅ N.γ (suc n)
Ix-L : ∀ n → Ix (η (cell n)) (N.L (suc n))

Ix-L n =
  let e = term n
      h = HS-≅ e (N.cert (suc n))
  in Ix-r (Ix-≈ (tie (cell n)) (Ix-rd (ys⁰ n) h)) (toLevel-≅ h (N.cert (suc n)) e)

term zero = Y-sim _ (is iz) zero
term (suc n) = Y-sim (wη (cell n)) (Ix-L n) (z<SV (SV-L (suc n)) (pos-L (suc n)))

T⁰≅ : fr T⁰ ≅ BTBOᴵ
T⁰≅ = l≅ term

label-T⁰ : Lab (fr T⁰) (E.EBOψ 2)
label-T⁰ = Lab-≅ T⁰≅ BTBO-label

T⁰≈ : fr T⁰ ≈ᵛ BTBOᴵ
T⁰≈ = ≅→≼ T⁰≅ , ≅→≼ (≅-sym T⁰≅)

fgh⁰ : ∀ n → FGH (fr T⁰) n ≡ FGH BTBOᴵ n
fgh⁰ = FGH-≅ T⁰≅
```
