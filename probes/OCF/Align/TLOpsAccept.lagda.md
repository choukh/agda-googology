# 树的算子语言: 验收

> **验收文件.** 只有这里读 `NoCumsum`, `Label`, `EBO` (标签). 入口 [TLOps](TLOps.lagda.md).
>
> | 站 | 新树 | 定理 | 档 |
> |---|---|---|---|
> | $\psi_0(\Omega_1)$ | `T₀ one` | `T₀≅ψ⁰`: 与 Level 的 $\psi^0(\Omega_1)$ $\cong$ | 结构, 所以值也是 |
> | $\psi_0(\Omega_\omega)$ | `T₀ ωA` | `Tω≅ψ⁰` | 同上 |
> | $\psi_0(\Omega_\eta)$, 一切字面合法的 $\eta$ | `T₀ η` | `T₀≅ψ⁰` | 同上 |
> | $\psi_0(\Omega_\Omega)$, 回灌对角线 | `Top.T azero tt` | `TΩ≅ : fr T ≅ BTBOᴵ`, `label-TΩ`, `TΩ≈`, `fghΩ` | **基本列验收, 序数值验收** |
>
> 高于这一站的新树与旧树之间没有定理, 只有 [TLOpsTest](TLOpsTest.lagda.md) 的有限测试. 见 [TLOps](TLOps.lagda.md).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.Level
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Align.Value using (_≈ᵛ_; ≅→≼)
open import OCF.Align.BTBOValNeg using (HS-≅)
open import OCF.Align.BTBOFullLv using (SV-L; pos-L; z<SV)
import OCF.Align.EBO as E
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Label using (BTBO-label)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadAccept using (natA; lgn)
open import OCF.Align.CumUpAcceptSim using (Ix; iz; is; il; Ix-r; fr; Y-sim)
open import OCF.Align.CumReadCFThm using (Y)
open import OCF.Align.NoCumLit using (rd; _≈ᴬ_; z≈; s≈; l≈; Ord₀)
open import OCF.Align.TLOpsW using (one; g₀; Gw; gw; lgw; pos)
open import OCF.Align.TLOpsPre using (Tᵖ)
open import OCF.Align.TLOpsSim using (T₀≅Y)
open import OCF.Align.TLOpsClo using (module Top; module Clo)
```

## §1 高度 0

```agda
fr≅ : ∀ {x y : Ord₀} → x FL.≅ y → fr x ≅ fr y
fr≅ FL.z≅ = z≅
fr≅ (FL.s≅ e) = s≅ (fr≅ e)
fr≅ (FL.l≅ h) = l≅ (λ n → fr≅ (h n))
fr≅ (FL.lᵢ≅ {p = ()} e h)
fr≅ (FL.upˡ {r = ()} e)
fr≅ (FL.upʳ {r = ()} e)

T₀ : ∀ η → Gw η → Ord₀
T₀ η g = Tᵖ azero η η tt g C.self

T₀≅ψ⁰ : ∀ {η ℓ} (g : Gw η) → Ix η ℓ → (p : zero <ᴵ ℓ) → fr (T₀ η g) ≅ ψ⁰ (Ω ℓ)
T₀≅ψ⁰ {η} g ix p = ≅-trans (fr≅ (T₀≅Y η g)) (Y-sim (lgw g) ix p)

T₁≅ : fr (T₀ one g₀) ≅ ψ⁰ (Ω (suc zero))
T₁≅ = T₀≅ψ⁰ g₀ (is iz) zero

ωA : A
ωA = alim natA

gω : Gw ωA
gω = gw ((λ n → C.suc C.self) , lgn) (C.lim 1 C.self)

Ix-n : ∀ n → Ix (natA n) (natᴵ n)
Ix-n zero = iz
Ix-n (suc n) = is (Ix-n n)

Tω≅ψ⁰ : fr (T₀ ωA gω) ≅ ψ⁰ (Ω ωᴵ)
Tω≅ψ⁰ = T₀≅ψ⁰ gω (il Ix-n) (lim 1 zero)
```

## §2 $\psi_0(\Omega_\Omega)$

```agda
private module TΩ = Top azero tt
private module K = Clo TΩ.F

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

term : ∀ n → fr (K.ys n) ≅ N.γ (suc n)
Ix-L : ∀ n → Ix (K.η (K.cell n)) (N.L (suc n))

Ix-L n =
  let e = term n
      h = HS-≅ e (N.cert (suc n))
  in Ix-r (Ix-≈ (K.tied n) (Ix-rd (K.ys n) h)) (toLevel-≅ h (N.cert (suc n)) e)

term zero = T₀≅ψ⁰ g₀ (is iz) zero
term (suc n) = T₀≅ψ⁰ (K.gη (K.cell n)) (Ix-L n) (z<SV (SV-L (suc n)) (pos-L (suc n)))

TΩ≅ : fr K.T ≅ BTBOᴵ
TΩ≅ = l≅ term

label-TΩ : Lab (fr K.T) (E.EBOψ 2)
label-TΩ = Lab-≅ TΩ≅ BTBO-label

TΩ≈ : fr K.T ≈ᵛ BTBOᴵ
TΩ≈ = ≅→≼ TΩ≅ , ≅→≼ (≅-sym TΩ≅)

fghΩ : ∀ n → FGH (fr K.T) n ≡ FGH BTBOᴵ n
fghΩ = FGH-≅ TΩ≅
```
