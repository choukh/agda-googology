# 验收: 过 (p, a) 世界的 $\psi_0(\Omega_\Omega)$

> **验收文件.** 主档是序数值验收: `TΩᴺ≈ : fr TΩᴺ ≈ᵛ BTBOᴵ`. `BTBOᴵ` 是过基本列验收的树. 这里更强: `TΩᴺ≅ : fr TΩᴺ ≅ BTBOᴵ`, 所以 `TΩᴺ≅T⁰`. 证明对 `Tᴰ` 的**任何证书** (`any-cert`), 不依赖 `Hn-Ω` 的具体证明. `Lab` 只作探路: `label-TΩᴺ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumHnAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
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
open import OCF.Align.CumReadCF using (azero; A; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumUpAcceptSim using (Ix; Ix-r; fr; Y-sim)
open import OCF.Align.NoCumLit using (Ord₀; rd; _≈ᴬ_)
open import OCF.Align.NoCumW using (one; g₀; lgw; Tᴰ; Ω̇)
open import OCF.Align.NoCumForce using (G; gw; gc; force; outs; G-T)
open import OCF.Align.NoCumHon using (TΩᴺ; Hn-Ω)
open import OCF.Align.NoCumOmega using (T⁰)
open import OCF.Align.NoCumAcceptOmega using (Ix-rd; Ix-≈; T⁰≅; term)
open import OCF.Align.NoCumHnBridge using (force-Y; Q-Ω; qw)

fr≅ : ∀ {a b : Ord₀} → a FL.≅ b → fr a ≅ fr b
fr≅ FL.z≅ = z≅
fr≅ (FL.s≅ e) = s≅ (fr≅ e)
fr≅ (FL.l≅ h) = l≅ (λ n → fr≅ (h n))
fr≅ (FL.lᵢ≅ {p = ()} e h)
fr≅ (FL.upˡ {r = ()} e)
fr≅ (FL.upʳ {r = ()} e)

ixOf : ∀ {v k} (y : Ord₀) → v ≈ᴬ rd y → fr y ≅ N.γ (suc k) → Ix v (N.L (suc k))
ixOf {k = k} y t e =
  let h = HS-≅ e (N.cert (suc k))
  in Ix-r (Ix-≈ t (Ix-rd y h)) (toLevel-≅ h (N.cert (suc k)) e)

any-cert : (d : G (Tᴰ 1 azero one g₀ (z⊲ one))) → fr (force d) ≅ BTBOᴵ
any-cert (gw (gc G₀ vs gv up₁ Gh t₀ tS s₀ sS)) = l≅ outt
  where
  E₀ : fr (force G₀) ≅ N.γ 1
  E₀ = ≅-trans (fr≅ (force-Y C.self (Ω̇ 0 one) g₀ g₀ _ _ _ _ (Q-Ω one) G₀)) (term 0)
  IX : ∀ n → Ix (vs n) (N.L (suc n))
  EE : ∀ n → fr (force (Gh n)) ≅ N.γ (suc (suc n))
  IX zero = ixOf _ t₀ E₀
  IX (suc n) = ixOf _ (tS n) (EE n)
  EE n = ≅-trans (fr≅ (force-Y C.self _ (gv n) (gv n) _ _ _ (lgw (gv n)) (qw (Q-Ω (vs n))) (Gh n)))
                 (Y-sim (lgw (gv n)) (IX n) (z<SV (SV-L (suc n)) (pos-L (suc n))))
  outt : ∀ n → fr (outs (force G₀) (λ k → force (Gh k)) n) ≅ N.γ (suc n)
  outt zero = E₀
  outt (suc n) = EE n

TΩᴺ≅ : fr TΩᴺ ≅ BTBOᴵ
TΩᴺ≅ = any-cert (G-T 1 azero one g₀ (z⊲ one) Hn-Ω)

TΩᴺ≈ : fr TΩᴺ ≈ᵛ BTBOᴵ
TΩᴺ≈ = ≅→≼ TΩᴺ≅ , ≅→≼ (≅-sym TΩᴺ≅)

TΩᴺ≅T⁰ : fr TΩᴺ ≅ fr T⁰
TΩᴺ≅T⁰ = ≅-trans TΩᴺ≅ (≅-sym T⁰≅)

label-TΩᴺ : Lab (fr TΩᴺ) (E.EBOψ 2)
label-TΩᴺ = Lab-≅ TΩᴺ≅ BTBO-label
```
