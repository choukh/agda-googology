# $\psi_0(\Omega_{\Omega+1})$, 不累加: 根上的义务不能去掉

> 不含记号. **定理 `no-Root`:** 取 $w=\lim_n 2n$ (与 `no-Hn-b` 同一个反例), `Root 0 (w+1)` 是假的. 所以 [Om1HnMain](Om1HnMain.lagda.md) 的 `G-Tᴿ` 的前提对字面任意的层不成立. **这只否定:** 对字面任意的 $a$ 要 `Root`. 不否定 $a=0,1,2$ (`root₀`, `root₁`, `root₂`), 不否定闭包定理 `Psi`, 不否定不累加.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1HnNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; z⊲; _⊲_)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (≈ᴬ-refl; Ord₀; rd; _≈ᴬ_)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumPsi using (ψQ)
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (ψW; ΩW)
open import OCF.Align.NoCumForce hiding (Cl)
open import OCF.Align.NoCumHon using (Fr-ψ; Fr-Ω; Fr→Hn)
open import OCF.Align.NoCumHnNeg using (w₂; g-w; Pψ; J)
open import OCF.Align.Om1HnCx using (idC; Fψ; rψ; idr)
open import OCF.Align.Om1HnMain using (Root)

z₂ : 𝓞 zero w₂ w₂
z₂ = Ω̇at zero w₂ g-w

T₂ : 𝓡 w₂
T₂ = ψ zero azero z₂ g-w w₂ g-w C.self (z⊲ w₂) C.self

E₂ : z₂ ≈ z₂
E₂ = ≈-Ωat zero g-w g-w (≈ᴬ-refl w₂)

d₂ : G T₂
d₂ = C′ T₂ g-w (ψQ z₂ z₂ g-w g-w w₂ g-w C.self (z⊲ w₂) C.self w₂ g-w C.self (z⊲ w₂) C.self (≈ᴬ-refl azero) E₂)
       (ψW zero azero z₂ g-w w₂ g-w C.self (z⊲ w₂) C.self E₂ (ΩW zero w₂ (lgw g-w)))
       (Fr→Hn T₂ (Fr-ψ azero z₂ g-w w₂ g-w C.self (z⊲ w₂) C.self (Fr-Ω w₂)))

no-Root : Root zero (asuc w₂) → ⊥
no-Root root = J (Pψ z₂ g-w w₂ g-w C.self (z⊲ w₂) C.self) d₂
  (proj₁ (root C.zero z₂ g-w C.self (rf E₂) (rψ g-w w₂ g-w C.self (z⊲ w₂) C.self (idr C.self g-w)) (gw d₂)))
```

## 加法把 $W$ 带进链点

`shift`: 第 $(0,0)$ 层的 $W\oplus$ 闭包, 第 0 个链点读的输出以 $W$ 的值的读出为第一位置. 不是否定, 是 [Om1HnAccept](Om1HnAccept.lagda.md) 的障碍里这一边的编译事实. 另一边是源码: `OCF.Free.Prefix.addˢ {k = zero}` 写成 `ĉᴸ c (toZ t₀) …`, 链点读没加的 $t_0$.

```agda
shift : ∀ {u₀ w m} (W : 𝓡 u₀) (gu : Gw u₀) → W ≈ W → (P : azero ⊲ azero) (x : 𝓡 w) (h : ∀ {v} → w ⊲ v → Gw v → 𝓡 v) (gx : Gw w)
        (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : azero ⊲ m) (d : G (add⁰ W gu (sa P) (oc x h) gx m gm um tm am)) (dW : G W) →
        Σ A λ v₀ → Σ Ord₀ λ y₀ → (v₀ ≈ᴬ rd y₀) × Fp (rd (force dW)) y₀
shift W gu E P x h gx gm um tm am (gc G₀ vs gv up Gh t₀ tS s₀ sS) dW =
  vs 0 , force G₀ , t₀ , ⊴→Fp (fo⊴ (AddF.add⊴ W gu (rf E) (sa P) x gx _ gm um tm am) dW G₀)
```
