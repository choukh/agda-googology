# $\psi_0(\Omega_{\Omega+1})$, 不累加: 闭项

> 不含记号. 结论写在 [Om1Hn](Om1Hn.lagda.md). `G-Tᴿ`: 对一切 $p,a$, 只要 `Root p a`, `Tᴰ p a` 有证书. `Root p a` 说 $\psi_{0,0}$ 看得见 $a$ 之下的层. **$a=0,1,2$ 时它是定理, 对一切 $p$** (`root₀`, `root₁`, `root₂`), 所以 `T₁ = Tᴺ 1 1`, 即不累加无前缀的 $\psi_0(\Omega_{\Omega+1})$, 是无条件的闭项. 对字面任意的 $a$, `Root` 是假的 ([Om1HnNeg](Om1HnNeg.lagda.md) 的 `no-Root`, 与 `no-Hn-b` 同一个反例), 这就是 "下标要带证据" 的准确形状: 义务只在根上, 不在闭包定理里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1HnMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (HS)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (Ord₀; ≈ᴬ-refl)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumMain using (ΩW)
open import OCF.Align.NoCumForce hiding (Cl; C′)
open import OCF.Align.NoCumHon using (fp₁)
open import OCF.Align.Om1HnCx
open import OCF.Align.Om1HnGd
open import OCF.Align.Om1HnOmega using (ΩG)
open import OCF.Align.Om1HnPsi using (Psi)
```

## §1 根

```agda
𝓘 : Cl
𝓘 C = C ≡ idC

seen₀ : Seen (Fψ idC zero azero) one
seen₀ z (rψ gx v gv uv tv av (idr p g)) (gw d) = fp₁ z gx v gv uv tv av d

sees₀ : Sees idC zero azero
sees₀ z gz cu ω (idr p g) (gw d) = Fp-z _ , ⊴→Fp (fo⊴ ω (gw (gs g0)) d)

Root : ℕ → A → Set
Root p a = ∀ {c} → c ≪ a → Sees (Fψ idC zero azero) p c

root₀ : ∀ {p} → Root p azero
root₀ ()

root₁ : ∀ {p} → Root p one
root₁ C.zero z gz cu ω r d = Fp-z _ , seen₀ z r d
root₁ (C.suc ())

root₂ : ∀ {p} → Root p (asuc one)
root₂ C.zero z gz cu ω r d = seen₀ z r d , seen₀ z r d
root₂ (C.suc r′) = root₁ r′
```

## §2 证书

```agda
G-Tᴿ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Root p a → G (Tᴰ p a u₀ g e)
G-Tᴿ p a u₀ g e root =
  X (Tᴰ p a u₀ g e) g (≈-T p a u₀ g e) (WF-T p a u₀ g e) 𝓘 refl
    (Psi zero azero (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e (𝓥 p a) 𝓘
      (λ { refl → vv (λ i → seen₀ , tt) root })
      (λ { refl → vt (vv (λ ()) (λ ())) sees₀ })
      (Ω≈ p (≈ᴬ-refl a)) (ΩW p a (lg⊲ e (lgw g))) (ΩG p a))

Tᴿ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Root p a → Ord₀
Tᴿ p a u₀ g e root = force (G-Tᴿ p a u₀ g e root)

HS-Tᴿ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) (root : Root p a) → HS (Tᴿ p a u₀ g e root)
HS-Tᴿ p a u₀ g e root = HS-force (G-Tᴿ p a u₀ g e root)
```

## §3 闭项

`G₁`: $\psi_0(\Omega_{\Omega+1})$ 的数据树的证书, 无条件.

```agda
G₁ : G (Tᴰ 1 one one g₀ C.self)
G₁ = G-Tᴿ 1 one one g₀ C.self root₁

T₁ : Ord₀
T₁ = force G₁

HS-T₁ : HS T₁
HS-T₁ = HS-force G₁

-- ψ₀(Ω_{Ω·p+1}) 这一族 (读法是判断, 强度没有验)
G-p₁ : ∀ p → G (Tᴰ p one one g₀ C.self)
G-p₁ p = G-Tᴿ p one one g₀ C.self root₁

G-p₀ : ∀ p → G (Tᴰ p azero one g₀ (z⊲ one))
G-p₀ p = G-Tᴿ p azero one g₀ (z⊲ one) root₀
```
