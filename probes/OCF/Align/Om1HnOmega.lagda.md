# $\psi_0(\Omega_{\Omega+1})$, 不累加: $\Omega$ 是好的

> 不含记号. 结论写在 [Om1Hn](Om1Hn.lagda.md). `ΩG p a : Gd (𝓥 p a) (Ω̇ p a)`, 对一切 $p,a$. 上下文的条件 `𝓥 p a`: 看得见 $a$ 之下的层.
>
> 闭包这一行的 `ch₀`, `chS` 就是 [NoCumHnCore](NoCumHnCore.lagda.md) 的 `Bach` 的一步: 链点 $v$ 之下的 $c$, 要么在上一个链点之下 (归纳), 要么 $v_j\triangleleft c$, 这时项压过 $\Omega_{v_j}$, 所以压过第 $j$ 支, 而 $c\ll v_{j+1}=\mathrm{rd}\,y_{j+1}$. 用的只有 `cmpN`, `≪→Fp`, `mn`, `dn`, 不看折叠的规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1HnOmega where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; ≪⊲; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_⊴₀_; _≈ᴬ_; rd)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumForce hiding (Cl; C′)
open import OCF.Align.NoCumHnCore using (≪→Fp)
open import OCF.Align.Om1HnCx
open import OCF.Align.Om1HnGd
```

## §1 闭包的一步

```agda
record Bb (p : ℕ) (v : A) (C : Cx) : Set₁ where
  constructor bb
  field bse : ∀ {c} → c ≪ v → Sees C p c
open Bb

record ⊤₁ : Set₁ where
  constructor tt₁

-- 项压过 Ω_c, c 在 first 的读出之内, 而 first 压在 Ω_c 之下, 则 c 在项的计值里
bach₁ : ∀ {p v} (C : Cx) {pf af uf wf} {f : 𝓞 pf af uf} {yf : 𝓡 wf} (rf₁ : Rn C f yf) (df : G yf) → Hb C p →
        v ≈ᴬ rd (force df) → ∀ {c} → c ≪ v → (∀ {u} (g : Gw u) → f ⊴ Ω̇at p c g) →
        ∀ {p₂ a₂ u} (z : 𝓞 p₂ a₂ u) (gz : Gw u) {w} {y : 𝓡 w} → c ⊲ u → Ω̇at p c gz ⊴ z → Rn C z y → (d : G y) → Fp c (force d)
bach₁ {p} C {f = f} rf₁ df hb t r fle z gz cu ω rz d with dn C (het hb cu) gz ω C.self rz d
... | w₃ , y₃ , r₃ , d₃ , s₃ = Fp-mono (≪→Fp r t) (⊴₀-tr (fo⊴ (mn C (fle gz) rf₁ r₃) df d₃) s₃)
```

## §2 `ΩG`

```agda
St𝓥 : ∀ {p c C C′} → 𝓥 p (asuc c) C → Over p p c C′ C → 𝓥 p (asuc c) C′
St𝓥 {p} {c} {C} {C′} (vv fo se) o = vv fo′ se′
  where
  fo′ : Fo p C′
  fo′ i = (λ z r d → proj₁ (fo i) (Ov.z (ovr o z r)) (Ov.rz (ovr o z r)) d) , ovb o i
  se′ : ∀ {c′} → c′ ≪ asuc c → Sees C′ p c′
  se′ C.zero z gz cu ω r d = let O = ovr o z r in se C.zero (Ov.z O) (Ov.gz O) (Ov.kz O) (Ov.ωz O) (Ov.rz O) d
  se′ (C.suc r′) z gz cu ω r d with ovr o z r
  ... | ov z₂ gz₂ kz rz ωz with dn C hom gz₂ ωz C.self rz d
  ...   | w₃ , y₃ , r₃ , d₃ , s₃ =
    let f = se (C.suc r′) (Ω̇at p c gz₂) gz₂ (⊲-tr (≪⊲ r′) kz) (lw₂ (rw (Ω⊴ p (≪⊲ r′)))) r₃ d₃
    in Fp-mono (proj₁ f) s₃ , Fp-mono (proj₂ f) s₃

ΩG : ∀ p a → Gd (𝓥 p a) (Ω̇ p a)
ΩG p (asuc c) = brr (𝓥 p (asuc c)) (λ C → C) (λ c₁ → c₁) (λ c₁ r → tr _ r)
  (λ (vv fo se) → vt (vv fo (λ r → se (C.suc r))) (se C.zero))
  St𝓥
  (λ 𝓔 sub q g y e w gz → Gd-mono (λ c₁ → im _ c₁ refl) y gz)
ΩG p (alim f) = λ n → Gd-mono (λ (vv fo se) → vv fo (λ r → se (C.lim n r))) (Ω̇ p (f n)) (ΩG p (f n))
ΩG zero azero = osr (λ _ → ⊤₁) (λ _ → tt₁) tt₂ (λ _ _ → tt₁) (λ _ r d o → o , Fp-z _)
ΩG (suc p) azero =
  ocr (λ v C → Bb p v C)
    (Gd-mono (λ (vv fo se) → vv (λ i → fo (suc i)) (λ { C.zero z gz cu ω r d → Fp-z _ , proj₁ (fo zero) z r d })) (Ω̇ p one) (ΩG p one))
    (λ {v} q g → Gd-mono (λ { (vv fo se , bb b) → vv (λ i → fo (suc i)) b }) (Ω̇ p v) (ΩG p v))
    (λ (vv fo se) r d → proj₁ (fo zero) _ r d , Fp-z _)
    (λ {C} (vv fo se) r d {v} gv t q → bb (λ r′ z gz cu ω r₂ d₂ →
       (case₀ C fo r d gv t q r′ z gz cu ω r₂ d₂) , proj₁ (fo zero) z r₂ d₂))
    (λ {C} {v} {v′} q g (vv fo se) (bb b) r d gv t q′ → bb (λ r′ z gz cu ω r₂ d₂ →
       (caseS C fo q g b r d gv t q′ r′ z gz cu ω r₂ d₂) , proj₁ (fo zero) z r₂ d₂))
  where
  case₀ : ∀ (C : Cx) (fo : Fo (suc p) C) {w} {y : 𝓡 w} → Rn C (oL {p = suc p} {a = azero} zero one C.self (Ω̇ p one)) y → (d : G y) → ∀ {v} → Gw v → v ≈ᴬ rd (force d) → one ⊲ v →
          ∀ {c} → c ≪ v → ∀ {p₂ a₂ u} (z : 𝓞 p₂ a₂ u) (gz : Gw u) {w₂} {y₂ : 𝓡 w₂} → c ⊲ u → Ω̇at p c gz ⊴ z → Rn C z y₂ → (d₂ : G y₂) → Fp c (force d₂)
  case₀ C fo r d gv t q r′ z gz cu ω r₂ d₂ with cmpN r′ q (lgw gv)
  ... | keep C.zero = Fp-z _
  ... | rise s₁ = bach₁ C r d (proj₂ (fo zero)) t r′ (λ g → lL {j = zero} (rw (Ω⊴ p s₁))) z gz cu ω r₂ d₂
  caseS : ∀ (C : Cx) (fo : Fo (suc p) C) {v v′} (q : one ⊲ v) (g : Gw v) → (∀ {c} → c ≪ v → Sees C p c) → ∀ {w} {y : 𝓡 w} →
          Rn C (oL {p = suc p} {a = azero} zero v C.self (ow (pos g) g₀ (Ω̇ p v))) y → (d : G y) → Gw v′ → v′ ≈ᴬ rd (force d) → v ⊲ v′ →
          ∀ {c} → c ≪ v′ → ∀ {p₂ a₂ u} (z : 𝓞 p₂ a₂ u) (gz : Gw u) {w₂} {y₂ : 𝓡 w₂} → c ⊲ u → Ω̇at p c gz ⊴ z → Rn C z y₂ → (d₂ : G y₂) → Fp c (force d₂)
  caseS C fo q g b r d gv t q′ r′ z gz cu ω r₂ d₂ with cmpN r′ q′ (lgw gv)
  ... | keep s₁ = proj₁ (b s₁ z gz cu ω r₂ d₂)
  ... | rise s₁ = bach₁ C r d (proj₂ (fo zero)) t r′ (λ g₁ → lL {j = zero} (lw₂ (rw (Ω⊴ p s₁)))) z gz cu ω r₂ d₂
```
