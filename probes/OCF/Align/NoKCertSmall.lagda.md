# 判据不空: $\psi_0(\Omega_0)$ 有 `Goodᵁ`

> 不含记号. 结论写在 [NoKCert](NoKCert.lagda.md). `G-x̂₀ : Goodᵁ (rdZ (x̂ᵗ 0))`: 判据 `Goodᵁ` 有非平凡的实例, 值是 $\omega$ (`force-x̂₀`), `fgh` 可以算. **这只说明判据的前提可满足, 不是强度.** 这个闭项没有闭包.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoKCertSmall where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import OCF.Align.LevelNoKU hiding (ŝ)
open import OCF.Align.LevelNoKLv using (module Lv)
open Lv 𝕌 using (Fl; tz; _∪_)
open import OCF.Free.Level using (Ordᶜ; _⊑⁰_; _≅_; ≺s; FGH)
import OCF.Free.Level as FL
import OCF.Align.LevelNoKFold as FF
open FF using (O; T⁰)
open FF.TT using (o0; os; ol; owk; repᵒ; _⊕_)
open import OCF.Align.NoKCertEval
open import OCF.Align.NoKCertTc
```

## §1 自然数形的树

```agda
natZ : ℕ → Zᵁ
natZ zero = zero
natZ (suc n) = suc (natZ n)

natO : ℕ → Ord₀
natO zero = FL.zero
natO (suc n) = FL.suc (natO n)

gn : ∀ n → Goodᵁ (natZ n)
gn zero = gz
gn (suc n) = gs (gn n)

gn-force : ∀ n → forceᵁ (natZ n) (gn n) ≡ natO n
gn-force zero = refl
gn-force (suc n) = cong FL.suc (gn-force n)

data RN : ∀ {π : Fl} → O U.zero π → ℕ → Set where
  r0 : ∀ {π} → RN {π} o0 0
  rs : ∀ {π} {a : O U.zero π} {n} → RN a n → RN (os a) (suc n)
  rw : ∀ {π ρ} (w : Lv.Wk 𝕌 π ρ) {a : O U.zero π} {n} → RN a n → RN (owk w a) n

rd-n : ∀ {π} {y : O U.zero π} {n} → RN y n → rdZ y ≡ natZ n
rd-n r0 = refl
rd-n (rs h) = cong suc (rd-n h)
rd-n (rw {π = π₁} w {a = a} h) = rd-n {π₁} {a} h

rn⊕ : ∀ {φ ψ} {x : O U.zero φ} → RN x 1 → {y : O U.zero ψ} {n : ℕ} → RN y n → RN (x ⊕ y) (suc n)
rn⊕ hx r0 = rw _ hx
rn⊕ hx (rs h) = rs (rn⊕ hx h)
rn⊕ hx (rw w h) = rw _ (rn⊕ hx h)

rn-rep : ∀ {π} {x : O U.zero π} → RN x 1 → ∀ m → RN (repᵒ x m) m
rn-rep hx zero = r0
rn-rep hx (suc m) = rw _ (rn⊕ hx (rn-rep hx m))
```

## §2 证书

```agda
force-subst : ∀ {a b} (eq : a ≡ b) (G : Goodᵁ a) → forceᵁ b (subst Goodᵁ eq G) ≡ forceᵁ a G
force-subst refl G = refl

X₀ : O U.zero tz
X₀ = x̂ᵗ 0

sym′ : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
sym′ refl = refl

trans′ : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans′ refl q = q

step : ∀ {a b} n → a ≡ natO n → b ≡ natO (suc n) → a ⊑⁰ b
step n refl refl h = ≺s h

module Rep {π} (x : O U.zero π) (hx : RN x 1) where
  rep-eq : ∀ n → natZ n ≡ rdZ (repᵒ x n)
  rep-eq n = sym′ (rd-n (rn-rep hx n))

  Gs : ∀ n → Goodᵁ (rdZ (repᵒ x n))
  Gs n = subst Goodᵁ (rep-eq n) (gn n)

  Gs-force : ∀ n → forceᵁ _ (Gs n) ≡ natO n
  Gs-force n = trans′ (force-subst (rep-eq n) (gn n)) (gn-force n)

  Gl : Goodᵁ (lim (λ n → rdZ (repᵒ x n)))
  Gl = gl Gs (λ n → step n (Gs-force n) (Gs-force (suc n)))

G-x̂₀ : Goodᵁ (rdZ X₀)
G-x̂₀ = Rep.Gl _ (rw _ (rs r0))

ω₀ : Ord₀
ω₀ = FL.lim natO

fgh-x̂₀ : ∀ n → fgh (rdZ X₀) G-x̂₀ n ≡ FGH (natO n) n
fgh-x̂₀ n = cong (λ z → FGH z n) (Rep.Gs-force _ (rw _ (rs r0)) n)
```

**有限测试.** $\mathrm{FGH}_\omega(2)$.

```agda
fgh-2 : fgh (rdZ X₀) G-x̂₀ 2 ≡ 8
fgh-2 = refl
```
