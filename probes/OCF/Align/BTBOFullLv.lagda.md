# Level 对角线的严格性

> 接 [BTBOFullLe](BTBOFullLe.lagda.md). 与 [BTBOFullSt](BTBOFullSt.lagda.md) 同形, 在 Level 的树族上: `Gv` 是严格版的 `Good`, 关系是 `Le` 取 $E=\cong^\mathsf{I}$. 主定理 `SV-L`: `NoCumsum` 的每个层号 $L_m$ 满足 `SV`, 也就是每个 `lim f s` 节点的相邻项之间夹着字面前驱: $f_n\sqsubseteq^\mathsf{I}c\prec^\mathsf{I}f_{n+1}$.
>
> **这是字面序能拿到的形状.** 字面的 $f_n\prec^\mathsf{I}f_{n+1}$ 这里不证, 也用不到: `SV` 已经够让后面的嵌入判定分块.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFullLv where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
import OCF.Align.NoCumsum as N
open import OCF.Align.BTBOFullLe
open import OCF.Align.BTBOValAbsorb using (St; stz; sts; stl)
open import OCF.Align.BTBOValNeg using (HS-≺; two-preds; ≺ᴵ→s≼; ≼-irr; forget-≅ᴵ; HS-≅)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≅→≼; ⊑→≼)
open Restr
```

## §1 $E=\cong^\mathsf{I}$

```agda
≅→⊑ᴵ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅→⊑ᴵ z≅     = z⊑
≅→⊑ᴵ (s≅ e) = s⊑ e zero
≅→⊑ᴵ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅→⊑ᴵ (h n)) (Sim→⊑ᴵ (lim n)))

≅-resp : ∀ {a b a′ b′} → a ≅ᴵ b → a ≅ᴵ a′ → b ≅ᴵ b′ → a′ ≅ᴵ b′
≅-resp e d d′ = ≅ᴵ-trans (≅ᴵ-sym d) (≅ᴵ-trans e d′)

open LeE _≅ᴵ_ ≅-resp ⊤ public

lim-⊑ᴵ : ∀ {g : ℕ → Ordᴵ} {t} n → g n ⊑ᴵ lim g t
lim-⊑ᴵ n = Sim→⊑ᴵ (lim n)

≺⊑ᵛ : ∀ {c b a} → c ≺ᴵ b → b ⊑ᴵ a → c ≺ᴵ a
≺⊑ᵛ (via e q) k = ≺ᴵ-respˡ e (sim k q)

Ω≤ : ∀ {a a′} → a ⊑ᴵ a′ → Le (Ω a) (Ω a′)
Ω≤ {a = zero} {a′ = a′} k = Le-one a′ (≅ᴵ-refl a′)
Ω≤ (s⊑ e q) = walk _ (≅ᴵ-refl _) e q
Ω≤ (l⊑ k) = Lll (λ n → Lul (Ω≤ (k n)))

ℒ≅ : Laws
ℒ≅ = record
  { lt-pres = λ e e′ r → ≺ᴵ-respˡ (≅ᴵ-sym e) (≺ᴵ-respʳ r e′)
  ; eq-pres = λ e e′ r → ≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans r e′)
  ; Ωlaw    = λ e → Ω≤ (≅→⊑ᴵ e)
  ; Ωc      = λ _ k → Ω≤ k
  }

open WithLaws ℒ≅ public

su-l : ∀ {k k₁ i} {r : i ◃₁ k₁} {z : U i (◃₁→◃ r)} {y : Ordᶜ k} → Le (suc (out (◃₁→◃ r) z)) y → Le (suc (up r z)) y
su-l (Ls d)    = Ls (Lul d)
su-l (Lsr d)   = Lsr (su-l d)
su-l (Llr n d) = Llr n (su-l d)
su-l (Lir H)   = Lir (λ z′ c → su-l (H z′ c))
su-l (Lb α k nz H) = Lb α k nz (λ z′ w → su-l (H z′ w))
su-l (Lur {r = zero} d)   = Lur (su-l d)
su-l (Lur {r = self n} d) = Lur (su-l d)
```

## §2 严格的层号与 $\Omega$

```agda
data SV : Ordᴵ → Set where
  svz : SV zero
  svs : ∀ {a} → SV a → SV (suc a)
  svl : ∀ {f : ℕ → Ordᴵ} {s} → (∀ n → SV (f n)) → (∀ n → Σ Ordᴵ (λ c → c ≺ᴵ f (suc n) × f n ⊑ᴵ c)) → SV (lim f s)

SV-≅ : ∀ {a b} → a ≅ᴵ b → SV b → SV a
SV-≅ z≅ svz        = svz
SV-≅ (s≅ e) (svs d) = svs (SV-≅ e d)
SV-≅ (l≅ {f = f} {g = g} h) (svl d st) = svl (λ n → SV-≅ (h n) (d n))
  (λ n → let c , r , k = st n in c , ≺ᴵ-respʳ r (≅ᴵ-sym (h (suc n))) , ⊑ᴵ-trans (≅→⊑ᴵ (h n)) k)

SV-sub : ∀ {c a} → SV a → c <ᴵ a → SV c
SV-sub (svs d) zero      = d
SV-sub (svs d) (suc q)   = SV-sub d q
SV-sub (svl d st) (lim n q) = SV-sub (d n) q

<→⊑ : ∀ {a b} → a <ᴵ b → a ⊑ᴵ b
<→⊑ q = Sim→⊑ᴵ (λ c → <ᴵ-trans c q)

Ω-st : ∀ {c c″ d} → c ⊑ᴵ c″ → c″ <ᴵ d → Le (suc (Ω c)) (Ω d)
Ω-st k zero      = Lb tt k (λ z′ w → Lur w) (λ z′ w → Lur w)
Ω-st k (suc q)   = Lb tt (⊑ᴵ-trans k (<→⊑ q)) (λ z′ w → Lur w) (λ z′ w → Lur w)
Ω-st k (lim n q) = Llr n (Lur (Ω-st k q))

Ω-st≺ : ∀ {c c″ d} → c ⊑ᴵ c″ → c″ ≺ᴵ d → Le (suc (Ω c)) (Ω d)
Ω-st≺ k (via e q) = Ω-st (⊑≅ k e) q
```

## §3 谓词

```agda
module _ (k : Ordᴵ) (G< : (i : Ordᴵ) (r : i ◃ k) → U i r → Set) where
  data Gv₊ : Ordᶜ k → Set where
    gz : Gv₊ zero
    gs : ∀ {a} → Gv₊ a → Gv₊ (suc a)
    gl : ∀ {h : ℕ → Ordᶜ k} → (∀ n → Gv₊ (h n)) → (∀ n → Le (suc (h n)) (h (suc n))) → Gv₊ (lim h)
    gi : ∀ {j} {p : j <ᴵ k} {f : U j (<→◃ p) → Ordᶜ k} → SV j →
         (∀ (z : Ordᶜ j) → G< j (<→◃ p) (into (<→◃ p) z) → Gv₊ (f (into (<→◃ p) z))) →
         (∀ (z z′ : Ordᶜ j) → L< j (<→◃ p) (into (<→◃ p) z′) z → Le (f (into (<→◃ p) z)) (f (into (<→◃ p) z′))) →
         (∀ (z z′ : Ordᶜ j) → L< j (<→◃ p) (into (<→◃ p) z′) (suc z) → Le (suc (f (into (<→◃ p) z))) (f (into (<→◃ p) z′))) →
         Gv₊ (limᵢ p f)
    gu : ∀ {i} {r : i ◃₁ k} {x : U i (◃₁→◃ r)} → G< i (◃₁→◃ r) x → Gv₊ (up r x)

Gd : ∀ {k} (i : Ordᴵ) (r : i ◃ k) → U i r → Set
Gd i zero         x = Gv₊ i Gd x
Gd i (suc r)      x = Gd i r x
Gd _ (self {f} n) x = Gv₊ (f n) Gd x
Gd i (lim n r)    x = Gd i r x

Gv : ∀ {k} → Ordᶜ k → Set
Gv {k} = Gv₊ k Gd

Gd→G : ∀ {i k} (r : i ◃ k) {x : Ordᶜ i} → Gd i r (into r x) → Gv x
Gd→G zero      g = g
Gd→G (suc r)   g = Gd→G r g
Gd→G (self n)  g = g
Gd→G (lim n r) g = Gd→G r g

G→Gd : ∀ {i k} (r : i ◃ k) {x : Ordᶜ i} → Gv x → Gd i r (into r x)
G→Gd zero      g = g
G→Gd (suc r)   g = G→Gd r g
G→Gd (self n)  g = g
G→Gd (lim n r) g = G→Gd r g

Le-refl : ∀ {k} {x : Ordᶜ k} → Gv x → Le x x
Le-refl gz        = Lz
Le-refl (gs g)    = Ls (Le-refl g)
Le-refl (gl h s)  = Lll (λ n → Llr n (Le-refl (h n)))
Le-refl (gi sv h m st) = Lii (≅ᴵ-refl _) m
Le-refl (gu {r = zero} g)   = Lul (Lur (Le-refl g))
Le-refl (gu {r = self n} g) = Lul (Lur (Le-refl g))
```

**沿搬运封闭.** 与 `Uniform` 的 `Good-tr` 一一对应. `back` 对 `suc` 交换 (`back-suc`), 严格分支要它.

```agda
back-suc : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) (u : Ordᶜ (rep (res q e))) → back (res q e) (suc u) ≡ suc (back (res q e) u)
back-suc zero      (s≅ e) u = refl
back-suc (suc q)   (s≅ e) u = back-suc q e u
back-suc (lim n q) (l≅ f) u = back-suc q (f n) u

back⁻-suc : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) (u : Ordᶜ (rep (res⁻ q e))) → back (res⁻ q e) (suc u) ≡ suc (back (res⁻ q e) u)
back⁻-suc zero      (s≅ e) u = refl
back⁻-suc (suc q)   (s≅ e) u = back⁻-suc q e u
back⁻-suc (lim n q) (l≅ f) u = back⁻-suc q (f n) u

G-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → Gv x → Gv (tr e x)
G-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → Gv x → Gv (tr⁻ e x)
G-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → Gv u → Gv (back (res q e) u)
G-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → Gv u → Gv (back (res⁻ q e) u)

G-tr e gz       = gz
G-tr e (gs g)   = gs (G-tr e g)
G-tr e (gl h s) = gl (λ n → G-tr e (h n)) (λ n → Lr-tr e (Ll-tr e (s n)))
G-tr e (gi {p = q} {f = f} sv h m st) = gi (SV-≅ (≅ᴵ-sym (eq (res q e))) sv)
  (λ z g → subst (λ u → Gv (tr e (f (into (<→◃ q) (back (res q e) u))))) (sym (out-into (<→◃ (lt (res q e))) z))
                 (G-tr e (h (back (res q e) z) (G→Gd (<→◃ q) (G-back q e (Gd→G (<→◃ (lt (res q e))) g))))))
  (λ z z′ w → subst₂ (λ u v → Le (tr e (f (into (<→◃ q) (back (res q e) u)))) (tr e (f (into (<→◃ q) (back (res q e) v)))))
                 (sym (out-into (<→◃ (lt (res q e))) z)) (sym (out-into (<→◃ (lt (res q e))) z′))
                 (Lr-tr e (Ll-tr e (m _ _ (Le→L (<→◃ q) (Lr-back q e (Ll-back q e (L→Le (<→◃ (lt (res q e))) w))))))))
  (λ z z′ w → subst₂ (λ u v → Le (suc (tr e (f (into (<→◃ q) (back (res q e) u))))) (tr e (f (into (<→◃ q) (back (res q e) v)))))
                 (sym (out-into (<→◃ (lt (res q e))) z)) (sym (out-into (<→◃ (lt (res q e))) z′))
                 (Lr-tr e (Ll-tr e (st _ _ (Le→L (<→◃ q) (Lr-back q e
                    (subst (λ t → Le t _) (back-suc q e z) (Ll-back q e (L→Le (<→◃ (lt (res q e))) w)))))))))
G-tr (s≅ e) (gu {r = zero} g)   = gu (G-tr e g)
G-tr (l≅ f) (gu {r = self n} g) = gu (G-tr (f n) g)

G-tr⁻ e gz       = gz
G-tr⁻ e (gs g)   = gs (G-tr⁻ e g)
G-tr⁻ e (gl h s) = gl (λ n → G-tr⁻ e (h n)) (λ n → Lr-tr⁻ e (Ll-tr⁻ e (s n)))
G-tr⁻ e (gi {p = q} {f = f} sv h m st) = gi (SV-≅ (≅ᴵ-sym (eq (res⁻ q e))) sv)
  (λ z g → subst (λ u → Gv (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) u))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
                 (G-tr⁻ e (h (back (res⁻ q e) z) (G→Gd (<→◃ q) (G-back⁻ q e (Gd→G (<→◃ (lt (res⁻ q e))) g))))))
  (λ z z′ w → subst₂ (λ u v → Le (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) u)))) (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) v)))))
                 (sym (out-into (<→◃ (lt (res⁻ q e))) z)) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
                 (Lr-tr⁻ e (Ll-tr⁻ e (m _ _ (Le→L (<→◃ q) (Lr-back⁻ q e (Ll-back⁻ q e (L→Le (<→◃ (lt (res⁻ q e))) w))))))))
  (λ z z′ w → subst₂ (λ u v → Le (suc (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) u))))) (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) v)))))
                 (sym (out-into (<→◃ (lt (res⁻ q e))) z)) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
                 (Lr-tr⁻ e (Ll-tr⁻ e (st _ _ (Le→L (<→◃ q) (Lr-back⁻ q e
                    (subst (λ t → Le t _) (back⁻-suc q e z) (Ll-back⁻ q e (L→Le (<→◃ (lt (res⁻ q e))) w)))))))))
G-tr⁻ (s≅ e) (gu {r = zero} g)   = gu (G-tr⁻ e g)
G-tr⁻ (l≅ f) (gu {r = self n} g) = gu (G-tr⁻ (f n) g)

G-back zero      (s≅ e) g = G-tr⁻ e g
G-back (suc q)   (s≅ e) g = G-back q e g
G-back (lim n q) (l≅ f) g = G-back q (f n) g

G-back⁻ zero      (s≅ e) g = G-tr e g
G-back⁻ (suc q)   (s≅ e) g = G-back⁻ q e g
G-back⁻ (lim n q) (l≅ f) g = G-back⁻ q (f n) g
```

## §4 对 $\Omega$, 加法, 折叠封闭

```agda
G-Ω : ∀ {a} → SV a → Gv (Ω a)
G-Ω svz = gs gz
G-Ω (svs {a} d) = gi d (λ z g → gu g) (λ z z′ w → Lul (Lur w)) (λ z z′ w → su-l (Lur w))
G-Ω (svl d st) = gl (λ n → gu (G-Ω (d n))) (λ n → let c , r , k = st n in su-l (Lur (Ω-st≺ k r)))

G-add : ∀ {k₁ ℓ} {a : Ordᶜ ℓ} {σ : Simᴵ k₁ ℓ} {b : Ordᶜ k₁} → Gv a → Gv b → Gv (add a σ b)
G-add ga gz       = ga
G-add ga (gs g)   = gs (G-add ga g)
G-add ga (gl h s) = gl (λ n → G-add ga (h n)) (λ n → L-add (Le-refl ga) (s n))
G-add {a = a} {σ = σ} ga (gi {p = q} {f = f} sv h m st) = gi sv
  (λ z g → subst (λ u → Gv (add a σ (f (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z))
                 (G-add ga (h z (G→Gd (<→◃ q) (Gd→G (<→◃ (σ q)) g)))))
  (λ z z′ w → subst₂ (λ u v → Le (add a σ (f (into (<→◃ q) u))) (add a σ (f (into (<→◃ q) v))))
                 (sym (out-into (<→◃ (σ q)) z)) (sym (out-into (<→◃ (σ q)) z′))
                 (L-add (Le-refl ga) (m z z′ (Le→L (<→◃ q) (L→Le (<→◃ (σ q)) w)))))
  (λ z z′ w → subst₂ (λ u v → Le (suc (add a σ (f (into (<→◃ q) u)))) (add a σ (f (into (<→◃ q) v))))
                 (sym (out-into (<→◃ (σ q)) z)) (sym (out-into (<→◃ (σ q)) z′))
                 (L-add (Le-refl ga) (st z z′ (Le→L (<→◃ q) (L→Le (<→◃ (σ q)) w)))))
G-add {σ = σ} ga (gu {r = zero} {x = x} g)   = G-add {σ = λ q → σ (suc q)} {b = x} ga g
G-add {σ = σ} ga (gu {r = self n} {x = x} g) = G-add {σ = λ q → σ (lim n q)} {b = x} ga g

G-iter : ∀ {k} {A : Ordᶜ k} → Gv A → ∀ n → Gv (iter (A +_) zero n)
G-iter gA zero    = gz
G-iter gA (suc n) = G-add gA (G-iter gA n)

rule4 : ∀ {k} {A : Ordᶜ k} → Gv A → Le (suc (zero {ℓ = k})) A → ∀ n → Le (suc (iter (A +_) zero n)) (iter (A +_) zero (suc n))
rule4 gA o zero    = o
rule4 gA o (suc n) = L-add (Le-refl gA) (rule4 gA o n)

s→one : ∀ {k k₁} {x : Ordᶜ k₁} {y : Ordᶜ k} → Le (suc x) y → Le (suc (zero {ℓ = Ordᴵ.zero})) y
s→one (Ls d)    = Ls Lz
s→one (Lsr d)   = Lsr (s→one d)
s→one (Llr n d) = Llr n (s→one d)
s→one (Lir H)   = Lir (λ z c → s→one (H z c))
s→one (Lb α k nz H) = Lb α k nz (λ z w → s→one (H z w))
s→one (Lur {r = zero} d)   = Lur (s→one d)
s→one (Lur {r = self n} d) = Lur (s→one d)

G-ψ : ∀ {i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) {x : Ordᶜ k} → SV i → Gv x → Gv (ψ p σ x)

chain-good : ∀ {j k} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} → SV j →
             (∀ (z : Ordᶜ j) → Gd j (<→◃ q) (into (<→◃ q) z) → Gv (f (into (<→◃ q) z))) →
             ∀ n → Gv (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n)
chain-good sv h zero = G-Ω sv
chain-good {q = q} {f = f} sv h (suc n) = G-ψ q (λ r → r) sv (h _ (G→Gd (<→◃ q) (chain-good {q = q} {f = f} sv h n)))

chain-step : ∀ {j k} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} →
             (∀ (z z′ : Ordᶜ j) → L< j (<→◃ q) (into (<→◃ q) z′) (suc z) → Le (suc (f (into (<→◃ q) z))) (f (into (<→◃ q) z′))) →
             ∀ n → Le (suc (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) n)) (iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j) (suc n))
chain-step {j = j} {q = q} {f = f} st zero =
  Sbt (Le-Ω (≅ᴵ-refl j)) q (λ r → r) {w = f (into (<→◃ q) (Ω j))} (s→one (st zero (Ω j) (Le→L (<→◃ q) (Le-one j (≅ᴵ-refl j)))))
chain-step {j = j} {q = q} {f = f} st (suc n) = S-ψ (≅ᴵ-refl j) q (λ r → r) q (λ r → r) (st _ _ (Le→L (<→◃ q) (chain-step {q = q} {f = f} st n)))
```

```agda
G-ψ p σ sv gz = G-Ω sv
G-ψ p σ sv (gs {a} g) = gl (G-iter (G-ψ p σ sv g)) (rule4 (G-ψ p σ sv g) (one-ψ p σ a))
G-ψ p σ sv (gl h s)   = gl (λ n → G-ψ p σ sv (h n)) (λ n → S-ψ (≅ᴵ-refl _) p σ p σ (s n))
G-ψ p σ sv (gi {p = q} {f = f} svj h m st) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = gi (SV-≅ (≅ᴵ-sym e) svj)
       (λ z g → subst (λ u → Gv (ψ p σ (f (into (<→◃ q) (tr⁻ e u))))) (sym (out-into (<→◃ r) z))
                      (G-ψ p σ sv (h (tr⁻ e z) (G→Gd (<→◃ q) (G-tr⁻ e (Gd→G (<→◃ r) g))))))
       (λ z z′ w → subst₂ (λ u v → Le (ψ p σ (f (into (<→◃ q) (tr⁻ e u)))) (ψ p σ (f (into (<→◃ q) (tr⁻ e v)))))
                      (sym (out-into (<→◃ r) z)) (sym (out-into (<→◃ r) z′))
                      (Le-ψ (≅ᴵ-refl _) p σ p σ (m _ _ (Le→L (<→◃ q) (Lr-tr⁻ e (Ll-tr⁻ e (L→Le (<→◃ r) w)))))))
       (λ z z′ w → subst₂ (λ u v → Le (suc (ψ p σ (f (into (<→◃ q) (tr⁻ e u))))) (ψ p σ (f (into (<→◃ q) (tr⁻ e v)))))
                      (sym (out-into (<→◃ r) z)) (sym (out-into (<→◃ r) z′))
                      (S-ψ (≅ᴵ-refl _) p σ p σ (st _ _ (Le→L (<→◃ q) (Lr-tr⁻ e (Ll-tr⁻ e (L→Le (<→◃ r) w)))))))
... | injᵇ _ = gl (λ n → G-ψ p σ sv (h _ (G→Gd (<→◃ q) (chain-good {q = q} {f = f} svj h n))))
                  (λ n → S-ψ (≅ᴵ-refl _) p σ p σ (st _ _ (Le→L (<→◃ q) (chain-step {q = q} {f = f} st n))))
... | injᶜ _ = gl (λ n → G-ψ p σ sv (h _ (G→Gd (<→◃ q) (chain-good {q = q} {f = f} svj h n))))
                  (λ n → S-ψ (≅ᴵ-refl _) p σ p σ (st _ _ (Le→L (<→◃ q) (chain-step {q = q} {f = f} st n))))
G-ψ p σ sv (gu {r = zero} g)   = G-ψ p (λ q → σ (suc q)) sv g
G-ψ p σ sv (gu {r = self n} g) = G-ψ p (λ q → σ (lim n q)) sv g
```

## §5 第 0 层: 值严格, 回到层号

```agda
Le→≼ : ∀ {x y : Ordᶜ Ordᴵ.zero} → Le x y → x ≼ y
Le→≼ Lz        = z≼
Le→≼ (Ls d)    = s≼s (Le→≼ d)
Le→≼ (Lsr d)   = ≼-suc (Le→≼ d)
Le→≼ (Lll h)   = l≼ (λ n → Le→≼ (h n))
Le→≼ (Llr n d) = ≼l n (Le→≼ d)
Le→≼ (Lii {p = ()} e h)
Le→≼ (Lir {p′ = ()} H)
Le→≼ (Lb {p′ = ()} α k nz H)
Le→≼ (Lul {r = ()} d)
Le→≼ (Lur {r = ()} d)

Gv→St : ∀ {x : Ordᶜ Ordᴵ.zero} → Gv x → St x
Gv→St gz       = stz
Gv→St (gs g)   = sts (Gv→St g)
Gv→St (gl h s) = stl (λ n → Gv→St (h n)) (λ n → Le→≼ (s n))
Gv→St (gi {p = ()} sv h m st)
Gv→St (gu {r = ()} g)

St-≅ : ∀ {a b : Ordᶜ Ordᴵ.zero} → a ≅ b → St b → St a
St-≅ z≅ stz       = stz
St-≅ (s≅ e) (sts d) = sts (St-≅ e d)
St-≅ (l≅ h) (stl d s) = stl (λ n → St-≅ (h n) (d n))
  (λ n → ≼-trans (s≼s (≅→≼ (h n))) (≼-trans (s n) (≅→≼ (≅-sym (h (suc n))))))
St-≅ (lᵢ≅ {p = ()} e h) d
St-≅ (upˡ {r = ()} e) d
St-≅ (upʳ {r = ()} e) d

⊑→≼f : ∀ {a b} → a ⊑ᴵ b → forget a ≼ forget b
⊑→≼f z⊑        = z≼
⊑→≼f (s⊑ e q)  = ≺ᴵ→s≼ (via e q)
⊑→≼f (l⊑ k)    = l≼ (λ n → ⊑→≼f (k n))

s≼pred : ∀ {a b : Ordᶜ Ordᴵ.zero} → suc a ≼ b → Σ (Ordᶜ Ordᴵ.zero) (λ c → c ≺ b × a ≼ c)
s≼pred {b = suc b₀} (s≼s d) = b₀ , ≺z (≅-refl⁰ b₀) , d
s≼pred (≼l n p) with s≼pred p
... | c , r , d = c , ≺l n r , d

⊑≺ : ∀ {a B c} → a ⊑ᴵ B → c ≺ᴵ B → forget a ≼ forget c → a ⊑ᴵ c
⊑≺ z⊑ r d = z⊑
⊑≺ {a = suc a₀} {c = c} (s⊑ e q) r d with two-preds (via e q) r
... | injᵃ x = s⊑′ x
... | injᵇ x = ⊥-elim (≼-irr (forget c) (≼-trans (≺ᴵ→s≼ x) (≼-trans (≼-suc (≼-refl (forget a₀))) d)))
... | injᶜ x = ⊥-elim (≼-irr (forget c) (≼-trans (s≼s (≅→≼ (forget-≅ᴵ (≅ᴵ-sym x)))) d))
⊑≺ (l⊑ k) r d = l⊑ (λ n → ⊑≺ (k n) r (≼-trans (≼l n (≼-refl _)) d))

SV-toLevel : ∀ (y : Ordᶜ Ordᴵ.zero) (h : HS y) → St y → SV (toLevel y h)
SV-toLevel zero h st = svz
SV-toLevel (suc a) h (sts st) = svs (SV-toLevel a (hs⁻ h) st)
SV-toLevel (lim f) h (stl d s) = svl (λ n → SV-toLevel (f n) (hl₁ h n) (d n)) step
  where
  step : ∀ n → Σ Ordᴵ (λ c → c ≺ᴵ toLevel (f (suc n)) (hl₁ h (suc n)) × toLevel (f n) (hl₁ h n) ⊑ᴵ c)
  step n with s≼pred (s n)
  ... | c , r , v = toLevel c hc , toLevel-≺ hc hb r ,
        ⊑≺ (toLevel-⊑ (hl₁ h n) hb (hl₂ h n)) (toLevel-≺ hc hb r)
           (≼-trans (≅→≼ (forget-toLevel (f n) (hl₁ h n))) (≼-trans v (≅→≼ (≅-sym (forget-toLevel c hc)))))
    where hb = hl₁ h (suc n)
          hc = HS-≺ r hb
SV-toLevel (limᵢ () f) h st
SV-toLevel (up () x) h st

data Pos : Ordᴵ → Set where
  ps : ∀ {a} → Pos (suc a)
  pl : ∀ {f s} → Pos (lim f s)

pos≺ : ∀ {c a} → c ≺ᴵ a → Pos a
pos≺ (via e zero)      = ps
pos≺ (via e (suc q))   = ps
pos≺ (via e (lim n q)) = pl

z<SV : ∀ {a} → SV a → Pos a → Ordᴵ.zero <ᴵ a
z<SV (svs {a = zero} d) ps    = zero
z<SV (svs {a = suc b} d) ps   = suc (z<SV d ps)
z<SV (svs {a = lim f s} d) ps = suc (z<SV d pl)
z<SV (svl d st) pl = lim 1 (z<SV (d 1) (pos≺ (proj₁ (proj₂ (st 0)))))

posF : ∀ a h → Pos (toLevel (ψ⁰ (Ω a)) h)
posF zero      h = pl
posF (suc a)   h = pl
posF (lim f s) h = pl

St-F : ∀ {a} → SV a → Pos a → St (ψ⁰ (Ω a))
St-F {a} sv ps₀ = St-≅ (ψ⁰≅ψ {p = z<SV sv ps₀} {σ = λ q → q} (Ω-refl a)) (Gv→St (G-ψ (z<SV sv ps₀) (λ q → q) svz (G-Ω sv)))

pos-L : ∀ m → Pos (N.L m)
pos-L zero    = ps
pos-L (suc m) = posF (N.L m) (N.cert (suc m))

SV-L : ∀ m → SV (N.L m)
St-γ : ∀ m → St (N.γ m)

St-γ zero    = sts stz
St-γ (suc m) = St-F (SV-L m) (pos-L m)

SV-L m = SV-toLevel (N.γ m) (N.cert m) (St-γ m)
```
