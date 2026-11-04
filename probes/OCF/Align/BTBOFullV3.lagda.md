# 累加层号落进折叠的基本列

> 接 [BTBOFullEb](BTBOFullEb.lagda.md). `V3`: 对 `SV` 的层号 $a$, `ordᴰ (bkᴵ a)` 的前驱保序映到树 $\psi^0(\Omega_a)$ 的字面前驱. **这就是吸收的字面形式**: 累加 $\Sigma_{n-1}+d$ 落到 $A+e(d)$, 其中 $A=\psi^0(\Omega_c)$, $f_n\sqsubseteq^\mathsf{I}c\prec^\mathsf{I}f_{n+1}$. 关键是 `key`: $\Omega_c+1\sqsubseteq^\mathsf{o}\psi_c(\Omega_d)$, 所以 $A\cdot\omega\sqsubseteq\psi^0(\Omega_{c+1})$ (`Fmul`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFullV3 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; injᵃ; injᵇ; injᶜ)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum; cumsum-mono)
open S using (iter; ordᴰ)
open import OCF.Align.Level hiding (below)
open import OCF.Align.Uniform using (_⊑ᵒ_; lim-r; limᵢ-r; add-cong; Ω0; ⊑ᵒ-≅ʳ; idO; ψ⁰o)
open import OCF.Align.BTBOFullQ using (<ᴰ-irrefl; clash-lt)
open import OCF.Align.BTBOFullLv using (SV; svz; svs; svl; ⊑≺)
open import OCF.Align.BTBOFullLe using (σ₀)
open import OCF.Align.BTBOValNeg using (add-≺)
open import OCF.Align.BTBOFullEb using (Tgt; module Blocks)
```

## §1 `key`

```agda
key : ∀ {c ℓ} (q : c <ᴵ ℓ) d (σ : Simᴵ d ℓ) → suc (Ω c) ⊑ᵒ ψ q σ (Ω d)
key {c} q zero σ = lim-r 2 (add-cong {σ = σ₀} {σ′ = λ r → r} (Ω-refl c) (Ω0 c))
key q (suc e) σ with <ᴵ-dec (σ zero) q
... | injᵃ (via e₁ r) = limᵢ-r (λ z dz →
        subst (λ u → _ ⊑ᵒ ψ q (λ r′ → σ (suc r′)) (tr⁻ e₁ u)) (sym (out-into (<→◃ r) z))
              (⊑ᵒ-≅ʳ (key q e (λ r′ → σ (suc r′)))
                     (ψ-≅ (≅ᴵ-refl _) (≅-sym (tr⁻-≅ e₁ (≅-trans dz (Ω-≅ (≅ᴵ-sym e₁))))))))
... | injᵇ _ = lim-r 0 (key q e (λ r′ → σ (suc r′)))
... | injᶜ _ = lim-r 0 (key q e (λ r′ → σ (suc r′)))
key q (lim g t) σ = lim-r 0 (key q (g 0) (λ r′ → σ (lim 0 r′)))

Fʸ : Ordᴵ → Ordᶜ zero
Fʸ a = ψ⁰ (Ω a)

Fmul : ∀ c → ψ⁰ (suc (Ω c)) ⊑ Fʸ (suc c)
Fmul c = ⊑-lim 1 (key zero c (λ r → suc r) (ψ⁰o idO))

z≺Fʸ : ∀ a → 𝟎 {zero} ≺ Fʸ a
z≺Fʸ a = z≺ψ⁰ (Ω a)

A≺A+A : ∀ a → Fʸ a ≺ (Fʸ a + Fʸ a)
A≺A+A a = add-≺ (Fʸ a) (z≺Fʸ a)

Fstep : ∀ a → Fʸ a ≺ Fʸ (suc a)
Fstep a = Fmul a (≺l 2 (A≺A+A a))

T3 : Ordᴵ → Ordᶜ zero
T3 a = Fʸ a + (Fʸ a + Fʸ a)

T3≺ : ∀ a → (Fʸ a + Fʸ a) ≺ T3 a
T3≺ a = add-≺ (Fʸ a) (A≺A+A a)

T3⊑ : ∀ a → T3 a ⊑ Fʸ (suc a)
T3⊑ a {c = x} h = Fmul a (≺l 3 h)

add-left : ∀ {x A : Ordᶜ zero} → x ≺ A → ∀ R → x ≺ (A + R)
add-left h zero        = h
add-left h (suc R)     = ≺s (add-left h R)
add-left h (lim f)     = ≺l 0 (add-left h (f 0))
add-left h (limᵢ () f)
add-left h (up () x)
```

## §2 目标: 第 0 层的树

```agda
≺→⊑₀ : ∀ {a b : Ordᶜ zero} → a ≺ b → a ⊑ b
≺→⊑₀ (≺z e)   h = ≺s (≺-respʳ h e)
≺→⊑₀ (≺s r)   h = ≺s (≺→⊑₀ r h)
≺→⊑₀ (≺l n r) h = ≺l n (≺→⊑₀ r h)
≺→⊑₀ (≺i {p = ()} x ex r) h
≺→⊑₀ (≺u {r = ()} r) h

𝕋₀ : Tgt
𝕋₀ = record
  { C = Ordᶜ zero ; _≺_ = _≺_ ; _≈_ = _≅_
  ; ≈r = ≅-refl⁰ ; ≈s = ≅-sym ; ≈t = ≅-trans
  ; ≺t = λ p q → ≺→⊑₀ q p
  ; ≺l = ≺-respˡ ; ≺r = ≺-respʳ }

open Blocks 𝕋₀

bkᴵ : Ordᴵ → S.Ord₀
bkᴵ zero      = S.zero
bkᴵ (suc a)   = S.suc (bkᴵ a)
bkᴵ (lim f s) = S.lim (λ n → bkᴵ (f n))

O∘ : (ℕ → Ordᴵ) → ℕ → Ordᴰ
O∘ f n = ordᴰ (bkᴵ (f n))
```

## §3 `V3`

```agda
V3 : ∀ {a} → SV a → Eb (ordᴰ (bkᴵ a)) (Fʸ a)
V3 svz = Eb-zero
V3 {suc a₀} (svs d) = Eb-suc (V3 d) (Fʸ a₀) (λ p → p) (Fstep a₀)
V3 {lim f s} (svl d st) = Blk.Lim (O∘ f) Bd (Fʸ (lim f s)) (V3 (d 0)) N Nb Nm Nc fl sp
  where
  c : ℕ → Ordᴵ
  c n = proj₁ (st n)
  rc : ∀ n → c n ≺ᴵ f (suc n)
  rc n = proj₁ (proj₂ (st n))
  kc : ∀ n → f n ⊑ᴵ c n
  kc n = proj₂ (proj₂ (st n))
  Bd : ℕ → Ordᶜ zero
  Bd zero    = Fʸ (f 0)
  Bd (suc n) = T3 (c (suc n))
  Fʸ⊑c : ∀ n → Fʸ (f n) ⊑ Fʸ (c n)
  Fʸ⊑c n = Ψ⁰-mono (kc n)
  Fs⊑ : ∀ n → Fʸ (suc (c n)) ⊑ Fʸ (f (suc n))
  Fs⊑ n = Ψ⁰-mono (s⊑′ (rc n))
  Bd⊑ : ∀ n → Bd n ⊑ Fʸ (f (suc n))
  Bd⊑ zero    h = Fs⊑ 0 (Ψ⁰-suc (c 0) (Fʸ⊑c 0 h))
  Bd⊑ (suc n) h = Fs⊑ (suc n) (T3⊑ (c (suc n)) h)
  eN : ∀ n → Eb (O∘ f (suc n)) (Fʸ (f (suc n)))
  eN n = V3 (d (suc n))
  N : ∀ n {x} → x B.< B.suc (O∘ f (suc n)) → Ordᶜ zero
  N n B.zero    = Fʸ (c (suc n)) + Fʸ (c (suc n))
  N n (B.suc p) = Fʸ (c (suc n)) + map (eN n) p
  low : ∀ n {x} (p : x B.< O∘ f (suc n)) → map (eN n) p ≺ Fʸ (c (suc n))
  low n p = Fʸ⊑c (suc n) (below (eN n) p)
  Nb : ∀ n {x} (p : x B.< B.suc (O∘ f (suc n))) → N n p ≺ Bd (suc n)
  Nb n B.zero    = T3≺ (c (suc n))
  Nb n (B.suc p) = ≺→⊑₀ (T3≺ (c (suc n))) (add-≺ (Fʸ (c (suc n))) (low n p))
  Nm : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O∘ f (suc n))) (q : d₂ B.< B.suc (O∘ f (suc n))) → d₁ B.< d₂ → N n p ≺ N n q
  Nm n B.zero    B.zero    r = ⊥-elim (<ᴰ-irrefl r)
  Nm n B.zero    (B.suc q) r = ⊥-elim (clash-lt r q)
  Nm n (B.suc p) B.zero    r = add-≺ (Fʸ (c (suc n))) (low n p)
  Nm n (B.suc p) (B.suc q) r = add-≺ (Fʸ (c (suc n))) (mono (eN n) p q r)
  Nc : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O∘ f (suc n))) (q : d₂ B.< B.suc (O∘ f (suc n))) → d₁ ≡ d₂ → N n p ≅ N n q
  Nc n B.zero    B.zero    r = ≅-refl⁰ _
  Nc n B.zero    (B.suc q) refl = ⊥-elim (<ᴰ-irrefl q)
  Nc n (B.suc p) B.zero    refl = ⊥-elim (<ᴰ-irrefl p)
  Nc n (B.suc p) (B.suc q) r = add-≅ (≅-refl⁰ _) (coh (eN n) p q r)
  to-A : ∀ n {x} → x ≺ Bd n → x ≺ Fʸ (c (suc n))
  to-A n h = Fʸ⊑c (suc n) (Bd⊑ n h)
  fl : ∀ n {x} → x ≺ Bd n → ∀ {y} (p : y B.< B.suc (O∘ f (suc n))) → x ≺ N n p
  fl n h B.zero    = add-left (to-A n h) _
  fl n h (B.suc p) = add-left (to-A n h) _
  sp : ∀ n {x} → x ≺ Bd n → x ≺ Fʸ (lim f s)
  sp n h = ≺l (suc n) (Bd⊑ n h)
```
