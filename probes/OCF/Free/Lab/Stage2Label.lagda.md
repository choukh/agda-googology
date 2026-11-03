# Stage2Label (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Stage2Label](../../Align/Stage2Label.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Stage2Label where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Symbolic using (Ctx; Pt; pt; lvP; Γᶜ; Mlev; σ1; X₂ᵗ)
open import OCF.Free.Lab.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; fΩ̂; ψᴾ; trˢ; tr⁻ˢ; outs; Goodᶻ; force; force-HS; _~_; H₊; Rh→~; ~→Rh; ψ~; Ω~; z<suc; empty-agree; X₂ˢ; z2)
import OCF.Free.Lab.NoCumsum as N
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Free.Lab.Label using (BTBO-label)
open import OCF.Free.Lab.Bachmann using (<sucT)
open import OCF.Free.Lab.Closure using (lt→<)
open import OCF.Free.Lab.Standard using () renaming (d₀ to d₀ᴰ)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-pred; NF₁-fsn; cofin₁; γ′-NF; diag₁-desc-NF; walkD)
open import OCF.Free.Lab.Stage2 using (≺→⊑; ctx; γ′ᴱ; Lab-uniq; Ωᵗ)
open import OCF.Free.Lab.UniformS
open import OCF.Free.Aux public using (one⁰; two⁰)
```

```agda
open Ord-Ord using (iter)
open E using (T; natT; fsn; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_) renaming (ψ to ψᵗ)
```

## §1 无符号输入与 `Ok`

```agda
Pl : ∀ {k} → Ordˢ k → Set
Pl x = Σ Ordᴵ λ ℓ′ → Σ (Ordᶜ ℓ′) λ y → x ~ y

~suc : ∀ {k ℓ′} {a : Ordˢ k} {y : Ordᶜ ℓ′} → Ord₊ˢ.suc a ~ y → Pl a
~suc (H₊.s~ d)              = _ , _ , d
~suc (H₊.upʳ {r = zero} d)   = ~suc d
~suc (H₊.upʳ {r = self n} d) = ~suc d

~lim : ∀ {k ℓ′} {f : ℕ → Ordˢ k} {y : Ordᶜ ℓ′} → Ord₊ˢ.lim f ~ y → ∀ n → Pl (f n)
~lim (H₊.l~ h) n              = _ , _ , h n
~lim (H₊.upʳ {r = zero} d) n   = ~lim d n
~lim (H₊.upʳ {r = self m} d) n = ~lim d n

~up : ∀ {k ℓ ℓ′} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} {y : Ordᶜ ℓ′} → Ord₊ˢ.up r x ~ y → Pl (outˢ (◃₁→◃ r) x)
~up zero     (H₊.upˡ d)              = _ , _ , d
~up (self n) (H₊.upˡ d)              = _ , _ , d
~up r        (H₊.upʳ {r = zero} d)   = ~up r d
~up r        (H₊.upʳ {r = self n} d) = ~up r d

~ŝ : ∀ {k ℓ′ c t₀ g} {y : Ordᶜ ℓ′} → Ord₊ˢ.ŝ {ℓ = k} c t₀ g ~ y → ⊥
~ŝ (H₊.upʳ {r = zero} d)   = ~ŝ d
~ŝ (H₊.upʳ {r = self n} d) = ~ŝ d

~ĉ : ∀ {k ℓ′ c t₀ g o₀ o} {y : Ordᶜ ℓ′} → Ord₊ˢ.ĉᴸ {ℓ = k} c t₀ g o₀ o ~ y → ⊥
~ĉ (H₊.upʳ {r = zero} d)   = ~ĉ d
~ĉ (H₊.upʳ {r = self n} d) = ~ĉ d

chain0 : ∀ {j k ℓ} (σ : Simᴵ k ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chain0 {j} σ q f = iter (λ x → ψ0 (σ q) σ (f (intoˢ (<→◃ q) x))) (Ωˢ j)

chain1 : ∀ {j k ℓ} (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) (q : j <ᴵ k) (f : Uˢ j (<→◃ q) → Ordˢ k) → ℕ → Ordˢ j
chain1 {j} σ z q f = iter (λ x → ψ1 (σ q) σ z (f (intoˢ (<→◃ q) x))) (Ωˢ j)

~chain : ∀ {j k ℓ ℓ′} (σ : Simᴵ k ℓ) {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {y : Ordᶜ ℓ′} →
         Ord₊ˢ.limᵢ q f ~ y → ∀ n → Pl (f (intoˢ (<→◃ q) (chain0 σ q f n)))
~chain σ {q = q} {f = f} (H₊.lᵢ~ {q = q′} {g = g} e h) n = _ , _ , h _ _ (~→Rh (<→◃ q) (ch n))
  where
  ch = iter-R _~_ {G = λ x → ψ0 (σ q) σ (f (intoˢ (<→◃ q) x))} {G′ = λ y → ψ q′ (λ r → r) (g (into (<→◃ q′) y))}
              (λ d → ψ~ {p = σ q} {σ = σ} {p′ = q′} {σ′ = λ r → r} e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
~chain σ (H₊.upʳ {r = zero} d)   n = ~chain σ d n
~chain σ (H₊.upʳ {r = self m} d) n = ~chain σ d n

Pl-Ω : ∀ a → Pl (Ωˢ a)
Pl-Ω a = _ , Ω a , Ω~ (≅ᴵ-refl a)
```

```agda
Ok : (i : Ordᴵ) → ∀ {k} → Ordˢ k → Set
Ok zero      x = Pl x
Ok (suc _)   x = ⊤
Ok (lim _ _) x = ⊤

Ok-Pl : ∀ i {k} {x : Ordˢ k} → Pl x → Ok i x
Ok-Pl zero      h = h
Ok-Pl (suc _)   h = tt
Ok-Pl (lim _ _) h = tt

Ok-suc : ∀ i {k} {a : Ordˢ k} → Ok i (Ord₊ˢ.suc a) → Ok i a
Ok-suc zero      (_ , _ , d) = ~suc d
Ok-suc (suc _)   _ = tt
Ok-suc (lim _ _) _ = tt

Ok-lim : ∀ i {k} {f : ℕ → Ordˢ k} → Ok i (Ord₊ˢ.lim f) → ∀ n → Ok i (f n)
Ok-lim zero      (_ , _ , d) n = ~lim d n
Ok-lim (suc _)   _ n = tt
Ok-lim (lim _ _) _ n = tt

Ok-up : ∀ i {k ℓ} (r : k ◃₁ ℓ) {x : Uˢ k (◃₁→◃ r)} → Ok i (Ord₊ˢ.up r x) → Ok i (outˢ (◃₁→◃ r) x)
Ok-up zero      r (_ , _ , d) = ~up r d
Ok-up (suc _)   r _ = tt
Ok-up (lim _ _) r _ = tt

Ok-col : ∀ {i j k ℓ} (σ : Simᴵ k ℓ) {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
         (i ≺ᴵ j ⊎ j ≅ᴵ i) → Ok i (Ord₊ˢ.limᵢ q f) →
         ∀ n → Ok j (f (intoˢ (<→◃ q) (chain0 σ q f n))) × Ok i (f (intoˢ (<→◃ q) (chain0 σ q f n)))
Ok-col {i = zero}    {j} σ c (_ , _ , d) n = Ok-Pl j (~chain σ d n) , ~chain σ d n
Ok-col {i = suc _}   {j = zero}    σ (inj₁ (via e ())) ok n
Ok-col {i = suc _}   {j = zero}    σ (inj₂ ()) ok n
Ok-col {i = suc _}   {j = suc _}   σ c ok n = tt , tt
Ok-col {i = suc _}   {j = lim _ _} σ c ok n = tt , tt
Ok-col {i = lim _ _} {j = zero}    σ (inj₁ (via e ())) ok n
Ok-col {i = lim _ _} {j = zero}    σ (inj₂ ()) ok n
Ok-col {i = lim _ _} {j = suc _}   σ c ok n = tt , tt
Ok-col {i = lim _ _} {j = lim _ _} σ c ok n = tt , tt
```

## §2 规则 6 的链

```agda
chain0-≅ : ∀ {j k k′ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
           Ord₊ˢ.limᵢ q f ≅ˢ b → ∀ n → chain0 σ q f n ≅ˢ chain0 σ q f n
chain0-≅ {j} e zero    = Ωˢ-refl j
chain0-≅ {j} e (suc n) = ψ0-≅ (≅ᴵ-refl j) (i-respˢ e (chain0-≅ e n))

chain1-≅ : ∀ {j k k′ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
           Ord₊ˢ.limᵢ q f ≅ˢ b → ∀ n → chain1 σ z q f n ≅ˢ chain1 σ z q f n
chain1-≅ {j} e zero    = Ωˢ-refl j
chain1-≅ {j} e (suc n) = ψ1-≅ (≅ᴵ-refl j) (i-respˢ e (chain1-≅ e n))

chain0-step : ∀ {j k k′ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} → Ord₊ˢ.limᵢ q f ≅ˢ b →
              (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
              ∀ n → chain0 σ q f n ⊑ᵒ chain0 σ q f (suc n)
chain0-step {j} {σ = σ} {q = q} {f = f} e hm zero =
  B1₀ {q = σ q} {σ = σ} (≅→⊑ᵒ (Ωˢ-refl j)) (f (intoˢ (<→◃ q) (Ωˢ j))) (i-respˢ e (Ωˢ-refl j))
chain0-step e hm (suc n) = ψ0-cong (hm (chain0-step e hm n))

Ω⊑pop : ∀ {j k ℓ} (t : j <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) → Ωˢ j ⊑ᵒ ψ1 t σ z Ord₊ˢ.zero
Ω⊑pop {j} t σ z = ŝ-r (B1₀ (≅→⊑ᵒ (Ωˢ-refl j)) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)))

chain1-step : ∀ {j k k′ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} {b : Ordˢ k′} →
              Ord₊ˢ.limᵢ q f ≅ˢ b →
              (∀ {z z′ : Ordˢ j} → z ⊑ᵒ z′ → f (intoˢ (<→◃ q) z) ⊑ᵒ f (intoˢ (<→◃ q) z′)) →
              ∀ n → chain1 σ z q f n ⊑ᵒ chain1 σ z q f (suc n)
chain1-step {j} {σ = σ} {z = z} {q = q} {f = f} e hm zero =
  B1₁ {q = σ q} {σ = σ} {z₁ = z} (Ω⊑pop (σ q) σ z) (f (intoˢ (<→◃ q) (Ωˢ j))) (i-respˢ e (Ωˢ-refl j))
chain1-step e hm (suc n) = ψ1-cong (hm (chain1-step e hm n))
```

## §3 空栈的闭包定理

```agda
mkĉ : ∀ {ℓ c} {t₀ : Ordˢ zero} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ zero} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} →
      Good t₀ → (∀ η e → Good (g η e)) → (∀ η e → t₀ ⊑ᵒ g η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → g η e ⊑ᵒ g η′ e′) →
      Dom zero c t₀ g → Good o₀ → (∀ η e → Good (o η e)) →
      (∀ η e → o₀ ⊑ᵒ o η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → o η e ⊑ᵒ o η′ e′) →
      Good (Ord₊ˢ.ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) o₀ o)
mkĉ g0 gg m mm (d₀ , dE) go gO mo mO =
  bĉ G₀ Gg (d₀ G₀) (λ η e → dE η e (Gg η e))
     (λ η e → m η e idO G₀ (Gg η e)) (λ η e η′ e′ h → mm η e η′ e′ h idO (Gg η e) (Gg η′ e′))
     go gO mo mO
  where
  G₀ = Good→Goodᶻ g0
  Gg = λ η e → Good→Goodᶻ (gg η e)

Ok-pen : ∀ {i j k} {x : Ordˢ k} → j <ᴵ i → Ok i x
Ok-pen {i = suc _}   r = tt
Ok-pen {i = lim _ _} r = tt

Good-ψ0 : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordˢ k} → Good x → x ≅ˢ x → Ok i x → Good (ψ0 p σ x)
chain0-good : ∀ {j k ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
              (∀ (z : Ordˢ j) → z ≅ˢ z → Gd j (<→◃ q) (intoˢ (<→◃ q) z) → Good (f (intoˢ (<→◃ q) z))) →
              Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → (∀ n → Ok j (f (intoˢ (<→◃ q) (chain0 σ q f n)))) →
              ∀ n → Good (chain0 σ q f n)
chain0-good {j} hb e ok zero = Good-Ω j
chain0-good {σ = σ} {q = q} {f = f} hb e ok (suc n) =
  Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ e n) (Good→Gd (<→◃ q) (chain0-good hb e ok n))) (i-respˢ e (chain0-≅ e n)) (ok n)

Good-ψ0 {i} bz ex ok = Good-Ω i
Good-ψ0 {i} {p = p} {σ = σ} (bs g) ex ok = bl (Good-iter (Good-ψ0 g ea (Ok-suc i ok)) eψ) (rule4ᵒ eψ)
  where ea = s-invˢ ex
        eψ = ψ0-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
Good-ψ0 {i} (bl hg st) ex ok = bl (λ n → Good-ψ0 (hg n) (l-invˢ ex n) (Ok-lim i ok n)) (λ n → ψ0-cong (st n))
Good-ψ0 {i} {p = p} {σ = σ} (bi {j = j} {p = q} {f = f} hb hm) ex ok with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = bi
  (λ z ez g → subst (λ u → Good (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))))) (sym (out-intoˢ (<→◃ r) z))
                    (Good-ψ0 (hb (tr⁻ˢ e z) (self-tr⁻ˢ e ez) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                             (i-respˢ ex (self-tr⁻ˢ e ez)) (Ok-pen r)))
  (λ {z} {z′} h → subst₂ (λ u v → ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ⊑ᵒ ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v))))
                         (sym (out-intoˢ (<→◃ r) z)) (sym (out-intoˢ (<→◃ r) z′)) (ψ0-cong (hm (tr⁻-cong h))))
... | injᵇ c = bl (λ n → Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ ex n)
                                       (Good→Gd (<→◃ q) (chain0-good hb ex (λ m → proj₁ (Ok-col σ (inj₁ c) ok m)) n)))
                                  (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₁ c) ok n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
... | injᶜ c = bl (λ n → Good-ψ0 (hb (chain0 σ q f n) (chain0-≅ ex n)
                                       (Good→Gd (<→◃ q) (chain0-good hb ex (λ m → proj₁ (Ok-col σ (inj₂ c) ok m)) n)))
                                  (i-respˢ ex (chain0-≅ ex n)) (proj₂ (Ok-col σ (inj₂ c) ok n)))
                  (λ n → ψ0-cong (hm (chain0-step ex hm n)))
Good-ψ0 {i} (bu {r = zero} g) ex ok   = Good-ψ0 g (u-reflˢ zero ex) (Ok-up i zero ok)
Good-ψ0 {i} (bu {r = self n} g) ex ok = Good-ψ0 g (u-reflˢ (self n) ex) (Ok-up i (self n) ok)
Good-ψ0 {i = zero} (bŝ g0 gg et eg m mm dm) ex (_ , _ , d) = ⊥-elim (~ŝ d)
Good-ψ0 {i = suc _} {k = zero} (bŝ g0 gg et eg m mm dm) ex ok =
  mkĉ g0 gg m mm dm (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
Good-ψ0 {i = lim _ _} {k = zero} (bŝ g0 gg et eg m mm dm) ex ok =
  mkĉ g0 gg m mm dm (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
      (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h))
Good-ψ0 {i = suc _} {k = suc _} (bŝ g0 gg et eg m mm dm) ex ok =
  bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
Good-ψ0 {i = suc _} {k = lim _ _} (bŝ g0 gg et eg m mm dm) ex ok =
  bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
Good-ψ0 {i = lim _ _} {k = suc _} (bŝ g0 gg et eg m mm dm) ex ok =
  bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
Good-ψ0 {i = lim _ _} {k = lim _ _} (bŝ g0 gg et eg m mm dm) ex ok =
  bŝ (Good-ψ0 g0 et tt) (λ η e → Good-ψ0 (gg η e) (eg η e η e (≅ᴵ-refl η)) tt)
     (ψ0-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ0-cong (m η e)) (λ η e η′ e′ h → ψ0-cong (mm η e η′ e′ h)) dm
Good-ψ0 {i = zero} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex (_ , _ , d) = ⊥-elim (~ĉ d)
Good-ψ0 {i = suc _} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ0 go (ĉ-refl₀ ex) tt) (λ η e → Good-ψ0 (gO η e) (ĉ-reflg ex η e) tt)
     (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))
Good-ψ0 {i = lim _ _} (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex ok =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ0 go (ĉ-refl₀ ex) tt) (λ η e → Good-ψ0 (gO η e) (ĉ-reflg ex η e) tt)
     (λ η e → ψ0-cong (mo η e)) (λ η e η′ e′ h → ψ0-cong (mO η e η′ e′ h))
```

## §4 严格性引理

```agda
Strict₀ : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} (y : Ordˢ k) → y ≅ˢ y → (G : Goodᶻ (toZ (ψ0 p σ y))) →
          suc zero ⊑ᴵ toLevel (force _ G) (force-HS _ G)
Strict₀ {p = p} {σ = σ} y ey G =
  toLevel-⊑ (hs hz) (force-HS _ G) (B1₀ {q = p} {σ = σ} (≅→⊑ᵒ (Ωˢ-refl zero)) y ey idO (Goodᶻ.gs Goodᶻ.gz) G)

t₀pop : ∀ {i ℓ} → i <ᴵ ℓ → zero <ᴵ ℓ → Ordˢ i
t₀pop {i} p z = ψ0 {ℓ = suc i} zero (σ1 (z<suc z p)) (Ωˢ (suc zero))

gpop : ∀ {i ℓ} → i <ᴵ ℓ → zero <ᴵ ℓ → (η : Ordᴵ) → suc i ⊑ᴵ η → Ordˢ i
gpop {i} p z η e = ψ0 {ℓ = Mlev (suc i) η e} (lim 0 zero) (λ q → lim 1 q) (Ωˢ η)

popGood : ∀ {i k ℓ} (p : i <ᴵ ℓ) (σ : Simᴵ k ℓ) (z : zero <ᴵ ℓ) → Dom i (suc i) (t₀pop p z) (gpop p z) →
          Good (ψ1 p σ z Ord₊ˢ.zero)
popGood {i} p σ z dm =
  bŝ (Good-ψ0 (Good-Ω (suc zero)) (Ωˢ-refl (suc zero)) (Ok-Pl i (Pl-Ω (suc zero))))
     (λ η e → Good-ψ0 (Good-Ω η) (Ωˢ-refl η) (Ok-Pl i (Pl-Ω η)))
     (ψ0-≅ (≅ᴵ-refl i) (Ωˢ-refl (suc zero))) (λ η e η′ e′ eη → ψ0-≅ (≅ᴵ-refl i) (Ωˢ-≅ eη))
     (λ η e → ψ0-cong (Ω-monoᵒ (⊑ᴵ-trans (s⊑ z≅ (z<suc z p)) e))) (λ η e η′ e′ h → ψ0-cong (Ω-monoᵒ h)) dm

popDom₀ : ∀ {ℓ} (p : zero <ᴵ ℓ) (z : zero <ᴵ ℓ) → Dom zero (suc zero) (t₀pop p z) (gpop p z)
popDom₀ p z = (λ G → Strict₀ (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G) , (λ η e G → Strict₀ (Ωˢ η) (Ωˢ-refl η) G)

popDom : ∀ {i ℓ} (p : i <ᴵ ℓ) (z : zero <ᴵ ℓ) → ℓ ⊑ᴵ two → Dom i (suc i) (t₀pop p z) (gpop p z)
popDom {i = zero}    p z h = popDom₀ p z
popDom {i = suc _}   p z h = s⊑′ (sim h p)
popDom {i = lim _ _} p z h = s⊑′ (sim h p)
```

```agda
two⊑ : ∀ {X : Ordᶜ zero} → one⁰ ≺ X → two⁰ ⊑ X
two⊑ h (≺z e)  = ≺-respˡ (≅-sym e) h
two⊑ h (≺s h′) = ≺→⊑ h h′

h2 : (G : Goodᶻ (Z.suc (Z.suc Z.zero))) → one⁰ ≺ force _ G
h2 (Goodᶻ.gs (Goodᶻ.gs Goodᶻ.gz)) = ≺z (s≅ z≅)

one≺ω : (G : Goodᶻ (toZ {- ψ₀(1) -} (Ord₊ˢ.lim (iter (Ord₊ˢ.suc Ord₊ˢ.zero +ˢ_) Ord₊ˢ.zero)))) → one⁰ ≺ force _ G
one≺ω (Goodᶻ.gl Gs st) = ≺l 2 (h2 (Gs 2))

one≺ : ∀ {L} {p : zero <ᴵ L} (σ : Simᴵ (suc zero) L) (G : Goodᶻ (toZ (ψ0 p σ (Ωˢ (suc zero))))) → one⁰ ≺ force _ G
one≺ {p = p} σ G = le idO G₁ G (one≺ω G₁)
  where
  u : Ordˢ (suc zero)
  u = Ord₊ˢ.up zero (Ord₊ˢ.suc Ord₊ˢ.zero)
  u⊑ : u ⊑ᵒ Ωˢ (suc zero)
  u⊑ = limᵢ-r (λ z d → up-l {r = zero} (up-r {r = zero} {y = z} (≅→⊑ᵒ (≅ˢ-sym d))))
  le : ψ0 p σ u ⊑ᵒ ψ0 p σ (Ωˢ (suc zero))
  le = ψ0-cong {p = p} {p′ = p} {σ = σ} {σ′ = σ} u⊑
  G₁ : Goodᶻ (toZ (ψ0 p σ u))
  G₁ = Good→Goodᶻ (Good-ψ0 (bu (bs bz)) (upˡ (upʳ (s≅ z≅))) (zero , one⁰ , H₊.upˡ (H₊.s~ H₊.z~)))

onepop : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) (G : Goodᶻ (toZ (ψ1 p σ z Ord₊ˢ.zero))) → one⁰ ≺ force _ G
onepop p σ z (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = ≺l 0 (one≺ (σ1 (z<suc z p)) Go₀)

Strict₁ : ∀ {L k} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} (y : Ordˢ k) → y ≅ˢ y → (G : Goodᶻ (toZ (ψ1 p σ z y))) →
          two ⊑ᴵ toLevel (force _ G) (force-HS _ G)
Strict₁ {k = k} {p = p} {σ = σ} {z = z} y ey G =
  toLevel-⊑ (hs (hs hz)) (force-HS _ G)
            (two⊑ (B1₁ {q = p} {σ = σ} {z₁ = z} {x = ψ1 p σ z (𝟎ˢ {k})}
                       (≅→⊑ᵒ (ψ1-≅ {k₁ = k} {k₂ = k} {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl zero) z≅))
                       y ey idO G₀ G (onepop p σ z G₀)))
  where G₀ = Good→Goodᶻ (popGood p σ z (popDom₀ p z))
```

## §5 单 $\hat\Omega$ 栈的闭包定理

```agda
Dom-ψ1 : ∀ {L k c} {p : zero <ᴵ L} {σ : Simᴵ k L} {z : zero <ᴵ L} {t₀ : Ordˢ k} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ k} →
         c ⊑ᴵ two → t₀ ≅ˢ t₀ → (∀ η e → g η e ≅ˢ g η e) →
         Dom zero c (ψ1 p σ z t₀) (λ η e → ψ1 p σ z (g η e))
Dom-ψ1 {t₀ = t₀} {g = g} dm et eg =
  (λ G → ⊑ᴵ-trans dm (Strict₁ t₀ et G)) , (λ η e G → ⊑ᴵ-trans dm (Strict₁ (g η e) (eg η e) G))

Good-ψ1 : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {x : Ordˢ k} → ℓ ⊑ᴵ two → Good x → x ≅ˢ x →
          Good (ψ1 p σ z x)
chain1-good : ∀ {j k ℓ} {σ : Simᴵ k ℓ} {z : zero <ᴵ ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} → ℓ ⊑ᴵ two →
              (∀ (y : Ordˢ j) → y ≅ˢ y → Gd j (<→◃ q) (intoˢ (<→◃ q) y) → Good (f (intoˢ (<→◃ q) y))) →
              Ord₊ˢ.limᵢ q f ≅ˢ Ord₊ˢ.limᵢ q f → ∀ n → Good (chain1 σ z q f n)
chain1-good {j} h hb e zero = Good-Ω j
chain1-good {σ = σ} {z = z} {q = q} {f = f} h hb e (suc n) =
  Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ e n) (Good→Gd (<→◃ q) (chain1-good h hb e n))) (i-respˢ e (chain1-≅ e n))

Good-ψ1 {p = p} {σ = σ} {z = z} h bz ex = popGood p σ z (popDom p z h)
Good-ψ1 {i} {p = p} {σ = σ} {z = z} h (bs g) ex = bl (Good-iter (Good-ψ1 h g ea) eψ) (rule4ᵒ eψ)
  where ea = s-invˢ ex
        eψ = ψ1-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} {z = z} {z′ = z} (≅ᴵ-refl i) ea
Good-ψ1 h (bl hg st) ex = bl (λ n → Good-ψ1 h (hg n) (l-invˢ ex n)) (λ n → ψ1-cong (st n))
Good-ψ1 {p = p} {σ = σ} {z = z} h (bi {j = j} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = bi
  (λ y ey g → subst (λ u → Good (ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e u))))) (sym (out-intoˢ (<→◃ r) y))
                    (Good-ψ1 h (hb (tr⁻ˢ e y) (self-tr⁻ˢ e ey) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                               (i-respˢ ex (self-tr⁻ˢ e ey))))
  (λ {y} {y′} hy → subst₂ (λ u v → ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e u))) ⊑ᵒ ψ1 p σ z (f (intoˢ (<→◃ q) (tr⁻ˢ e v))))
                          (sym (out-intoˢ (<→◃ r) y)) (sym (out-intoˢ (<→◃ r) y′)) (ψ1-cong (hm (tr⁻-cong hy))))
... | injᵇ _ = bl (λ n → Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1-good h hb ex n)))
                                    (i-respˢ ex (chain1-≅ ex n)))
                  (λ n → ψ1-cong (hm (chain1-step ex hm n)))
... | injᶜ _ = bl (λ n → Good-ψ1 h (hb (chain1 σ z q f n) (chain1-≅ ex n) (Good→Gd (<→◃ q) (chain1-good h hb ex n)))
                                    (i-respˢ ex (chain1-≅ ex n)))
                  (λ n → ψ1-cong (hm (chain1-step ex hm n)))
Good-ψ1 h (bu {r = zero} g) ex   = Good-ψ1 h g (u-reflˢ zero ex)
Good-ψ1 h (bu {r = self n} g) ex = Good-ψ1 h g (u-reflˢ (self n) ex)
Good-ψ1 {i = zero} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
Good-ψ1 {i = suc _} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
Good-ψ1 {i = lim _ _} {k = zero} h (bŝ g0 gg et eg m mm dm) ex =
  mkĉ g0 gg m mm dm (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
      (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
Good-ψ1 {i = zero} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
     (Dom-ψ1 dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
Good-ψ1 {i = zero} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh))
     (Dom-ψ1 dm et (λ η e → eg η e η e (≅ᴵ-refl η)))
Good-ψ1 {i = suc _} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
Good-ψ1 {i = suc _} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
Good-ψ1 {i = lim _ _} {k = suc _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
Good-ψ1 {i = lim _ _} {k = lim _ _} h (bŝ g0 gg et eg m mm dm) ex =
  bŝ (Good-ψ1 h g0 et) (λ η e → Good-ψ1 h (gg η e) (eg η e η e (≅ᴵ-refl η)))
     (ψ1-≅ (≅ᴵ-refl _) et) (λ η e η′ e′ eη → ψ1-≅ (≅ᴵ-refl _) (eg η e η′ e′ eη))
     (λ η e → ψ1-cong (m η e)) (λ η e η′ e′ hh → ψ1-cong (mm η e η′ e′ hh)) dm
Good-ψ1 h (bĉ G₀ Gg d₀ dE m₀ mE go gO mo mO) ex =
  bĉ G₀ Gg d₀ dE m₀ mE (Good-ψ1 h go (ĉ-refl₀ ex)) (λ η e → Good-ψ1 h (gO η e) (ĉ-reflg ex η e))
     (λ η e → ψ1-cong (mo η e)) (λ η e η′ e′ hh → ψ1-cong (mO η e η′ e′ hh))
```

## §6 检验 1: $\psi_0(\Omega_\Omega+\Omega_2)$ 的计值树

```agda
X₂-good : Good X₂ˢ
X₂-good = Good-ψ1 {p = z2} {σ = λ q → q} {z = z2} ⊑ᴵ-refl (Good-Ω two) (Ωˢ-refl two)

GX₂ : Goodᶻ (toZ X₂ˢ)
GX₂ = Good→Goodᶻ X₂-good

X₂ᶠ : Ordᶜ zero
X₂ᶠ = force (toZ X₂ˢ) GX₂
```

## §7 计值与加法、目标 0 的弹栈闭包

```agda
outsMap : (C C′ : Ctx) → Ctx.t₀ C ≅ Ctx.t₀ C′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Ctx.E C η e ≅ Ctx.E C′ η′ e′) →
          ∀ {O₀ O} {P₀ : Ordᶜ zero} {P : (η : Ordᴵ) → Ctx.c C′ ⊑ᴵ η → Ordᶜ zero} (F : Ordᶜ zero → Ordᶜ zero) →
          O₀ ≅ F P₀ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≅ F (P η′ e′)) →
          ∀ n → outs C O₀ O n ≅ F (outs C′ P₀ P n)
outsMap C C′ h₀ hE F o₀ hO zero    = o₀
outsMap C C′ h₀ hE F o₀ hO (suc k) =
  hO _ _ _ _ (toLevel-≅ (Pt.hx (Γᶜ C k)) (Pt.hx (Γᶜ C′ k)) (chain≅ C C′ h₀ hE k))
```

```agda
pop0≅ : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) (G : Goodᶻ (toZ (ψ1 p σ z Ord₊ˢ.zero))) →
        force _ G ≅ N.BTBOᴵ
pop0≅ p σ z (Goodᶻ.gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) = l≅ outs≅′
  where
  C : Ctx
  C = record { c = suc zero ; t₀ = force (toZ (t₀pop p z)) G₀ ; E = λ η e → force (toZ (gpop p z η e)) (Gg η e)
             ; h₀ = force-HS _ G₀ ; hE = λ η e → force-HS _ (Gg η e) ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }
  ag₀ : ∀ G → force (toZ (t₀pop p z)) G ≅ ψ⁰ (Ω (suc zero))
  ag₀ G = empty-agree zero (σ1 (z<suc z p)) G
  agβ : ∀ η e G → force (toZ (gpop p z η e)) G ≅ ψ⁰ (Ω η)
  agβ η e G = empty-agree (lim 0 zero) (λ q → lim 1 q) G
  pts : ∀ k → Pt.x (Γᶜ C k) ≅ N.γ (suc k)
  pts zero    = ag₀ G₀
  pts (suc k) = ≅-trans (agβ _ _ (Gg _ _)) (ψ⁰-≅ (Ω-≅ (toLevel-≅ (Pt.hx (Γᶜ C k)) (N.cert (suc k)) (pts k))))
  outs≅′ : ∀ n → outs C (force (toZ (t₀pop p z)) Go₀) (λ η e → force (toZ (gpop p z η e)) (Go η e)) n ≅ N.γ (suc n)
  outs≅′ zero    = ag₀ Go₀
  outs≅′ (suc k) = ≅-trans (agβ _ _ (Go _ _)) (ψ⁰-≅ (Ω-≅ (toLevel-≅ (Pt.hx (Γᶜ C k)) (N.cert (suc k)) (pts k))))

pop0-label : ∀ {L k} (p : zero <ᴵ L) (σ : Simᴵ k L) (z : zero <ᴵ L) (G : Goodᶻ (toZ (ψ1 p σ z Ord₊ˢ.zero))) →
             Lab (force _ G) (E.EBOψ 2)
pop0-label p σ z G = Lab-≅ (pop0≅ p σ z G) BTBO-label
```

## §10 序的对应来自标签

```agda
Lab-oc : ∀ {X Y : Ordᶜ zero} {u v : T} → Lab X u → NF₁ u → Lab Y v → NF₁ v → v <ᵀ u → Y ≺ X
Lab-oc {u = []} (l0 c e) nu lY nv ()
Lab-oc {u = x ∷ xs} (l0 c e) nu lY nv p = ⊥-elim (cof-ne x xs c)
Lab-oc {u = u} {v = v} (l1 c e l) nu lY nv p with <sucT (pred u) (subst (v <ᵀ_) (sym (E.pred-suc u c)) p)
... | inj₁ q    = ≺-respʳ (≺s (Lab-oc l (NF₁-pred nu c) lY nv q)) (≅-sym e)
... | inj₂ refl = ≺-respʳ (≺z (Lab-uniq lY l)) (≅-sym e)
Lab-oc (lω c e h) nu lY nv p with cofin₁ nu c nv p
... | n , q = ≺-respʳ (≺l n (Lab-oc (h n) (NF₁-fsn nu c n) lY nv q)) (≅-sym e)
```

## §13 结论与边界
