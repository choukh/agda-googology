# 一切深度 (一): 脊与观测

> 接 [UniformNF3D2U](UniformNF3D2U.lagda.md) §4. 结论先说:
>
> 1. **`Sp d`, `Fr d φ`: 反柯里化的帧.** 深度 $d$ 的帧吃一条脊 $s$ (外层的帧, 一直到底), 给一个 `Run`. `fold1` 对任意 $d$ 只在后继行碰脊的头, 其余各行都是 `Run` 层的定义性计算, **对未知的 $d$ 也定义性地算**. 这解除了 "把 `fo2`, `fo3`, … 逐个加进 `Obs`" 的需要.
> 2. **`Obs` 的 `fo1` 现在吃任意深度:** `fo1 {d} O E s ev p` 的 `run` 是 `fold1 (flo k) (cvFlo k) E x s ev p`. 规则层只有这一个高阶构造子, 不随深度增长.
> 3. `run-≅` 对一切深度成立: `fold-≅U` 是 `fold-≅1` 的克隆, 只把 "$P\approx P'$" 换成 "脊 $s\approx s'$".
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3O where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_)
open Restrˢ
open import OCF.Align.UniformNF3Eq using (flo-∼; limR; limᵢR; ĉR; ŝR; wkR; ≅→Rˢ; tf; ≅ᴵ→⊑ᴵ; _≅ᶻ_; ≅ᶻ-sym; ≅ᶻ-trans;
  _≅ˢ_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; toZ-≅;
  trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; addˢ-≅; _≈ᴿ_; fold-≅0; cloR)
open import OCF.Align.Uniform3Base using (⊔∼; Flr; fz; fk; _⊔_; Ev; Run; limᵢA; ŝA; ĉA; flo; cvFlo; toFlo; fold; Ω̂A; ∅ᴿ; _∼ᶠ_; ∼ᶠ-refl; cloA)
```

## §1 脊与反柯里化的帧

```agda
mutual
  Sp : ℕ → Set
  Sp zero    = ⊤
  Sp (suc d) = Σ Flr λ fl → Fr d fl × Sp d

  sf : ∀ {d : ℕ} → Sp d → Flr
  sf {d = zero}  _            = fz
  sf {d = suc d} (fl , _ , s) = sf s ⊔ fl

  Fr : ℕ → Flr → Set
  Fr d φ = (s : Sp d) → Run (sf s ⊔ φ)

repU : ∀ {d fl ψ} → Fr d fl → Fr (suc d) ψ → ℕ → Fr d (fl ⊔ ψ)
repU P F zero          s ev p = P s (proj₁ ev , proj₁ (proj₂ ev)) p
repU {fl = fl} P F (suc zero)    s ev p = F (fl , P , s) ((proj₁ ev , proj₁ (proj₂ ev)) , proj₂ (proj₂ ev)) p
repU {fl = fl} {ψ = ψ} P F (suc (suc m)) s ev p = F ((fl ⊔ ψ) , repU P F (suc m) , s) (ev , proj₂ (proj₂ ev)) p

rowU : ∀ {d ψ} (Q : Sp (suc d)) → Fr (suc d) ψ → ℕ → Run (sf Q ⊔ ψ)
rowU (fl , P , s) F m ev p = repU P F m s (proj₁ (proj₁ ev) , (proj₂ (proj₁ ev) , proj₂ ev)) p

fold1 : ∀ {d flE k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → Fr (suc d) flE → Ordˢ k → Fr (suc d) (flE ⊔ φ)
fold1 φ cv E Ord₊ˢ.zero s ev p = E s (proj₁ ev , proj₁ (proj₂ ev)) p
fold1 φ cv E (Ord₊ˢ.suc a) Q ev p = Ord₊ˢ.lim (λ m → rowU Q (fold1 φ cv E a) m ev p)
fold1 φ cv E (Ord₊ˢ.lim f) s ev p = Ord₊ˢ.lim (λ m → fold1 φ cv E (f m) s ev p)
fold1 φ cv E (Ord₊ˢ.limᵢ q f) s ev p = limᵢA 0 (λ e → cv (proj₂ (proj₂ e)) q) (λ x → fold1 φ cv E (f (intoˢ (<→◃ q) x)) s) ev p
fold1 {k = suc k′} φ cv E (Ord₊ˢ.up zero x) s ev p =
  fold1 (flo k′) (cvFlo k′) E x s (proj₁ ev , (proj₁ (proj₂ ev) , toFlo k′ (λ q → cv (proj₂ (proj₂ ev)) (suc q)))) p
fold1 {k = lim f t} φ cv E (Ord₊ˢ.up (self n) x) s ev p =
  fold1 (flo (f n)) (cvFlo (f n)) E x s (proj₁ ev , (proj₁ (proj₂ ev) , toFlo (f n) (λ q → cv (proj₂ (proj₂ ev)) (lim n q)))) p
fold1 {k = zero}    φ cv E (Ord₊ˢ.ŝ c t₀ g) s ev p =
  ĉA 0 c (toZ t₀) (λ η e → toZ (g η e)) (fold1 φ cv E t₀ s) (λ η e → fold1 φ cv E (g η e) s) ev p
fold1 {k = suc _}   φ cv E (Ord₊ˢ.ŝ c t₀ g) s ev p = ŝA 0 c (fold1 φ cv E t₀ s) (λ η e → fold1 φ cv E (g η e) s) ev p
fold1 {k = lim _ _} φ cv E (Ord₊ˢ.ŝ c t₀ g) s ev p = ŝA 0 c (fold1 φ cv E t₀ s) (λ η e → fold1 φ cv E (g η e) s) ev p
fold1 φ cv E (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) s ev p = ĉA 0 c t₀ g (fold1 φ cv E o₀ s) (λ η e → fold1 φ cv E (o η e) s) ev p
```

## §2 互模拟

```agda
mutual
  _≈S_ : ∀ {d : ℕ} → Sp d → Sp d → Set
  _≈S_ {d = zero} _ _ = ⊤
  _≈S_ {d = suc d} (fl , P , s) (fl′ , P′ , s′) = (fl ∼ᶠ fl′) × (P ≈U P′) × (s ≈S s′)

  _≈U_ : ∀ {d φ ψ} → Fr d φ → Fr d ψ → Set
  X ≈U X′ = ∀ {s s′} → s ≈S s′ → X s ≈ᴿ X′ s′

infix 4 _≈S_ _≈U_

repR : ∀ {d fl fl′ ψ ψ′} {Q : Fr d fl} {Q′ : Fr d fl′} {fr : Fr (suc d) ψ} {fr′ : Fr (suc d) ψ′} →
       fl ∼ᶠ fl′ → ψ ∼ᶠ ψ′ → Q ≈U Q′ → fr ≈U fr′ → ∀ m → repU Q fr m ≈U repU Q′ fr′ m
repR s sψ H F zero    ss ev p ev′ p′ ei = H ss _ p _ p′ ei
repR s sψ H F (suc zero) ss ev p ev′ p′ ei = F (s , H , ss) _ p _ p′ ei
repR s sψ H F (suc (suc m)) ss ev p ev′ p′ ei = F (⊔∼ s sψ , repR s sψ H F (suc m) , ss) _ p _ p′ ei

fold-≅U : ∀ {d flE flE′ k₁ k₂} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L}
          {E : Fr (suc d) flE} {E′ : Fr (suc d) flE′} {a : Ordˢ k₁} {b : Ordˢ k₂} →
          flE ∼ᶠ flE′ → E ≈U E′ → a ≅ˢ b → fold1 (flo k₁) cv E a ≈U fold1 (flo k₂) cv′ E′ b
fold-≅U sE HE z≅ ss ev p ev′ p′ ei = HE ss _ p _ p′ ei
fold-≅U sE HE (s≅ le e) {fl , P , s} {fl′ , P′ , s′} (sφ , H , ss) ev p ev′ p′ ei =
  l≅ (λ m → repR sφ (⊔∼ sE (flo-∼ le)) H (fold-≅U sE HE e) m ss _ p _ p′ ei)
fold-≅U sE HE (l≅ h) ss = limR (λ n → fold-≅U sE HE (h n) ss)
fold-≅U sE HE (lᵢ≅ {p = q} e h) ss =
  limᵢR e (λ x y d → fold-≅U sE HE (h x y (≅→Rˢ (<→◃ q) d)) ss)
fold-≅U {k₁ = suc k′} {cv = cv} sE HE (upˡ {r = zero} e) ss ev p ev′ p′ ei =
  fold-≅U {cv = cvFlo k′} sE HE e ss _ p _ p′ ei
fold-≅U {k₁ = lim f t} {cv = cv} sE HE (upˡ {r = self n} e) ss ev p ev′ p′ ei =
  fold-≅U {cv = cvFlo (f n)} sE HE e ss _ p _ p′ ei
fold-≅U {k₂ = suc k′} {cv′ = cv′} sE HE (upʳ {r = zero} e) ss ev p ev′ p′ ei =
  fold-≅U {cv′ = cvFlo k′} sE HE e ss _ p _ p′ ei
fold-≅U {k₂ = lim f t} {cv′ = cv′} sE HE (upʳ {r = self n} e) ss ev p ev′ p′ ei =
  fold-≅U {cv′ = cvFlo (f n)} sE HE e ss _ p _ p′ ei
fold-≅U {k₁ = zero} {k₂ = zero} sE HE (ŝ≅ k ec et eg) ss =
  ĉR ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (fold-≅U sE HE et ss)
     (λ η e η′ e′ eη → fold-≅U sE HE (eg η e η′ e′ eη) ss)
fold-≅U {k₁ = zero} {k₂ = suc _}   sE HE (ŝ≅ k ec et eg) ss = ⊥-elim (tf k)
fold-≅U {k₁ = zero} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) ss = ⊥-elim (tf k)
fold-≅U {k₁ = suc _}   {k₂ = zero} sE HE (ŝ≅ k ec et eg) ss = ⊥-elim (tf (sym k))
fold-≅U {k₁ = lim _ _} {k₂ = zero} sE HE (ŝ≅ k ec et eg) ss = ⊥-elim (tf (sym k))
fold-≅U {k₁ = suc _} {k₂ = suc _} sE HE (ŝ≅ k ec et eg) ss =
  ŝR ec (fold-≅U sE HE et ss) (λ η e η′ e′ eη → fold-≅U sE HE (eg η e η′ e′ eη) ss)
fold-≅U {k₁ = suc _} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) ss =
  ŝR ec (fold-≅U sE HE et ss) (λ η e η′ e′ eη → fold-≅U sE HE (eg η e η′ e′ eη) ss)
fold-≅U {k₁ = lim _ _} {k₂ = suc _} sE HE (ŝ≅ k ec et eg) ss =
  ŝR ec (fold-≅U sE HE et ss) (λ η e η′ e′ eη → fold-≅U sE HE (eg η e η′ e′ eη) ss)
fold-≅U {k₁ = lim _ _} {k₂ = lim _ _} sE HE (ŝ≅ k ec et eg) ss =
  ŝR ec (fold-≅U sE HE et ss) (λ η e η′ e′ eη → fold-≅U sE HE (eg η e η′ e′ eη) ss)
fold-≅U sE HE (ĉ≅ ec dt dg eo eO) ss =
  ĉR ec dt dg (fold-≅U sE HE eo ss) (λ η e η′ e′ eη → fold-≅U sE HE (eO η e η′ e′ eη) ss)
```

## §3 观测

```agda
data Obs : Ordᴵ → Set where
  idO  : Obs zero
  fo   : ∀ {i k ℓ fl} (φ : Flr) → Obs i → (P : Run fl) → (cv : ∀ {L} → Ev L φ → Simᴵ k L) → Ev ℓ (fl ⊔ φ) → i <ᴵ ℓ → Obs k
  fo1  : ∀ {d i k ℓ flE} → Obs i → (E : Fr (suc d) flE) → (Q : Sp (suc d)) → Ev ℓ (sf Q ⊔ (flE ⊔ flo k)) → i <ᴵ ℓ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordˢ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

run : ∀ {k} → Obs k → Ordˢ k → Ordˢ zero
run idO              x = x
run (fo φ O P cv ev p) x = run O (fold 0 φ cv P x ev p)
run (fo1 {k = k} O E Q ev p) x = run O (fold1 (flo k) (cvFlo k) E x Q ev p)
run (addo O a σ)     x = run O (addˢ a σ x)
run (tro O e)        x = run O (trˢ e x)
run (tr⁻o O e)       x = run O (tr⁻ˢ e x)

infix 4 _≈ᵒ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set where
  idO  : idO ≈ᵒ idO
  fo   : ∀ {i k k′ ℓ ℓ′ fl φ φ′} {O O′ : Obs i} {P : Run fl}
         {cv : ∀ {L} → Ev L φ → Simᴵ k L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k′ L}
         {ev : Ev ℓ (fl ⊔ φ)} {ev′ : Ev ℓ′ (fl ⊔ φ′)} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} →
         O ≈ᵒ O′ → P ≈ᴿ P → fo φ O P cv ev p ≈ᵒ fo φ′ O′ P cv′ ev′ p′
  fo1  : ∀ {d i k k′ ℓ ℓ′ flE} {O O′ : Obs i} {E : Fr (suc d) flE} {Q : Sp (suc d)}
         {ev : Ev ℓ (sf Q ⊔ (flE ⊔ flo k))} {ev′ : Ev ℓ′ (sf Q ⊔ (flE ⊔ flo k′))} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} →
         O ≈ᵒ O′ → E ≈U E → Q ≈S Q → fo1 {k = k} O E Q ev p ≈ᵒ fo1 {k = k′} O′ E Q ev′ p′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordˢ ℓ} {a′ : Ordˢ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → ℓ ≅ᴵ ℓ′ → a ≅ˢ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′
  tro  : ∀ {a a′ b b′} {O : Obs b} {O′ : Obs b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} → O ≈ᵒ O′ → tro O e ≈ᵒ tro O′ e′
  tr⁻o : ∀ {a a′ b b′} {O : Obs a} {O′ : Obs a′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} → O ≈ᵒ O′ → tr⁻o O e ≈ᵒ tr⁻o O′ e′

≈ᵒ-reflˡ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O ≈ᵒ O
≈ᵒ-reflˡ idO          = idO
≈ᵒ-reflˡ (fo o r)     = fo (≈ᵒ-reflˡ o) r
≈ᵒ-reflˡ (fo1 o rE rQ) = fo1 (≈ᵒ-reflˡ o) rE rQ
≈ᵒ-reflˡ (addo o k e) = addo (≈ᵒ-reflˡ o) (≅ᴵ-refl _) (≅ˢ-reflˡ e)
≈ᵒ-reflˡ (tro o)      = tro (≈ᵒ-reflˡ o)
≈ᵒ-reflˡ (tr⁻o o)     = tr⁻o (≈ᵒ-reflˡ o)

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᵒ-reflʳ idO          = idO
≈ᵒ-reflʳ (fo o r)     = fo (≈ᵒ-reflʳ o) r
≈ᵒ-reflʳ (fo1 o rE rQ) = fo1 (≈ᵒ-reflʳ o) rE rQ
≈ᵒ-reflʳ (addo o k e) = addo (≈ᵒ-reflʳ o) (≅ᴵ-refl _) (≅ˢ-reflʳ e)
≈ᵒ-reflʳ (tro o)      = tro (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (tr⁻o o)     = tr⁻o (≈ᵒ-reflʳ o)

run-≅ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordˢ k} {x′ : Ordˢ k′} → O ≈ᵒ O′ → x ≅ˢ x′ → run O x ≅ˢ run O′ x′
run-≅ idO          d = d
run-≅ (fo o r)     d = run-≅ o (fold-≅0 r d _ _ _ _ (≅ᴵ-refl _))
run-≅ (fo1 {k = k} {k′ = k′} {flE = flE} o rE rQ) d = run-≅ o (fold-≅U {cv = cvFlo k} {cv′ = cvFlo k′} (∼ᶠ-refl flE) rE d rQ _ _ _ _ (≅ᴵ-refl _))
run-≅ (addo o k a) d = run-≅ o (addˢ-≅ k a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (trˢ-≅ e (≅-trˢ e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻ˢ-≅ e (≅-tr⁻ˢ e′ d))

r∅ : ∅ᴿ ≈ᴿ ∅ᴿ
r∅ ev p ev′ p′ ei = Ωˢ-≅ ei

rΩ̂ : ∀ {fl} {P : Run fl} → P ≈ᴿ P → Ω̂A 0 P ≈ᴿ Ω̂A 0 P
rΩ̂ {fl} {P} r =
  cloR {t = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
       {t′ = fold 0 (fk zero) (λ e → e) P (Ωˢ (suc zero))} {g′ = λ η → fold 0 (fk η) (λ e q → e (suc q)) P (Ωˢ η)}
       (∼ᶠ-refl fl)
       (fold-≅0 {φ = fk zero} {φ′ = fk zero} {cv = λ e → e} {cv′ = λ e → e} {P = P} {P′ = P} r (Ωˢ-refl (suc zero)))
       (λ η η′ eη → fold-≅0 {φ = fk η} {φ′ = fk η′} {cv = λ e q → e (suc q)} {cv′ = λ e q → e (suc q)} {P = P} {P′ = P} r (Ωˢ-≅ eη))
```
