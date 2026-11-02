# 深度 1 的观测 (一): `Obs` 加 `fo1`

> 接 [UniformNF3Eq](UniformNF3Eq.lagda.md), [UniformNF3Base](UniformNF3Base.lagda.md) §1. 结论先说:
>
> 1. **`fo1 O E Q ev p`: 以帧 $E$、前缀 $Q$ 在目标 $i$ 处观测尾巴, 地板取尾巴层号的紧地板 `flo k`.** `run` 是 `fold 1 (flo k) (cvFlo k) E x Q ev p`.
> 2. **`run-≅` 对一切相关尾巴成立**, 没有 `AlignD`: 对齐条件已经在 `≅ˢ` 的后继行里 ([UniformNF3Eq](UniformNF3Eq.lagda.md) §3). UniformNFBase §1 记下的阻塞在这里解除.
> 3. 相似的两个 `fo1` 同一帧、同一前缀, 帧与前缀都带自互模拟.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D1O where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ;
  Ωˢ; addˢ; _+ˢ_; Goodᶻ; force; force-HS; z<suc)
open Restrˢ
open import OCF.Align.UniformNF3Eq using (fold-≅1; _≈₁_; kd; kd-≅; ≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; ≅ᶻ-trans; force-≅; Goodᶻ-tr;
  _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; Rˢ; R→≅ˢ; ≅→Rˢ; R-convˢ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ;
  trˢ-≅; tr⁻ˢ-≅; backˢ-≅; back⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; tf; addˢ-≅;
  s-invˢ; l-invˢ; i-respˢ; u-invˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ; ĉ-reflg; ≅ᶻ-refl₀; ≅ᶻ-reflg; ĉ-reflO;
  two; Lv; Lv-refl; Lv-up; 𝟎ˢ)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; InF; ink; inl; inr; liftEv; Run; A; wk; limA; limᵢA; ŝA; ĉA; Top; top; bound; Bd; sb; nz; ubd; Fc; evF; iF; FM; MF; FB; cloA; flo; cvFlo; toFlo; repA; fold; Ω̂A; ∅ᴿ; chainA; _∼ᶠ_; ∼ᶠ-refl; ≺0)
open import OCF.Align.UniformNF3Eq using (_≈₁_; _≈ᴿ_; fold-≅0; cloR)
```

## §1 观测

```agda
data Obs : Ordᴵ → Set where
  idO  : Obs zero
  fo   : ∀ {i k ℓ fl} (φ : Flr) → Obs i → (P : Run fl) → (cv : ∀ {L} → Ev L φ → Simᴵ k L) → Ev ℓ (fl ⊔ φ) → i <ᴵ ℓ → Obs k
  fo1  : ∀ {i k ℓ fl flE} → Obs i → (E : A 1 flE) → (Q : Run fl) → Ev ℓ (fl ⊔ (flE ⊔ flo k)) → i <ᴵ ℓ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordˢ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

run : ∀ {k} → Obs k → Ordˢ k → Ordˢ zero
run idO              x = x
run (fo φ O P cv ev p) x = run O (fold 0 φ cv P x ev p)
run (fo1 {k = k} O E Q ev p) x = run O (fold 1 (flo k) (cvFlo k) E x Q ev p)
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
  fo1  : ∀ {i k k′ ℓ ℓ′ fl flE} {O O′ : Obs i} {E : A 1 flE} {Q : Run fl}
         {ev : Ev ℓ (fl ⊔ (flE ⊔ flo k))} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo k′))} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} →
         O ≈ᵒ O′ → E ≈₁ E → Q ≈ᴿ Q → fo1 {k = k} O E Q ev p ≈ᵒ fo1 {k = k′} O′ E Q ev′ p′
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
run-≅ (fo1 {k = k} {k′ = k′} {fl = fl} {flE = flE} o rE rQ) d = run-≅ o (fold-≅1 {cv = cvFlo k} {cv′ = cvFlo k′} (∼ᶠ-refl flE) rE d (∼ᶠ-refl fl) rQ _ _ _ _ (≅ᴵ-refl _))
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
