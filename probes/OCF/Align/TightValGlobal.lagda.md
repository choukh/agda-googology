# 紧界树比值 (六): `TΩ2′ˢ` 没有证书

> [TightVal](TightVal.lagda.md) 的第六篇. [TightValNeg](TightValNeg.lagda.md) 的否定只在具体环境上. 本文给 `ψᵉ′` 一条层对齐的互模拟 (`ψᵉ′-≅ᴬ`, 两侧指数的层号 $\cong^\mathsf I$, 第 $\ge2$ 层也成立), 把否定搬到一切环境 (`no-Ω₃-any`), 再沿 $\psi_0(\psi_\Omega(\Omega_1))$ 的标签走到 $\Omega_3$.
>
> **`no-T : Goodᴺ (toZ TΩ2′ˢ) → ⊥`: 紧界树没有证书. 占位 $0$ 的后果不是值小, 是这棵树在 $\Omega_3$ 处就不是合法的树.** [TightValCap](TightValCap.lagda.md) 的 `cap-T` 所以在 `TΩ2′ˢ` 上是空真的; 非空的是 `capΩ` 的机制, 对单调的占位见 [TightValPh](TightValPh.lagda.md).
>
> `ψᵉ′-≅` (OmegaSqBase) 只对第 $\le1$ 层, 因为 $\cong^\mathsf s$ 允许 "第 2 层的字面后继" 对 "第 1 层的后继经 `up`", 那时一边是占位, 一边是真帧. 换成 $\cong^\mathsf A$ (成对的 `up`) 再加 $k_1\cong^\mathsf I k_2$, 这种对就不出现了.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. §3 读标签: 用它确定第一个链点的形状.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightValGlobal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; tr⁻ˢ; z<suc; z1)
open import OCF.Align.EBO using (T; fsn; natT)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅)
open import OCF.Align.UniformS using (_≅ᶻ_; toZ-≅; kd-≅; tf; Ωˢ-refl)
open import OCF.Align.GoodLBase using (Goodᴸ; forceᴸ)
open import OCF.Align.NotFree using (Goodᴺ; gc; gl; forceᴺ; forceᴺ-≅; ofL; ofL-≅)
open import OCF.Align.OmegaExpBase using (Stk; ψˢ; ∅ˢ; _▹Ω̂; Good∅; hR)
open import OCF.Align.OmegaExp using (tΩ1)
open import OCF.Align.OmegaSqBase using (ψᵉ′; repᴷ; _▹[_]_; s₀; ψᵉ′-≅; lo1; z3)
open import OCF.Align.OmegaSq using (TΩ2′ˢ; t₀′; gΩ; GLΩ0′)
open import OCF.Align.UniformNF3D3N using (Goodᴺ-tr)
open import OCF.Align.Symbolic using (σ1)
open import OCF.Align.Relative using (_≅ᴬ_; zᴬ; sᴬ; lᴬ; lᵢᴬ; uᴬ; uz; us; ŝᴬ; ĉᴬ; Rᴬ; R→≅ᴬ; ≅→Rᴬ; R-convᴬ; addˢ-≅ᴬ; tr⁻ˢ-≅ᴬ; ≅ᴬ-tr⁻ˢ; Ωˢ-≅ᴬ; ≅ᴬ→≅ˢ₀)
open import OCF.Align.TightValNeg using (four; z4; F₃; no-Ω₃)
```

## §1 `ψˢ` 与 `ψᵉ′` 尊重 $\cong^\mathsf A$

```agda
infix 4 _≈ᵃ_
_≈ᵃ_ : Stk → Stk → Set
S ≈ᵃ S′ = ∀ {i i′ ℓ ℓ′} (z : zero <ᴵ ℓ) (p : i <ᴵ ℓ) (z′ : zero <ᴵ ℓ′) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → S z p ≅ᴬ S′ z′ p′

liSᴬ : ∀ {S S′ : Stk} {i i′ k₁ ℓ₁ k₂ ℓ₂ j j′} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
       {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
       {q : j <ᴵ k₁} {q′ : j′ <ᴵ k₂} {f : Uˢ j (<→◃ q) → Ordˢ k₁} {g : Uˢ j′ (<→◃ q′) → Ordˢ k₂} →
       i ≅ᴵ i′ → j ≅ᴵ j′ →
       (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rᴬ j (<→◃ q) (intoˢ (<→◃ q) x) y →
          ψˢ S z p σ (f (intoˢ (<→◃ q) x)) ≅ᴬ ψˢ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) y))) →
       (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rᴬ j (<→◃ q) (intoˢ (<→◃ q) x) y →
          ψˢ S z (σ q) σ (f (intoˢ (<→◃ q) x)) ≅ᴬ ψˢ S′ z′ (σ′ q′) σ′ (g (intoˢ (<→◃ q′) y))) →
       ψˢ S z p σ (Ord₊ˢ.limᵢ q f) ≅ᴬ ψˢ S′ z′ p′ σ′ (Ord₊ˢ.limᵢ q′ g)
liSᴬ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e rec recC
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψˢ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ᴬ ψˢ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (rec _ _ (≅→Rᴬ (<→◃ q) (tr⁻ˢ-≅ᴬ e₁ (≅ᴬ-tr⁻ˢ e₂ (R→≅ᴬ (<→◃ r₁) d)))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
  where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
... | injᵇ _ | injᶜ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
  where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
... | injᶜ _ | injᵇ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
  where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
... | injᶜ _ | injᶜ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
  where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)

ψˢ-≅ᴬ : ∀ {S S′ : Stk} → S ≈ᵃ S′ → ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
        {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ k₁} {b : Ordˢ k₂} →
        i ≅ᴵ i′ → a ≅ᴬ b → ψˢ S z p σ a ≅ᴬ ψˢ S′ z′ p′ σ′ b
ψˢ-≅ᴬ H {z = z} {p = p} {z′ = z′} {p′ = p′} ei zᴬ = H z p z′ p′ ei
ψˢ-≅ᴬ H ei (sᴬ e) = lᴬ (iter-R _≅ᴬ_ (λ e′ → addˢ-≅ᴬ (kd-≅ ei) (ψˢ-≅ᴬ H ei e) e′) zᴬ)
ψˢ-≅ᴬ H ei (lᴬ h) = lᴬ (λ n → ψˢ-≅ᴬ H ei (h n))
ψˢ-≅ᴬ H ei (uᴬ uz e)     = ψˢ-≅ᴬ H ei e
ψˢ-≅ᴬ H ei (uᴬ (us m) e) = ψˢ-≅ᴬ H ei e
ψˢ-≅ᴬ H {k₁ = zero}    {k₂ = zero}    ei (ŝᴬ k ec et eg) =
  ĉᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (ψˢ-≅ᴬ H ei et) (λ η e η′ e′ eη → ψˢ-≅ᴬ H ei (eg η e η′ e′ eη))
ψˢ-≅ᴬ H {k₁ = zero}    {k₂ = suc _}   ei (ŝᴬ k ec et eg) = ⊥-elim (tf k)
ψˢ-≅ᴬ H {k₁ = zero}    {k₂ = lim _ _} ei (ŝᴬ k ec et eg) = ⊥-elim (tf k)
ψˢ-≅ᴬ H {k₁ = suc _}   {k₂ = zero}    ei (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
ψˢ-≅ᴬ H {k₁ = lim _ _} {k₂ = zero}    ei (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
ψˢ-≅ᴬ H {k₁ = suc _}   {k₂ = suc _}   ei (ŝᴬ k ec et eg) =
  ŝᴬ (kd-≅ ei) ec (ψˢ-≅ᴬ H ei et) (λ η e η′ e′ eη → ψˢ-≅ᴬ H ei (eg η e η′ e′ eη))
ψˢ-≅ᴬ H {k₁ = suc _}   {k₂ = lim _ _} ei (ŝᴬ k ec et eg) =
  ŝᴬ (kd-≅ ei) ec (ψˢ-≅ᴬ H ei et) (λ η e η′ e′ eη → ψˢ-≅ᴬ H ei (eg η e η′ e′ eη))
ψˢ-≅ᴬ H {k₁ = lim _ _} {k₂ = suc _}   ei (ŝᴬ k ec et eg) =
  ŝᴬ (kd-≅ ei) ec (ψˢ-≅ᴬ H ei et) (λ η e η′ e′ eη → ψˢ-≅ᴬ H ei (eg η e η′ e′ eη))
ψˢ-≅ᴬ H {k₁ = lim _ _} {k₂ = lim _ _} ei (ŝᴬ k ec et eg) =
  ŝᴬ (kd-≅ ei) ec (ψˢ-≅ᴬ H ei et) (λ η e η′ e′ eη → ψˢ-≅ᴬ H ei (eg η e η′ e′ eη))
ψˢ-≅ᴬ H ei (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (ψˢ-≅ᴬ H ei eo) (λ η e η′ e′ eη → ψˢ-≅ᴬ H ei (eO η e η′ e′ eη))
ψˢ-≅ᴬ {S = S} {S′ = S′} H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ei (lᵢᴬ {p = q} {q = q′} {f = f} {g = g} e h) =
  liSᴬ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e
       (λ x y d → ψˢ-≅ᴬ H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ei (h x y d))
       (λ x y d → ψˢ-≅ᴬ H {z = z} {p = σ q} {σ = σ} {z′ = z′} {p′ = σ′ q′} {σ′ = σ′} e (h x y d))

∅-≈ᵃ : ∅ˢ ≈ᵃ ∅ˢ
∅-≈ᵃ z p z′ p′ ei = Ωˢ-≅ᴬ ei

▹Ω̂-≈ᵃ : ∀ {S S′ : Stk} → S ≈ᵃ S′ → (S ▹Ω̂) ≈ᵃ (S′ ▹Ω̂)
▹Ω̂-≈ᵃ H z p z′ p′ ei = ŝᴬ (kd-≅ ei) (s≅ ei) (ψˢ-≅ᴬ H ei (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero)))) (λ η e η′ e′ eη → ψˢ-≅ᴬ H ei (Ωˢ-≅ᴬ eη))

liEᴬ : ∀ {S S′ : Stk} {i i′ k₁ ℓ₁ k₂ ℓ₂ j j′} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
       {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
       {q : j <ᴵ k₁} {q′ : j′ <ᴵ k₂} {f : Uˢ j (<→◃ q) → Ordˢ k₁} {g : Uˢ j′ (<→◃ q′) → Ordˢ k₂} →
       i ≅ᴵ i′ → j ≅ᴵ j′ →
       (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rᴬ j (<→◃ q) (intoˢ (<→◃ q) x) y →
          ψᵉ′ S z p σ (f (intoˢ (<→◃ q) x)) ≅ᴬ ψᵉ′ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) y))) →
       (∀ (x : Ordˢ j) (y : Ordˢ j′) → Rᴬ j (<→◃ q) (intoˢ (<→◃ q) x) y →
          ψᵉ′ S z (σ q) σ (f (intoˢ (<→◃ q) x)) ≅ᴬ ψᵉ′ S′ z′ (σ′ q′) σ′ (g (intoˢ (<→◃ q′) y))) →
       ψᵉ′ S z p σ (Ord₊ˢ.limᵢ q f) ≅ᴬ ψᵉ′ S′ z′ p′ σ′ (Ord₊ˢ.limᵢ q′ g)
liEᴬ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e rec recC
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψᵉ′ S z p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ≅ᴬ ψᵉ′ S′ z′ p′ σ′ (g (intoˢ (<→◃ q′) (tr⁻ˢ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (rec _ _ (≅→Rᴬ (<→◃ q) (tr⁻ˢ-≅ᴬ e₁ (≅ᴬ-tr⁻ˢ e₂ (R→≅ᴬ (<→◃ r₁) d)))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
  where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
... | injᵇ _ | injᶜ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
  where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
... | injᶜ _ | injᵇ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
  where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)
... | injᶜ _ | injᶜ _  = lᴬ (λ m → rec _ _ (≅→Rᴬ (<→◃ q) (chain m)))
  where chain = iter-R _≅ᴬ_ (λ d → recC _ _ (≅→Rᴬ (<→◃ q) d)) (Ωˢ-≅ᴬ e)

ψᵉ′-≅ᴬ : ∀ {S S′ : Stk} → S ≈ᵃ S′ → ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {z : zero <ᴵ ℓ₁} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁}
         {z′ : zero <ᴵ ℓ₂} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ k₁} {b : Ordˢ k₂} →
         k₁ ≅ᴵ k₂ → i ≅ᴵ i′ → a ≅ᴬ b → ψᵉ′ S z p σ a ≅ᴬ ψᵉ′ S′ z′ p′ σ′ b
repᴷ-≈ᵃ : ∀ {S S′ : Stk} → S ≈ᵃ S′ → ∀ {k₁ k₂} {s : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k₁ ℓ} {s′ : ∀ {ℓ} → zero <ᴵ ℓ → Simᴵ k₂ ℓ}
          {a : Ordˢ k₁} {b : Ordˢ k₂} → k₁ ≅ᴵ k₂ → a ≅ᴬ b → ∀ m → repᴷ S s a m ≈ᵃ repᴷ S′ s′ b m

ψᵉ′-≅ᴬ H {z = z} {p = p} {z′ = z′} {p′ = p′} ek ei zᴬ = ▹Ω̂-≈ᵃ H z p z′ p′ ei
ψᵉ′-≅ᴬ H {z = z} {p = p} {z′ = z′} {p′ = p′} z≅ ei (sᴬ e) = lᴬ (λ m → repᴷ-≈ᵃ H z≅ e m z p z′ p′ ei)
ψᵉ′-≅ᴬ H {z = z} {p = p} {z′ = z′} {p′ = p′} (s≅ z≅) ei (sᴬ e) = lᴬ (λ m → repᴷ-≈ᵃ H (s≅ z≅) e m z p z′ p′ ei)
ψᵉ′-≅ᴬ H (s≅ (s≅ _)) ei (sᴬ e) = zᴬ
ψᵉ′-≅ᴬ H (s≅ (l≅ _)) ei (sᴬ e) = zᴬ
ψᵉ′-≅ᴬ H (l≅ _) ei (sᴬ e) = zᴬ
ψᵉ′-≅ᴬ H ek ei (lᴬ h) = lᴬ (λ n → ψᵉ′-≅ᴬ H ek ei (h n))
ψᵉ′-≅ᴬ H (s≅ ek) ei (uᴬ uz e) = ψᵉ′-≅ᴬ H ek ei e
ψᵉ′-≅ᴬ H (l≅ h) ei (uᴬ (us m) e) = ψᵉ′-≅ᴬ H (h m) ei e
ψᵉ′-≅ᴬ H z≅ ei (ŝᴬ k ec et eg) =
  ĉᴬ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (ψᵉ′-≅ᴬ H z≅ ei et) (λ η e η′ e′ eη → ψᵉ′-≅ᴬ H z≅ ei (eg η e η′ e′ eη))
ψᵉ′-≅ᴬ H (s≅ ek) ei (ŝᴬ k ec et eg) =
  ŝᴬ (kd-≅ ei) ec (ψᵉ′-≅ᴬ H (s≅ ek) ei et) (λ η e η′ e′ eη → ψᵉ′-≅ᴬ H (s≅ ek) ei (eg η e η′ e′ eη))
ψᵉ′-≅ᴬ H (l≅ h) ei (ŝᴬ k ec et eg) =
  ŝᴬ (kd-≅ ei) ec (ψᵉ′-≅ᴬ H (l≅ h) ei et) (λ η e η′ e′ eη → ψᵉ′-≅ᴬ H (l≅ h) ei (eg η e η′ e′ eη))
ψᵉ′-≅ᴬ H ek ei (ĉᴬ ec dt dg eo eO) = ĉᴬ ec dt dg (ψᵉ′-≅ᴬ H ek ei eo) (λ η e η′ e′ eη → ψᵉ′-≅ᴬ H ek ei (eO η e η′ e′ eη))
ψᵉ′-≅ᴬ {S = S} {S′ = S′} H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ek ei (lᵢᴬ {p = q} {q = q′} {f = f} {g = g} e h) =
  liEᴬ {S = S} {S′ = S′} {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} {q = q} {q′ = q′} {f = f} {g = g} ei e
       (λ x y d → ψᵉ′-≅ᴬ H {z = z} {p = p} {σ = σ} {z′ = z′} {p′ = p′} {σ′ = σ′} ek ei (h x y d))
       (λ x y d → ψᵉ′-≅ᴬ H {z = z} {p = σ q} {σ = σ} {z′ = z′} {p′ = σ′ q′} {σ′ = σ′} ek e (h x y d))

repᴷ-≈ᵃ H ek e zero    = H
repᴷ-≈ᵃ H ek e (suc m) z p z′ p′ ei = ψᵉ′-≅ᴬ (repᴷ-≈ᵃ H ek e m) ek ei e
```

## §2 一切环境

```agda
three′ : Ordᴵ
three′ = suc (suc (suc zero))

no-Ω₃-any : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ three′ ℓ) → Goodᴺ (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ three′))) → ⊥
no-Ω₃-any z p σ G = no-Ω₃ (Goodᴺ-tr (toZ-≅ (≅ᴬ→≅ˢ₀ (ψᵉ′-≅ᴬ ∅-≈ᵃ {z = z} {p = p} {σ = σ} {z′ = z4} {p′ = z4} {σ′ = λ q → suc q} (≅ᴵ-refl three′) z≅ (Ωˢ-≅ᴬ (≅ᴵ-refl three′))))) G)
```

## §3 沿标签到 $\Omega_3$

`TΩ2′ˢ` 的第一个链点带标签 $\theta_1=\psi_0(\psi_\Omega(\Omega_1))$. 沿 $[0,1,0,0,3]$ 它到自然数 $3$, 所以它的层号沿同一路到字面的 $3$, 分支 $\Omega_{L}$ 沿同一路到 $\Omega_3$. 路径的前四步与 `OmegaSqA.Refute` 相同, 只是最后一步取 $[3]$.

```agda
θ : T
θ = tΩ1

Bad : (Y : Ordᶜ zero) → HS Y → Set
Bad Y hY = ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (toLevel Y hY) ℓ) → Goodᴺ (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ (toLevel Y hY)))) → ⊥

nat0 : ∀ {Y} → Lab Y (natT 0) → Y ≅ natᶜ 0
nat0 (l0 c e) = e
nat0 (l1 () e l)
nat0 (lω () e h)

nat1 : ∀ {Y} → Lab Y (natT 1) → Y ≅ natᶜ 1
nat1 (l0 () e)
nat1 (l1 c e l) = ≅-trans e (s≅ (nat0 l))
nat1 (lω () e h)

nat2 : ∀ {Y} → Lab Y (natT 2) → Y ≅ natᶜ 2
nat2 (l0 () e)
nat2 (l1 c e l) = ≅-trans e (s≅ (nat1 l))
nat2 (lω () e h)

nat3 : ∀ {Y} → Lab Y (natT 3) → Y ≅ natᶜ 3
nat3 (l0 () e)
nat3 (l1 c e l) = ≅-trans e (s≅ (nat2 l))
nat3 (lω () e h)

leaf : ∀ Y hY → Y ≅ natᶜ 3 → Bad Y hY
leaf .(Ord₊.suc (Ord₊.suc (Ord₊.suc Ord₊.zero))) hY (s≅ (s≅ (s≅ z≅))) z p σ G = no-Ω₃-any z p σ G

step₄ : ∀ Y hY → Lab Y (fsn (fsn (fsn (fsn θ 0) 1) 0) 0) → Bad Y hY
step₄ Y hY (l0 () e)
step₄ Y hY (l1 () e l)
step₄ (Ord₊.lim F) hY (lω c (l≅ k) h) z p σ (gl G st) =
  leaf (F 3) (hl₁ hY 3) (nat3 (Lab-≅ (k 3) (h 3))) z p (λ q → σ (lim 3 q)) (G 3)

step₃ : ∀ Y hY → Lab Y (fsn (fsn (fsn θ 0) 1) 0) → Bad Y hY
step₃ Y hY (l0 () e)
step₃ Y hY (l1 () e l)
step₃ (Ord₊.lim F) hY (lω c (l≅ k) h) z p σ (gl G st) =
  step₄ (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) z p (λ q → σ (lim 0 q)) (G 0)

step₂ : ∀ Y hY → Lab Y (fsn (fsn θ 0) 1) → Bad Y hY
step₂ Y hY (l0 () e)
step₂ Y hY (l1 () e l)
step₂ (Ord₊.lim F) hY (lω c (l≅ k) h) z p σ (gl G st) =
  step₃ (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) z p (λ q → σ (lim 0 q)) (G 0)

step₁ : ∀ Y hY → Lab Y (fsn θ 0) → Bad Y hY
step₁ Y hY (l0 () e)
step₁ Y hY (l1 () e l)
step₁ (Ord₊.lim F) hY (lω c (l≅ k) h) z p σ (gl G st) =
  step₂ (F 1) (hl₁ hY 1) (Lab-≅ (k 1) (h 1)) z p (λ q → σ (lim 1 q)) (G 1)

step₀ : ∀ Y hY → Lab Y θ → Bad Y hY
step₀ Y hY (l0 () e)
step₀ Y hY (l1 () e l)
step₀ (Ord₊.lim F) hY (lω c (l≅ k) h) z p σ (gl G st) =
  step₁ (F 0) (hl₁ hY 0) (Lab-≅ (k 0) (h 0)) z p (λ q → σ (lim 0 q)) (G 0)

rt₀ : toZ t₀′ ≅ᶻ toZ t₀′
rt₀ = toZ-≅ (ψᵉ′-≅ (hR Good∅) {z = z<suc z1 z1} {p = zero} {σ = σ1 (z<suc z1 z1)} {z′ = z<suc z1 z1} {p′ = zero} {σ′ = σ1 (z<suc z1 z1)} lo1 lo1 (≅ᴵ-refl zero) (Ωˢ-refl (suc zero)))

no-T : Goodᴺ (toZ TΩ2′ˢ) → ⊥
no-T (gc ys hy dy G₀ l₀ Gg lE Go₀ Go mo₀ mo) =
  step₀ (ys 0) (hy 0) lY _ _ _ (Go 0)
  where
  lY : Lab (ys 0) θ
  lY = Lab-≅ (≅-trans (≅-sym l₀) (≅-trans (forceᴺ-≅ rt₀ G₀ (ofL (proj₁ GLΩ0′))) (ofL-≅ (proj₁ GLΩ0′)))) (proj₂ GLΩ0′)
```

**读法.** `no-T` 的陈述不提标签; 标签只在证明里确定 `ys 0` 的形状. 它不否定紧界设计的其他写法, 只否定这棵树: 占位是 $0$ 的 `ψᵉ′` 上的 `TΩ2′ˢ`.
