# 原底行的全层 typed 读取

先保留原 tl、ψ̄ 与全部不可数反馈，建立异族读取。关系来自已有的
Ordˢ/Ordᶜ 桥；这里只新增其对原 Ladder 实际读取的保持，而非把原程序
改写成另一个解释器。两个派发均在各自原 source 公共界内进行。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseRead (𝕊 : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; subst₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ; intoˢ; out-intoˢ; Ωˢ; toZ; tr⁻ˢ)
open import OCF.Free.Floor using (Flr; Ev; flo; cvFlo; toFlo)
open import OCF.Align.OrdLabZLevel using (ψ; Ω; tr⁻; iter-R; clash₁; clash₂)
open import OCF.Align.OrdLabZPrefix using
  (_~_; z~; s~; l~; lᵢ~; upˡ; upʳ; Ω~; add~; Rh→~; ~→Rh; tr⁻ˢ-~; ~-tr⁻)
open import OCF.Align.LadderOrdTree 𝕊

read-related : ∀ {m c φ χ w i i′ k ℓ k′ ℓ′}
  {cv : ∀ {L} → Ev L φ → Simᴵ k L}
  {a : Ordˢ k} {b : Ordᶜ k′}
  (ok : Ok w) (env : Eh h₀ m w χ)
  (ev : Ev ℓ φ) (p : i <ᴵ ℓ)
  {p′ : i′ <ᴵ ℓ′} {σ′ : Simᴵ k′ ℓ′} →
  i ≅ᴵ i′ → a ~ b →
  ψ̄ᵠ ok env (tl {m = m} {c = c} {χ = χ} φ cv a) ev p ~ ψ p′ σ′ b
read-related ok env ev p ei z~ = Ω~ ei
read-related ok env ev p ei (s~ d) =
  l~ (iter-R _~_ (λ d′ → add~ (read-related ok env ev p ei d) d′) z~)
read-related ok env ev p ei (l~ h) = l~ (λ n → read-related ok env ev p ei (h n))
read-related {k = suc k} {cv = cv} ok env ev p ei (upˡ {r = zero} d) =
  read-related ok env (toFlo k (λ q → cv ev (suc q))) p ei d
read-related {k = lim f st} {cv = cv} ok env ev p ei (upˡ {r = self n} d) =
  read-related ok env (toFlo (f n) (λ q → cv ev (lim n q))) p ei d
read-related ok env ev p ei (upʳ {r = zero} d) = read-related ok env ev p ei d
read-related ok env ev p ei (upʳ {r = self n} d) = read-related ok env ev p ei d
read-related {cv = cv} ok env ev p {p′} {σ′} ei
  (lᵢ~ {p = q} {q = q′} {f = f} {g = g} ej h)
  with <ᴵ-dec (cv ev q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) =
  lᵢ~ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans ej e₂)) λ x y d →
    subst₂ (λ u v → ψ̄ᵠ ok env (tl _ cv (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u)))) ev p ~ ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₂ v))))
      (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-into (<→◃ r₂) y))
      (read-related ok env ev p ei
        (h _ _ (~→Rh (<→◃ q) (tr⁻ˢ-~ e₁ (~-tr⁻ e₂ (Rh→~ (<→◃ r₁) d))))))
... | injᵃ r | injᵇ s = ⊥-elim (clash₁ ej ei r s)
... | injᵃ r | injᶜ e = ⊥-elim (clash₂ ej ei r e)
... | injᵇ s | injᵃ r = ⊥-elim (clash₁ (≅ᴵ-sym ej) (≅ᴵ-sym ei) r s)
... | injᶜ e | injᵃ r = ⊥-elim (clash₂ (≅ᴵ-sym ej) (≅ᴵ-sym ei) r e)
... | injᵇ _ | injᵇ _ = l~ (λ n → read-related ok env ev p ei (h _ _ (~→Rh (<→◃ q) (linked n))))
  where linked = iter-R _~_ (λ d → read-related ok env ev (cv ev q) ej (h _ _ (~→Rh (<→◃ q) d))) (Ω~ ej)
... | injᵇ _ | injᶜ _ = l~ (λ n → read-related ok env ev p ei (h _ _ (~→Rh (<→◃ q) (linked n))))
  where linked = iter-R _~_ (λ d → read-related ok env ev (cv ev q) ej (h _ _ (~→Rh (<→◃ q) d))) (Ω~ ej)
... | injᶜ _ | injᵇ _ = l~ (λ n → read-related ok env ev p ei (h _ _ (~→Rh (<→◃ q) (linked n))))
  where linked = iter-R _~_ (λ d → read-related ok env ev (cv ev q) ej (h _ _ (~→Rh (<→◃ q) d))) (Ω~ ej)
... | injᶜ _ | injᶜ _ = l~ (λ n → read-related ok env ev p ei (h _ _ (~→Rh (<→◃ q) (linked n))))
  where linked = iter-R _~_ (λ d → read-related ok env ev (cv ev q) ej (h _ _ (~→Rh (<→◃ q) d))) (Ω~ ej)
```

原底行全部层号的实例；m、c、环境和实际目标均保留。

```agda
omega-read : ∀ {m c φ χ w i ℓ η}
  (cv : ∀ {L} → Ev L φ → Simᴵ η L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : i <ᴵ ℓ) →
  ψ̄ᵠ ok env (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ η)) ev p ~
    ψ p (cv ev) (Ω η)
omega-read cv ok env ev p = read-related ok env ev p (≅ᴵ-refl _) (Ω~ (≅ᴵ-refl _))
```

此定理保留每个旧 Ω 的实际坐标和全部无累加反馈，不将回调视为对
任意同形坐标自动相容。相容性正是源关系 lᵢ~ 的异坐标字段。
