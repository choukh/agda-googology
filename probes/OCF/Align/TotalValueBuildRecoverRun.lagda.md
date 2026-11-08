# 顶 Ω 回收与原反馈链同步

本篇只消费 Cross 显式相关回调。比较均在各侧原源界中；
不同 <ᴵ-dec 代表元通过原层同构搬坐标，不假其证明相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRecoverRun (𝕊 : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ; intoˢ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ᶻ_; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound; bound-≅; evF)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Free.Base using (clash; r∅)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open RestrQ
open import OCF.Free.Eq using (_≅ˢ_)

open import OCF.Align.TotalValueBuildRecoverIf 𝕊

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

ht-eq : DecidableEquality Ht
ht-eq a b with tri a b
... | tlt p = no (λ eq → irr (subst (a <ᴸ_) (sym eq) p))
... | teq eq = yes eq
... | tgt p = no (λ eq → irr (subst (_<ᴸ a) (sym eq) p))

tri-self : ∀ m → tri m m ≡ teq refl
tri-self m with tri m m
... | tlt p = ⊥-elim (irr p)
... | tgt p = ⊥-elim (irr p)
... | teq eq = cong teq (Decidable⇒UIP.≡-irrelevant ht-eq eq refl)

recover : ∀ {m m′ a b t t′ φ χ ψ ρ w} (δ : m <ᴸ m′)
  (q : t <ᴵ a) (ok : Ok w) (e : Eh m m′ w ρ) (p : t′ <ᴵ w m) → t ≅ᴵ t′ →
  {x : Q m a φ χ} {y : Q m′ b ψ ρ} → Cross δ a b x y →
  Rq m t t′ (ψᵠ q x) (Ψ δ ok e p y)

chain-recover : ∀ {m m′ a b k k′ φ χ ψ ρ ξ ξ′ w} (δ : m <ᴸ m′)
  (ok : Ok w) (e : Eh m m′ w (lo m (Z* ρ) ∪ ρ)) (p : k′ <ᴵ w m)
  {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl}
  {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))}
  {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
  {r : k <ᴵ a}
  {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m a (ξ ⊔ φ) (lo m ζ ∪ χ)}
  {h′ : ∀ ξ ζ → Vs m′ δ k′ ξ ζ → Q m′ b (ξ ⊔ ψ) (lo m ζ ∪ ρ)} →
  k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sim∼ m χ ρ →
  (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ m ζ ζ′ →
    (z : Q m k ξ ζ) (z′ : Q m k′ ξ′ ζ′) → Rq m k k′ z z′ →
    Cross δ a b (h ξ ζ (intoU (<→◃ r) z)) (h′ ξ′ ζ′ (intoV δ z′))) →
  ∀ i → Rq m k k′
    (chainᵠ fe fc* (λ z → qwk a₁ (⇑ (cv* m)) (ψᵠ r (h ξ (Z* χ) (intoU (<→◃ r) z)))) i)
    (chainᵠ fe′ fc* (λ z → qwk a₂ (⇑ (cv* m)) (Ψ δ ok e p (h′ ξ′ (Z* ρ) (intoV δ z)))) i)

recover {m} δ q ok e p et dz = rwk (RΩ̇ m et)
recover δ q ok e p et (ds sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ sb) (recover δ q ok e p et r))
recover δ q ok e p et (dl h) = rl (λ i → recover δ q ok e p et (h i))
recover δ q ok e p et (di d h) = ri d (λ x y dd → recover δ q ok e p et (h x y dd))
recover δ q ok e p et (dŝ d r h) = rŝ d (recover δ q ok e p et r) (λ η ee η′ e′ dη → recover δ q ok e p et (h η ee η′ e′ dη))
recover δ q ok e p et (dĉ d dzz dg r h) = rĉ d dzz dg (recover δ q ok e p et r) (λ η ee η′ e′ dη → recover δ q ok e p et (h η ee η′ e′ dη))
recover δ q ok e p et (dclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (recover δ q ok e p et r)) (λ η η′ d → rwk (recover δ q ok e p et (h η η′ d))))
recover δ q ok e p et (dmark r) = recover δ q ok e p et r
recover δ q ok e p et (dwkˡ r) = rwkˡ (recover δ q ok e p et r)
recover δ q ok e p et (dwkʳ {lc′ = lc} r) = rwkʳ (recover δ q ok (λ i hi ri → lc i ri (e i hi ri)) p et r)
recover {m} δ q ok e p et (dcl {n = n} {q = r₀} s r h) with tri n m
... | teq eq = ⊥-elim (irr (subst (n <ᴸ_) (sym eq) r₀))
... | tgt l = ⊥-elim (irr (tr< r₀ l))
... | tlt l rewrite <-prop l r₀ = rcl same (⊔∼ (∼ᶠ-refl Fl) s) (recover δ q ok e p et r)
  (λ η η′ d → rwk (recover δ q ok _ p et (h η η′ d)))
recover {m} {t = t} {t′} δ q ok e p et (dΩ↓ {n = n} {q = r₀} {h = h} {h′ = h′} ek s c f) with tri n m
... | teq eq = ⊥-elim (irr (subst (n <ᴸ_) (sym eq) r₀))
... | tgt l = ⊥-elim (irr (tr< r₀ l))
... | tlt l rewrite <-prop l r₀ = rΩ↓ same ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c)
  (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ rel → rwk
    (subst (λ v → Rq m t t′ (ψᵠ q (h ξ ζ (intoV r₀ z)))
      (Ψ δ ok (e-lo ζ′ (inj₂ r₀) e) p (h′ ξ′ ζ′ (intoV (tr< r₀ δ) v))))
      (sym (out-intoV r₀ z′))
      (recover δ q ok (e-lo ζ′ (inj₂ r₀) e) p et (f ξ ξ′ ζ ζ′ d dc z z′ (outVq r₀ rel)))))
recover {m} {t = t} {t′} δ q ok e p et
  (dΩtop {φ = φ} {χ} {ψ} {ρ} {r = r} {ac′ = ac′} {h = h} {h′ = h′} ek s c f)
  rewrite tri-self m with <ᴵ-dec r q | <ᴵ-dec (ac′ (e m (inj₁ refl) δ)) p
... | injᵃ (via d s₁) | injᵃ (via d′ s₂) =
  rΩ {r = s₁} {r′ = s₂} (≅ᴵ-trans (≅ᴵ-sym d) (≅ᴵ-trans ek d′))
    (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c)
    (λ ξ ξ′ ζ ζ′ ds dc z z′ rel → rwk
      (subst₂ (λ u v → Rq m t t′
        (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q d u))))
        (Ψ δ ok (e-lo ζ′ (inj₁ refl) e) p (h′ ξ′ ζ′ (intoV δ (tr⁻Q d′ v)))))
        (sym (out-intoU (<→◃ s₁) z)) (sym (out-intoU (<→◃ s₂) z′))
        (recover δ q ok (e-lo ζ′ (inj₁ refl) e) p et
          (f ξ ξ′ ζ ζ′ ds dc _ _ (R-tr⁻ˡ d (R-tr⁻ʳ d′ (outRq (<→◃ s₁) rel)))))))
... | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
... | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
... | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
... | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
... | injᵇ _ | injᵇ _ = rl (λ i → rwk
  (recover δ q ok (e⁺ m ok e) p et
    (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ)
      (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _
      (chain-recover δ ok (e⁺ m ok e) (ac′ (e m (inj₁ refl) δ))
        {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2}
        {r = r} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
... | injᵇ _ | injᶜ _ = rl (λ i → rwk
  (recover δ q ok (e⁺ m ok e) p et
    (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ)
      (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _
      (chain-recover δ ok (e⁺ m ok e) (ac′ (e m (inj₁ refl) δ))
        {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2}
        {r = r} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
... | injᶜ _ | injᵇ _ = rl (λ i → rwk
  (recover δ q ok (e⁺ m ok e) p et
    (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ)
      (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _
      (chain-recover δ ok (e⁺ m ok e) (ac′ (e m (inj₁ refl) δ))
        {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2}
        {r = r} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
... | injᶜ _ | injᶜ _ = rl (λ i → rwk
  (recover δ q ok (e⁺ m ok e) p et
    (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ)
      (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _
      (chain-recover δ ok (e⁺ m ok e) (ac′ (e m (inj₁ refl) δ))
        {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2}
        {r = r} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))

chain-recover {m} δ ok e p ek sξ c f zero = rwk (RΩ̇ m ek)
chain-recover {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} δ ok e p
  {fe = fe} {fe′} {a₁} {a₂} {r} {h} {h′} ek sξ c f (suc i) =
  rwk (recover δ r ok e p ek
    (f ξ ξ′ (Z* χ) (Z* ρ) sξ (Z∼ c) _ _
      (chain-recover δ ok e p {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂}
        {r = r} {h = h} {h′ = h′} ek sξ c f i)))
```
