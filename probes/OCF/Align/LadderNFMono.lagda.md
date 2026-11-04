# 阶梯去记号 (二十二): 层号的单调

> 结论写在 [LadderNF](LadderNF.lagda.md). `Ωm`: 经 `ι` 看, $\dot\Omega$ 对层号单调. `Ωm↓`: 经 `ι↓` 看, 同样. `Up≤`: `omk` 的两格各走各的, 由此 $\dot\Omega_{\lim f}$ 的基本列单调. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderNFMono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Ωˢ; addˢ; _+ˢ_; 𝟎ˢ)
open import OCF.Free.Eq using (≅ᴵ→⊑ᴵ; ⊑ᴵ-≅ˡ; ⊑ᴵ-≅ʳ; _≅ᶻ_; ≅ᶻ-sym; _≅ˢ_; z≅; s≅; l≅; upˡ; upʳ; ≅ˢ-sym; ≅ˢ-trans; ≅ˢ-reflˡ; ≅ˢ-reflʳ; trˢ-≅; tr⁻ˢ-≅; ≅-trˢ; ≅-tr⁻ˢ; Ωˢ-≅; Ωˢ-refl; toZ-≅; addˢ-≅; s-invˢ; l-invˢ; i-respˢ; u-reflˢ; ŝ-refl₀; ĉ-refl₀; self-trˢ; self-tr⁻ˢ)
open import OCF.Free.Floor using (_∼ᶠ_; ∼ᶠ-refl; fz∼; ⊔∼; Flr; fz; fk; Ev; Run; flo; cvFlo; toFlo; ∅ᴿ; _⊔_; bound)
open import OCF.Free.Force using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; Goodᴺ-tr)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderNFTree
open import OCF.Align.LadderNFRel
open import OCF.Align.LadderNFCx
open import OCF.Align.LadderNFRules
open import OCF.Align.LadderNFRules2
open import OCF.Align.LadderNFRules3
open import OCF.Align.LadderNFStrict
open import Data.Bool using (Bool; true; false)
open import OCF.Free.Eq using (backˢ-≅; back⁻ˢ-≅; ≅ˢ-trans)
open import OCF.Align.LadderNFStrict2
open import OCF.Align.LadderNFClass
open import OCF.Free.Eq using (≅ᴵ→⊑ᴵ)

open RestrQ
```

## §1 两次嵌入

```agda
R-ιι : ∀ {m a b b′ c d φ χ ψ ρ} (q : a ◃ c) (q₁ : b ◃ b′) (q₂ : b′ ◃ d) {x : Q m a φ χ} {x′ : Q m b ψ ρ} → Rq m a b x x′ → Rq m c d (ι q x) (ι q₂ (ι q₁ x′))
R-ιι q q₁ q₂ rz = rz
R-ιι q q₁ q₂ (rs sa sb r) = rs sa sb (R-ιι q q₁ q₂ r)
R-ιι q q₁ q₂ (rl h) = rl (λ n → R-ιι q q₁ q₂ (h n))
R-ιι q q₁ q₂ (ri e h) = ri e (λ x y d → R-ιι q q₁ q₂ (h x y d))
R-ιι q q₁ q₂ (rŝ e r h) = rŝ e (R-ιι q q₁ q₂ r) (λ η ee η′ e′ d → R-ιι q q₁ q₂ (h η ee η′ e′ d))
R-ιι q q₁ q₂ (rĉ e dz dg r h) = rĉ e dz dg (R-ιι q q₁ q₂ r) (λ η ee η′ e′ d → R-ιι q q₁ q₂ (h η ee η′ e′ d))
R-ιι q q₁ q₂ (rclo s r h) = rclo s (R-ιι q q₁ q₂ r) (λ η η′ d → R-ιι q q₁ q₂ (h η η′ d))
R-ιι q q₁ q₂ (rcl eqn s r h) = rcl eqn s (R-ιι q q₁ q₂ r) (λ η η′ d → R-ιι q q₁ q₂ (h η η′ d))
R-ιι q q₁ q₂ (rwkˡ r) = rwkˡ (R-ιι q q₁ q₂ r)
R-ιι q q₁ q₂ (rwkʳ r) = rwkʳ (R-ιι q q₁ q₂ r)
R-ιι q q₁ q₂ (rΩ↓ eqn ek s c f) = rΩ↓ eqn ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → R-ιι q q₁ q₂ (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
R-ιι {m} {c = c} {d = dd} q q₁ q₂ (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s c′ f) =
  rΩ {r = <◃ r q} {r′ = <◃ (<◃ r′ q₁) q₂} ek s c′
     (λ ξ ξ′ ζ ζ′ e dc z z′ l →
        subst₂ (λ w w′ → Rq m c dd (ι q (h ξ ζ (intoU (<→◃ r) w))) (ι q₂ (ι q₁ (h′ ξ′ ζ′ (intoU (<→◃ r′) (outU (<→◃ (<◃ r′ q₁)) (intoU (<→◃ (<◃ r′ q₁)) w′))))))) (sym (out-intoU (<→◃ (<◃ r q)) z)) (sym (out-intoU (<→◃ (<◃ (<◃ r′ q₁) q₂)) z′))
          (subst (λ w′ → Rq m c dd (ι q (h ξ ζ (intoU (<→◃ r) z))) (ι q₂ (ι q₁ (h′ ξ′ ζ′ (intoU (<→◃ r′) w′))))) (sym (out-intoU (<→◃ (<◃ r′ q₁)) z′))
             (R-ιι q q₁ q₂ (f ξ ξ′ ζ ζ′ e dc _ _ (intoRq (<→◃ r) (outRq (<→◃ (<◃ r q)) l))))))
R-ιι q q₁ q₂ (rob _ l r) = R-ιι q q₁ q₂ r

R-ιι′ : ∀ {m a a′ b c d φ χ ψ ρ} (q₁ : a ◃ a′) (q₂ : a′ ◃ c) (q : b ◃ d) {x : Q m a φ χ} {x′ : Q m b ψ ρ} → Rq m a b x x′ → Rq m c d (ι q₂ (ι q₁ x)) (ι q x′)
R-ιι′ q₁ q₂ q rz = rz
R-ιι′ q₁ q₂ q (rs sa sb r) = rs sa sb (R-ιι′ q₁ q₂ q r)
R-ιι′ q₁ q₂ q (rl h) = rl (λ n → R-ιι′ q₁ q₂ q (h n))
R-ιι′ q₁ q₂ q (ri e h) = ri e (λ x y d → R-ιι′ q₁ q₂ q (h x y d))
R-ιι′ q₁ q₂ q (rŝ e r h) = rŝ e (R-ιι′ q₁ q₂ q r) (λ η ee η′ e′ d → R-ιι′ q₁ q₂ q (h η ee η′ e′ d))
R-ιι′ q₁ q₂ q (rĉ e dz dg r h) = rĉ e dz dg (R-ιι′ q₁ q₂ q r) (λ η ee η′ e′ d → R-ιι′ q₁ q₂ q (h η ee η′ e′ d))
R-ιι′ q₁ q₂ q (rclo s r h) = rclo s (R-ιι′ q₁ q₂ q r) (λ η η′ d → R-ιι′ q₁ q₂ q (h η η′ d))
R-ιι′ q₁ q₂ q (rcl eqn s r h) = rcl eqn s (R-ιι′ q₁ q₂ q r) (λ η η′ d → R-ιι′ q₁ q₂ q (h η η′ d))
R-ιι′ q₁ q₂ q (rwkˡ r) = rwkˡ (R-ιι′ q₁ q₂ q r)
R-ιι′ q₁ q₂ q (rwkʳ r) = rwkʳ (R-ιι′ q₁ q₂ q r)
R-ιι′ q₁ q₂ q (rΩ↓ eqn ek s c f) = rΩ↓ eqn ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → R-ιι′ q₁ q₂ q (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
R-ιι′ {m} {c = c} {d = dd} q₁ q₂ q (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s c′ f) =
  rΩ {r = <◃ (<◃ r q₁) q₂} {r′ = <◃ r′ q} ek s c′
     (λ ξ ξ′ ζ ζ′ e dc z z′ l →
        subst₂ (λ w w′ → Rq m c dd (ι q₂ (ι q₁ (h ξ ζ (intoU (<→◃ r) (outU (<→◃ (<◃ r q₁)) (intoU (<→◃ (<◃ r q₁)) w)))))) (ι q (h′ ξ′ ζ′ (intoU (<→◃ r′) w′)))) (sym (out-intoU (<→◃ (<◃ (<◃ r q₁) q₂)) z)) (sym (out-intoU (<→◃ (<◃ r′ q)) z′))
          (subst (λ w → Rq m c dd (ι q₂ (ι q₁ (h ξ ζ (intoU (<→◃ r) w)))) (ι q (h′ ξ′ ζ′ (intoU (<→◃ r′) z′)))) (sym (out-intoU (<→◃ (<◃ r q₁)) z))
             (R-ιι′ q₁ q₂ q (f ξ ξ′ ζ ζ′ e dc _ _ (intoRq (<→◃ r) (outRq (<→◃ (<◃ (<◃ r q₁) q₂)) l))))))
R-ιι′ q₁ q₂ q (rob _ l r) = R-ιι′ q₁ q₂ q r

◃-tr : ∀ {a b c} → a ◃ b → b ◃ c → a ◃ c
◃-tr r zero      = suc r
◃-tr r (suc q)   = suc (◃-tr r q)
◃-tr r (self n)  = lim n r
◃-tr r (lim n q) = lim n (◃-tr r q)

⊑ᵗ-Rˡ : ∀ {m c φ χ ψ ρ} {x x′ : Q m c φ χ} {y : Q m c ψ ρ} → Rq m c c x x′ → x′ ⊑ᵗ y → x ⊑ᵗ y
⊑ᵗ-Rˡ e h o G G′ = ⊑-trans (≅→⊑ (forceᴺ-≅ d G (Goodᴺ-tr d G))) (h o (Goodᴺ-tr d G) G′)
  where d = toZ-≅ (runᶜ-≅ (≈ᶜ-reflˡ o) e)
```

## §2 上行

```agda
Ωstep : ∀ {m b c} (r₀ : b ◃ c) (r : suc b ◃ c) → ι r₀ (Ω̇ m b) ⊑ᵀ ι r (Ω̇ m (suc b))
Ωstep {m} {b} {c} r₀ r = Ω-rᵀ (λ ξ ζ z rz₁ f →
  subst (λ w → ι r₀ (Ω̇ m b) ⊑ᵀ ι r (qwk proj₁ (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e)) (omk zero w (ι zero w)))) (sym (out-intoU (<→◃ (<◃ {k = b} zero r)) z))
    (wk-rᵀ (⊑ᵀ-Rʳ (ι-cong {q = r₀} (f (RΩ̇ m (≅ᴵ-refl b)) (R→⊑ᵀ (RΩ̇ m (≅ᴵ-refl b))))) (R-ιι r₀ zero r rz₁))))

Ωlim : ∀ {m f s c} n (r₀ : f n ◃ c) (r : lim f s ◃ c) → ι r₀ (Ω̇ m (f n)) ⊑ᵀ ι r (Ω̇ m (lim f s))
Ωlim {m} n r₀ r = lim-rᵀ n (R→⊑ᵀ (R-ιι r₀ (self n) r (RΩ̇ m (≅ᴵ-refl _))))

Ωz : ∀ {m c} b (r : zero ◃ c) (r′ : b ◃ c) → ι r (Ω̇ m zero) ⊑ᵀ ι r′ (Ω̇ m b)
Ωz {m} zero r r′ = R→⊑ᵀ (R-ι r r′ (RΩ̇ m z≅))
Ωz (suc b) r r′ = ⊑ᵀ-trans (Ωz b r (◃-tr zero r′)) (Ωstep (◃-tr zero r′) r′)
Ωz (lim g s) r r′ = ⊑ᵀ-trans (Ωz (g 0) r (◃-tr (self 0) r′)) (Ωlim 0 (◃-tr (self 0) r′) r′)

Ωs : ∀ {m a₀ a″ b c} → a₀ ≅ᴵ a″ → a″ <ᴵ b → (r : suc a₀ ◃ c) (r′ : b ◃ c) → ι r (Ω̇ m (suc a₀)) ⊑ᵀ ι r′ (Ω̇ m b)
Ωs {m} e zero r r′ = R→⊑ᵀ (R-ι r r′ (RΩ̇ m (s≅ e)))
Ωs e (suc q) r r′ = ⊑ᵀ-trans (Ωs e q r (◃-tr zero r′)) (Ωstep (◃-tr zero r′) r′)
Ωs e (lim n q) r r′ = ⊑ᵀ-trans (Ωs e q r (◃-tr (self n) r′)) (Ωlim n (◃-tr (self n) r′) r′)

Ωm : ∀ {m a b c} → a ⊑ᴵ b → (r : a ◃ c) (r′ : b ◃ c) → ι r (Ω̇ m a) ⊑ᵗ ι r′ (Ω̇ m b)
Ωm {m} {b = b} z⊑ r r′ = ⊑ᵀ→ᵗ (R-ι r r (RΩ̇ m z≅)) (Ωz b r r′)
Ωm {m} (s⊑ e q) r r′ = ⊑ᵀ→ᵗ (R-ι r r (RΩ̇ m (≅ᴵ-refl _))) (Ωs e q r r′)
Ωm {m} (l⊑ k) r r′ = lim-lᵗ (λ n → ⊑ᵗ-Rˡ (R-ιι′ (self n) r (◃-tr (self n) r) (RΩ̇ m (≅ᴵ-refl _))) (Ωm (k n) (◃-tr (self n) r) r′))
```

## §3 下行

```agda
⊑ᵀ-transʷ : ∀ {m c φ₀ χ₀ φ₁ χ₁ ψ ρ} {x : Q m c φ₀ χ₀} {y : Q m c φ₁ χ₁} {w : Q m c ψ ρ} (le : ∀ {L} → Ev L ψ → Ev L φ₁) (lc : Sub m ρ χ₁) → x ⊑ᵀ y → y ⊑ᵀ w → x ⊑ᵀ w
⊑ᵀ-transʷ le lc h i {C} {C′} o G′ = proj₁ K , ⊑-trans (proj₂ K) (proj₂ J)
  where
  J = i (≈ᶜ-wkˡ le lc (≈ᶜ-reflʳ o)) G′
  K = h (≈ᶜ-wkʳ le lc o) (proj₁ J)

D↑s : ∀ {n b} → Sub (suc n) (upd (κ Fl) n (flo (suc b))) (upd (κ Fl) n (flo b))
D↑s {n} {b} = ⇑ (upd-map n (λ i e → e) (tighten zero))

D↑l : ∀ {n f s} i → Sub (suc n) (upd (κ Fl) n (flo (lim f s))) (upd (κ Fl) n (flo (f i)))
D↑l {n} i = ⇑ (upd-map n (λ j e → e) (tighten (self i)))

Ωstep↓ : ∀ {n b} → ι↓ {n = n} {α = zero} (Ω̇ n b) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n (suc b))
Ωstep↓ {n} {b} = Ω↓-rᵀ {q = zero} (λ ξ ζ z rz₁ f → wk-rᵀ (wk-rᵀ (wk-rᵀ (ιD-cong (f (RΩ̇ n (≅ᴵ-refl b)) (R→⊑ᵀ (RΩ̇ n (≅ᴵ-refl b))))))))

Ωlim↓ : ∀ {n f s} i → ι↓ {n = n} {α = zero} (Ω̇ n (f i)) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n (lim f s))
Ωlim↓ {n} {f} i = lim-rᵀ i (wk-rᵀ (R→⊑ᵀ (R-ι↓ (≅ᴵ-refl (f i)) (RΩ̇ n (≅ᴵ-refl (f i))))))

Ωz↓ : ∀ {n} b → ι↓ {n = n} {α = zero} (Ω̇ n zero) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n b)
Ωz↓ {n} zero = R→⊑ᵀ (R-ι↓ z≅ (RΩ̇ n z≅))
Ωz↓ (suc b) = ⊑ᵀ-transʷ (λ e → e) D↑s (Ωz↓ b) Ωstep↓
Ωz↓ (lim g s) = ⊑ᵀ-transʷ (λ e → e) (D↑l 0) (Ωz↓ (g 0)) (Ωlim↓ 0)

Ωs↓ : ∀ {n a₀ a″ b} → a₀ ≅ᴵ a″ → a″ <ᴵ b → ι↓ {n = n} {α = zero} (Ω̇ n (suc a₀)) ⊑ᵀ ι↓ {n = n} {α = zero} (Ω̇ n b)
Ωs↓ {n} e zero = R→⊑ᵀ (R-ι↓ (s≅ e) (RΩ̇ n (s≅ e)))
Ωs↓ e (suc q) = ⊑ᵀ-transʷ (λ e₁ → e₁) D↑s (Ωs↓ e q) Ωstep↓
Ωs↓ e (lim i q) = ⊑ᵀ-transʷ (λ e₁ → e₁) (D↑l i) (Ωs↓ e q) (Ωlim↓ i)

Ωm↓ : ∀ {n a b} → a ⊑ᴵ b → ι↓ {n = n} {α = zero} (Ω̇ n a) ⊑ᵗ ι↓ {n = n} {α = zero} (Ω̇ n b)
Ωm↓ {n} {b = b} z⊑ = ⊑ᵀ→ᵗ (R-ι↓ z≅ (RΩ̇ n z≅)) (Ωz↓ b)
Ωm↓ {n} (s⊑ e q) = ⊑ᵀ→ᵗ (R-ι↓ (≅ᴵ-refl _) (RΩ̇ n (≅ᴵ-refl _))) (Ωs↓ e q)
Ωm↓ (l⊑ k) = lim-lᵗ (λ i → wk-lᵗ (Ωm↓ (k i)))
```

## §4 `Up` 的单调

```agda
-- y 在一切上下文里与 Ω̇ k 同值
RΩv : ∀ n k {φ χ} → Q n k φ χ → Set
RΩv n k {φ} {χ} y = ∀ {E : Cx n k φ χ} {E₂ : Cx n k Fl (κ Fl)} → E ≈ᶜ E₂ → runᶜ E y ≅ˢ runᶜ E₂ (Ω̇ n k)

RΩv-Ω : ∀ {n k} → RΩv n k (Ω̇ n k)
RΩv-Ω {n} {k} o = runᶜ-≅ o (RΩ̇ n (≅ᴵ-refl k))

RΩv-tr : ∀ {n a b φ χ} (e : a ≅ᴵ b) {y : Q n a φ χ} → RΩv n a y → RΩv n b (trQ e y)
RΩv-tr {n} e h {E = E} {E₂} o = ≅ˢ-trans (h {E = ptr e E} {E₂ = ptr e E₂} (ptr o)) (runᶜ-≅ (≈ᶜ-reflʳ o) (R-trˡ e (RΩ̇ n e)))

RΩv-tr⁻ : ∀ {n a b φ χ} (e : a ≅ᴵ b) {y : Q n b φ χ} → RΩv n b y → RΩv n a (tr⁻Q e y)
RΩv-tr⁻ {n} e h {E = E} {E₂} o = ≅ˢ-trans (h {E = ptr⁻ e E} {E₂ = ptr⁻ e E₂} (ptr⁻ o)) (runᶜ-≅ (≈ᶜ-reflʳ o) (R-tr⁻ˡ e (RΩ̇ n (≅ᴵ-sym e))))

shD≤ : ∀ {n k k′ ℓ} (r : k ◃₁ ℓ) (r′ : k′ ◃₁ ℓ) {C C′ : Cx n ℓ Fl (κ Fl)} → C ≈ᶜ C′ → (d : Dd C) (d′ : Dd C′) → k ⊑ᴵ k′ →
       {y : Q n k Fl (κ Fl)} {y′ : Q n k′ Fl (κ Fl)} → RΩv n k y → RΩv n k′ y′ →
       (G : Goodᴺ (toZ (runᶜ (shD r C d) y))) (G′ : Goodᴺ (toZ (runᶜ (shD r′ C′ d′) y′))) → forceᴺ _ G ⊑ forceᴺ _ G′
shD≤ {n} {k} {k′} r r′ (pD {C = C₁} {C′ = C₁′} o) d d′ u {y} {y′} hy hy′ G G′ =
  ⊑-trans (≅→⊑ (forceᴺ-≅ dl G G₁)) (⊑-trans (Ωm↓ u (wk≈ (λ e → e) _ (λ e → e) _ o) G₁ G₁′) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dr) G₁′ G′)))
  where
  dl = toZ-≅ (hy {E₂ = pD (wkC (λ e → e) (⇑ (upd-map n (λ i e → e) (tighten r))) C₁)} (pD (wk≈ (λ e → e) _ (λ e → e) _ (≈ᶜ-reflˡ o))))
  dr = toZ-≅ (hy′ {E₂ = pD (wkC (λ e → e) (⇑ (upd-map n (λ i e → e) (tighten r′))) C₁′)} (pD (wk≈ (λ e → e) _ (λ e → e) _ (≈ᶜ-reflʳ o))))
  G₁ = Goodᴺ-tr dl G
  G₁′ = Goodᴺ-tr dr G′
shD≤ zero zero (ptr {e = s≅ e} {e′ = s≅ e′} o) d d′ u hy hy′ G G′ =
  shD≤ zero zero o d d′ (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (≅ᴵ-sym e)) (⊑ᴵ-trans u (≅ᴵ→⊑ᴵ e′))) (RΩv-tr e hy) (RΩv-tr e′ hy′) G G′
shD≤ (self i) (self j) (ptr {e = l≅ h} {e′ = l≅ h′} o) d d′ u hy hy′ G G′ =
  shD≤ (self i) (self j) o d d′ (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (≅ᴵ-sym (h i))) (⊑ᴵ-trans u (≅ᴵ→⊑ᴵ (h′ j)))) (RΩv-tr (h i) hy) (RΩv-tr (h′ j) hy′) G G′
shD≤ zero zero (ptr⁻ {e = s≅ e} {e′ = s≅ e′} o) d d′ u hy hy′ G G′ =
  shD≤ zero zero o d d′ (⊑ᴵ-trans (≅ᴵ→⊑ᴵ e) (⊑ᴵ-trans u (≅ᴵ→⊑ᴵ (≅ᴵ-sym e′)))) (RΩv-tr⁻ e hy) (RΩv-tr⁻ e′ hy′) G G′
shD≤ (self i) (self j) (ptr⁻ {e = l≅ h} {e′ = l≅ h′} o) d d′ u hy hy′ G G′ =
  shD≤ (self i) (self j) o d d′ (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (h i)) (⊑ᴵ-trans u (≅ᴵ→⊑ᴵ (≅ᴵ-sym (h′ j))))) (RΩv-tr⁻ (h i) hy) (RΩv-tr⁻ (h′ j) hy′) G G′

shE≤ : ∀ {n f s} i j → f i ⊑ᴵ f j → {C C′ : Cx n (lim f s) Fl (κ Fl)} → C ≈ᶜ C′ → (u : Nd C ⊎ Dd C) (v : Nd C′ ⊎ Dd C′) →
       (G : Goodᴺ (toZ (runᶜ (shE (self i) C u) (Ω̇ n (f i))))) (G′ : Goodᴺ (toZ (runᶜ (shE (self j) C′ v) (Ω̇ n (f j))))) → forceᴺ _ G ⊑ forceᴺ _ G′
shE≤ i j le o (inj₁ a) (inj₁ b) G G′ = Ωm le (self i) (self j) o G G′
shE≤ i j le {C = C} o (inj₁ a) (inj₂ b) G G′ = ⊥-elim (Nd∧Dd C a (Dd-≈ o b))
shE≤ i j le {C′ = C′} o (inj₂ a) (inj₁ b) G G′ = ⊥-elim (Nd∧Dd C′ b (Dd-≈ (≈ᶜ-sym o) a))
shE≤ i j le o (inj₂ a) (inj₂ b) G G′ = shD≤ (self i) (self j) o a b le RΩv-Ω RΩv-Ω G G′

Up≤ : ∀ {n f s} i j → f i ⊑ᴵ f j → Up (self {f} {s} i) (Ω̇ n (f i)) ⊑ᵗ Up (self {f} {s} j) (Ω̇ n (f j))
Up≤ {n} {f} i j le {C} {C′} o G G′ =
  ⊑-trans (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym dl) G G₁)) (⊑-trans (shE≤ i j le o (dh C) (dh C′) G₁ G₁′) (≅→⊑ (forceᴺ-≅ dr G₁′ G′)))
  where
  dl = toZ-≅ (up-run (self i) (≈ᶜ-reflˡ o) (RΩ̇ n (≅ᴵ-refl (f i))))
  dr = toZ-≅ (up-run (self j) (≈ᶜ-reflʳ o) (RΩ̇ n (≅ᴵ-refl (f j))))
  G₁ = Goodᴺ-tr (≅ᶻ-sym dl) G
  G₁′ = Goodᴺ-tr (≅ᶻ-sym dr) G′
```
