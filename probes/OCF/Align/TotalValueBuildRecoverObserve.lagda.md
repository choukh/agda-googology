# 顶 Ω 跨层关系的完整底读回

endpoint 回收与所有低目标派发共用真实 Cross 分支证据。
本篇将其送到原 ψ̄，而非只在内部目标留下一个条件记录。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRecoverObserve (𝕊 : HtB) where
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
import OCF.Align.TotalValueBuildRecoverRun 𝕊 as U

below : ∀ {H m m′ a b t t′ φ χ ψ ρ w w′} (δ : m <ᴸ m′) (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) (ok′ : Ok w′) (e′ : Eh H m′ w′ ρ) (p′ : t′ <ᴵ w′ H) → t ≅ᴵ t′ → {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Cross δ a b x x′ → Rq H t t′ (Ψ qH ok e p x) (Ψ (tr< qH δ) ok′ e′ p′ x′)
chain-below : ∀ {m m′ a b n k k′ φ χ ψ ρ ξ ξ′ w w′} (δ : m <ᴸ m′) (q : n <ᴸ m) (ok : Ok w) (e* : Eh n m w (lo n (Z* χ) ∪ χ)) (p₁ : k <ᴵ w n) (ok′ : Ok w′) (e′* : Eh n m′ w′ (lo n (Z* ρ) ∪ ρ)) (p₂ : k′ <ᴵ w′ n)
       {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs m′ (tr< q δ) k′ ξ ζ → Q m′ b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sim∼ m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Cross δ a b (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV (tr< q δ) z′))) →
       ∀ i → Rq n k k′ (chainᵠ fe fc* (λ z → qwk a₁ (⇑ (cv* n)) (Ψ q ok e* p₁ (h ξ (Z* χ) (intoV q z)))) i) (chainᵠ fe′ fc* (λ z → qwk a₂ (⇑ (cv* n)) (Ψ (tr< q δ) ok′ e′* p₂ (h′ ξ′ (Z* ρ) (intoV (tr< q δ) z)))) i)

below {H} δ qH ok e p ok′ e′ p′ et dz = rwk (RΩ̇ H et)
below δ qH ok e p ok′ e′ p′ et (ds sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ (λ i q → sb i (tr< q qH))) (below δ qH ok e p ok′ e′ p′ et r))
below δ qH ok e p ok′ e′ p′ et (dl h) = rl (λ n → below δ qH ok e p ok′ e′ p′ et (h n))
below δ qH ok e p ok′ e′ p′ et (di d h) = ri d (λ x y dd → below δ qH ok e p ok′ e′ p′ et (h x y dd))
below δ qH ok e p ok′ e′ p′ et (dŝ d r h) = rŝ d (below δ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → below δ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
below δ qH ok e p ok′ e′ p′ et (dĉ d dz′ dg r h) = rĉ d dz′ dg (below δ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → below δ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
below δ qH ok e p ok′ e′ p′ et (dclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (below δ qH ok e p ok′ e′ p′ et r)) (λ η η′ d → rwk (below δ qH ok e p ok′ e′ p′ et (h η η′ d))))
below δ qH ok e p ok′ e′ p′ et (dmark r) = below δ qH ok e p ok′ e′ p′ et r
below δ qH ok e p ok′ e′ p′ et (dwkˡ {lc = lc} r) = rwkˡ (below δ qH ok (λ i h r₁ → lc i r₁ (e i h r₁)) p ok′ e′ p′ et r)
below δ qH ok e p ok′ e′ p′ et (dwkʳ {lc′ = lc′} r) = rwkʳ (below δ qH ok e p ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)) p′ et r)
below {H} δ qH ok e p ok′ e′ p′ et (dcl {n = n} s r h) with tri n H
... | tlt l = rcl {q = l} same (⊔∼ (∼ᶠ-refl Fl) s) (below δ qH ok e p ok′ e′ p′ et r) (λ η η′ d → rwk (below δ qH ok _ p ok′ _ p′ et (h η η′ d)))
... | teq refl = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ p _ p′ et) (below δ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (below δ qH _ _ _ _ _ _ et (h η η′ eη)))
... | tgt l = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (below δ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (below δ qH _ _ _ _ _ _ et (h η η′ eη)))
below {H} {t = t} {t′} δ qH ok e p ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) with tri n H
... | tlt l = rΩ↓ {q = l} same ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
      (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ lz → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q u))) (Ψ (tr< qH δ) ok′ (e-lo ζ′ (inj₂ l) e′) p′ (h′ ξ′ ζ′ (intoV (tr< q δ) v)))) (sym (out-intoV l z)) (sym (out-intoV l z′))
         (below δ qH ok (e-lo ζ (inj₂ l) e) p ok′ (e-lo ζ′ (inj₂ l) e′) p′ et (f ξ ξ′ ζ ζ′ d dc z z′ (outVq l lz)))))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p | <ᴵ-dec (ac′ (e′ n (inj₁ refl) (tr< q δ))) p′
...   | injᵃ (via d₁ s₁) | injᵃ (via d₂ s₂) =
  rΩ {r = s₁} {r′ = s₂} (≅ᴵ-trans (≅ᴵ-sym d₁) (≅ᴵ-trans ek d₂)) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q (tr⁻Q d₁ u)))) (Ψ (tr< qH δ) ok′ (e-lo ζ′ (inj₁ refl) e′) p′ (h′ ξ′ ζ′ (intoV (tr< q δ) (tr⁻Q d₂ v))))) (sym (out-intoU (<→◃ s₁) z)) (sym (out-intoU (<→◃ s₂) z′))
        (below δ qH ok (e-lo ζ (inj₁ refl) e) p ok′ (e-lo ζ′ (inj₁ refl) e′) p′ et (f ξ ξ′ ζ ζ′ d dc _ _ (R-tr⁻ˡ d₁ (R-tr⁻ʳ d₂ (outRq (<→◃ s₁) l)))))))
...   | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
...   | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
...   | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
...   | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
...   | injᵇ _ | injᵇ _ = rl (λ i → rwk (below δ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chain-below δ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᵇ _ | injᶜ _ = rl (λ i → rwk (below δ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chain-below δ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᶜ _ | injᵇ _ = rl (λ i → rwk (below δ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chain-below δ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᶜ _ | injᶜ _ = rl (λ i → rwk (below δ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chain-below δ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
below {H} {t = t} {t′} δ qH ok e p ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) | tgt l =
  rl (λ i → rwk (below δ qH ok (e⁺ n ok e) p ok′ (e⁺ n ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chain-below δ q ok (e⁺ n ok (e↑ l e)) (ac ((e↑ l e) n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↑ l e′)) (ac′ ((e↑ l e′) n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))

below {H} {m} {t = t} {t′} δ qH ok e p ok′ e′ p′ et
  (dΩtop {φ = φ} {χ} {ψ} {ρ} {r = r} {ac′ = ac′} {h = h} {h′ = h′} ek s c f) with tri m H
... | tlt l = ⊥-elim (irr (tr< qH l))
... | teq eq = ⊥-elim (irr (subst (_<ᴸ m) (sym eq) qH))
... | tgt l rewrite <-prop l qH = rl (λ i → rwk
  (below δ qH ok (e⁺ m ok e) p ok′ (e⁺ m ok′ e′) p′ et
    (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ)
      (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _
      (U.chain-recover δ ok′ (e⁺ m ok′ (e↑ qH e′))
        (ac′ (e↑ qH e′ m (inj₁ refl) δ))
        {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2}
        {r = r} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))

chain-below {n = n} δ q ok e* p₁ ok′ e′* p₂ ek sξ c f zero = rwk (RΩ̇ n ek)
chain-below {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} δ q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′} {a₁} {a₂} {h} {h′} ek sξ c f (suc i) =
  rwk (below δ q ok e* p₁ ok′ e′* p₂ ek (f ξ ξ′ (Z* χ) (Z* ρ) sξ (Z∼ (λ j r → c j (tr< r q))) _ _ (chain-below δ q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂} {h = h} {h′ = h′} ek sξ c f i)))
observe : ∀ {m m′ a b φ χ ψ ρ w w′} {δ : m <ᴸ m′} {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Cross δ a b x x′ → (ok : Ok w) (e : Eh h₀ m w χ) (ok′ : Ok w′) (e′ : Eh h₀ m′ w′ ρ) → ψ̄ᵠ ok e x ≈ᴿ ψ̄ᵠ ok′ e′ x′
observe dz ok e ok′ e′ = wkR _ _ r∅
observe (ds s c r) ok e ok′ e′ = sucR (observe r ok e ok′ e′)
observe (dl h) ok e ok′ e′ = limR (λ n → observe (h n) ok e ok′ e′)
observe (di {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) ok e ok′ e′ = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ᵠ ok e (f x)} {H′ = λ x → ψ̄ᵠ ok′ e′ (f′ x)} d (λ x y dd → observe (h x y dd) ok e ok′ e′)
observe (dŝ d r h) ok e ok′ e′ = ŝR d (observe r ok e ok′ e′) (λ η ee η′ e₁ dd → observe (h η ee η′ e₁ dd) ok e ok′ e′)
observe (dĉ d dz′ dg r h) ok e ok′ e′ = ĉR d dz′ dg (observe r ok e ok′ e′) (λ η ee η′ e₁ dd → observe (h η ee η′ e₁ dd) ok e ok′ e′)
observe (dclo {t = t} {t′} {g} {g′} s r h) ok e ok′ e′ = cloR {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} {t′ = ψ̄ᵠ ok′ e′ t′} {g′ = λ η → ψ̄ᵠ ok′ e′ (g′ η)} s (observe r ok e ok′ e′) (λ η η′ d → observe (h η η′ d) ok e ok′ e′)
observe {χ = χ} {ρ = ρ} {w = w} {w′ = w′} {δ = δ} (dcl {n = n} {κ₁ = κ₁} {κ₂ = κ₂} {q = q} {s = s₁} {s′ = s₂} s r h) ok e ok′ e′ =
  ŝR (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (observe r ok e ok′ e′)
      (λ η d η′ d′ eη → observe (h η η′ eη)
         (upd-ok n w ok (tt , λ x → lim 0 (proj₂ (evF B₁) x))) (λ i k r₁ → upd-ev n i w χ (evη κ₁ B₁ η d) (e i k r₁))
         (upd-ok n w′ ok′ (tt , λ x → lim 0 (proj₂ (evF B₂) x))) (λ i k r₁ → upd-ev n i w′ ρ (evη κ₂ B₂ η′ d′) (e′ i k r₁)))
  where
  B₁ = bound (κ₁ ⊔ fk zero) (s₁ (e n (Hi-0 n) q)) (zr ok n)
  B₂ = bound (κ₂ ⊔ fk zero) (s₂ (e′ n (Hi-0 n) (tr< q δ))) (zr ok′ n)
observe (dmark r) ok e ok′ e′ = observe r ok e ok′ e′
observe (dwkˡ {le = le} {lc = lc} r) ok e ok′ e′ = wkR le (λ v → v) (observe r ok (λ i h r₁ → lc i r₁ (e i h r₁)) ok′ e′)
observe (dwkʳ {le′ = le′} {lc′ = lc′} r) ok e ok′ e′ = wkR (λ v → v) le′ (observe r ok e ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)))
observe {δ = δ} (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {q = q} {fe = fe} {fe′} {ac} {ac′} {h} {h′} ek s c f) ok e ok′ e′ =
  limR (λ i → wkR _ _ (observe (f φ ψ (Z* χ) (Z* ρ) s (Z∼ (λ j r → c j (tr< r q))) _ _ (chain-below δ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↓ e′)) (ac′ (e↓ e′ n (inj₁ refl) (tr< q δ))) {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {h = h} {h′ = h′} ek s c f i)) ok (e⁺ n ok e) ok′ (e⁺ n ok′ e′)))

observe {m = m} {δ = δ}
  (dΩtop {φ = φ} {χ} {ψ} {ρ} {r = r} {fe = fe} {fe′} {ac′ = ac′} {h} {h′} ek s c f) ok e ok′ e′ =
  limR (λ i → wkR _ _
    (observe
      (f φ ψ (Z* χ) (Z* ρ) s (Z∼ c) _ _
        (U.chain-recover δ ok′ (e⁺ m ok′ (e↓ e′))
          (ac′ (e↓ e′ m (inj₁ refl) δ))
          {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)}
          {r = r} {h = h} {h′ = h′} ek s c f i))
      ok (e⁺ m ok e) ok′ (e⁺ m ok′ e′)))
```
