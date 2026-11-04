# 序数高度: 跨高度的关系 `Dn`

> 由 `Survey/scripts/ladderord/mk_ord.py` 从 [LadderInfDn](LadderInfDn.lagda.md) 生成, 对结构 `HtB` 参数化. **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 除了名字逐字相同. 下面的说明是原文件的.
>
> **判决: HOLDS** (编译过, 无条件). 结论写在 [LadderOrd](LadderOrd.lagda.md). 由 `Survey/scripts/laddernf/mk_inf_down.py` 从 [LadderMonoRel](LadderMonoRel.lagda.md), [LadderMonoDown](LadderMonoDown.lagda.md) 改写, $m+1$ 换成任意 `δ : m <ᴸ m′`, 节点的 `suc q` 换成 `tr< q δ`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdDn (𝕊 : HtB) where

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
```

## §1 关系

```agda
module _ {m m′ : Ht} (δ : m <ᴸ m′) (a b : Ordᴵ) where
  data Dn : ∀ {φ χ ψ ρ} → Q m a φ χ → Q m′ b ψ ρ → Set where
    dz : ∀ {φ χ ψ ρ} → Dn {φ} {χ} {ψ} {ρ} q0 q0
    ds : ∀ {φ χ ψ ρ} {p : Q m a φ χ} {p′ : Q m′ b ψ ρ} → φ ∼ᶠ ψ → Sim∼ m χ ρ → Dn p p′ → Dn (qs p) (qs p′)
    dl : ∀ {φ χ ψ ρ} {F : ℕ → Q m a φ χ} {F′ : ℕ → Q m′ b ψ ρ} → (∀ n → Dn (F n) (F′ n)) → Dn (ql F) (ql F′)
    di : ∀ {φ χ ψ ρ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → Q m a φ χ} {f′ : Ordˢ j′ → Q m′ b ψ ρ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → Dn (f x) (f′ y)) → Dn (qi ac f) (qi ac′ f′)
    dŝ : ∀ {φ χ ψ ρ c₁ c₂} {t : Q m a φ χ} {t′ : Q m′ b ψ ρ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q m′ b ψ ρ} →
         c₁ ≅ᴵ c₂ → Dn t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Dn (g η e) (g′ η′ e′)) → Dn (qŝ c₁ t g) (qŝ c₂ t′ g′)
    dĉ : ∀ {φ χ ψ ρ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : Q m a φ χ} {o₀′ : Q m′ b ψ ρ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q m′ b ψ ρ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → Dn o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → Dn (o η e) (o′ η′ e′)) → Dn (qĉ c₁ z zg o₀ o) (qĉ c₂ z′ zg′ o₀′ o′)
    dclo : ∀ {φ χ ψ ρ} {t : Q m a (φ ⊔ fk zero) χ} {t′ : Q m′ b (ψ ⊔ fk zero) ρ} {g : (η : Ordᴵ) → Q m a (φ ⊔ fk η) χ} {g′ : (η : Ordᴵ) → Q m′ b (ψ ⊔ fk η) ρ} →
         φ ∼ᶠ ψ → Dn t t′ → (∀ η η′ → η ≅ᴵ η′ → Dn (g η) (g′ η′)) → Dn (qclo t g) (qclo t′ g′)
    dcl : ∀ {φ χ ψ ρ n κ₁ κ₂} {q : n <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : Q m a φ χ} {t′ : Q m′ b ψ ρ} {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → Q m′ b ψ (upd ρ n (κ₂ ⊔ fk η))} →
         κ₁ ∼ᶠ κ₂ → Dn t t′ → (∀ η η′ → η ≅ᴵ η′ → Dn (g η) (g′ η′)) → Dn (qcl q κ₁ s t g) (qcl (tr< q δ) κ₂ s′ t′ g′)
    dwkˡ : ∀ {φ φ′ χ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Dn x x′ → Dn (qwk le lc x) x′
    dwkʳ : ∀ {φ χ ψ ψ′ ρ ρ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub m′ ρ′ ρ} {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Dn x x′ → Dn x (qwk le′ lc′ x′)
    dΩ↓ : ∀ {φ χ ψ ρ n k k′} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs m′ (tr< q δ) k′ ξ ζ → Q m′ b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Dn (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV (tr< q δ) z′))) → Dn (qΩ↓ q fe ac h) (qΩ↓ (tr< q δ) fe′ ac′ h′)
D-Ψ : ∀ {H m m′ a b t t′ φ χ ψ ρ w w′} (δ : m <ᴸ m′) (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) (ok′ : Ok w′) (e′ : Eh H m′ w′ ρ) (p′ : t′ <ᴵ w′ H) → t ≅ᴵ t′ → {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Dn δ a b x x′ → Rq H t t′ (Ψ qH ok e p x) (Ψ (tr< qH δ) ok′ e′ p′ x′)
chD : ∀ {m m′ a b n k k′ φ χ ψ ρ ξ ξ′ w w′} (δ : m <ᴸ m′) (q : n <ᴸ m) (ok : Ok w) (e* : Eh n m w (lo n (Z* χ) ∪ χ)) (p₁ : k <ᴵ w n) (ok′ : Ok w′) (e′* : Eh n m′ w′ (lo n (Z* ρ) ∪ ρ)) (p₂ : k′ <ᴵ w′ n)
       {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs m′ (tr< q δ) k′ ξ ζ → Q m′ b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sim∼ m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Dn δ a b (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV (tr< q δ) z′))) →
       ∀ i → Rq n k k′ (chainᵠ fe fc* (λ z → qwk a₁ (⇑ (cv* n)) (Ψ q ok e* p₁ (h ξ (Z* χ) (intoV q z)))) i) (chainᵠ fe′ fc* (λ z → qwk a₂ (⇑ (cv* n)) (Ψ (tr< q δ) ok′ e′* p₂ (h′ ξ′ (Z* ρ) (intoV (tr< q δ) z)))) i)

D-Ψ {H} δ qH ok e p ok′ e′ p′ et dz = rwk (RΩ̇ H et)
D-Ψ δ qH ok e p ok′ e′ p′ et (ds sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ (λ i q → sb i (tr< q qH))) (D-Ψ δ qH ok e p ok′ e′ p′ et r))
D-Ψ δ qH ok e p ok′ e′ p′ et (dl h) = rl (λ n → D-Ψ δ qH ok e p ok′ e′ p′ et (h n))
D-Ψ δ qH ok e p ok′ e′ p′ et (di d h) = ri d (λ x y dd → D-Ψ δ qH ok e p ok′ e′ p′ et (h x y dd))
D-Ψ δ qH ok e p ok′ e′ p′ et (dŝ d r h) = rŝ d (D-Ψ δ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → D-Ψ δ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
D-Ψ δ qH ok e p ok′ e′ p′ et (dĉ d dz′ dg r h) = rĉ d dz′ dg (D-Ψ δ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → D-Ψ δ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
D-Ψ δ qH ok e p ok′ e′ p′ et (dclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (D-Ψ δ qH ok e p ok′ e′ p′ et r)) (λ η η′ d → rwk (D-Ψ δ qH ok e p ok′ e′ p′ et (h η η′ d))))
D-Ψ δ qH ok e p ok′ e′ p′ et (dwkˡ {lc = lc} r) = rwkˡ (D-Ψ δ qH ok (λ i h r₁ → lc i r₁ (e i h r₁)) p ok′ e′ p′ et r)
D-Ψ δ qH ok e p ok′ e′ p′ et (dwkʳ {lc′ = lc′} r) = rwkʳ (D-Ψ δ qH ok e p ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)) p′ et r)
D-Ψ {H} δ qH ok e p ok′ e′ p′ et (dcl {n = n} s r h) with tri n H
... | tlt l = rcl {q = l} same (⊔∼ (∼ᶠ-refl Fl) s) (D-Ψ δ qH ok e p ok′ e′ p′ et r) (λ η η′ d → rwk (D-Ψ δ qH ok _ p ok′ _ p′ et (h η η′ d)))
... | teq refl = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ p _ p′ et) (D-Ψ δ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (D-Ψ δ qH _ _ _ _ _ _ et (h η η′ eη)))
... | tgt l = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (D-Ψ δ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (D-Ψ δ qH _ _ _ _ _ _ et (h η η′ eη)))
D-Ψ {H} {t = t} {t′} δ qH ok e p ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) with tri n H
... | tlt l = rΩ↓ {q = l} same ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
      (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ lz → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q u))) (Ψ (tr< qH δ) ok′ (e-lo ζ′ (inj₂ l) e′) p′ (h′ ξ′ ζ′ (intoV (tr< q δ) v)))) (sym (out-intoV l z)) (sym (out-intoV l z′))
         (D-Ψ δ qH ok (e-lo ζ (inj₂ l) e) p ok′ (e-lo ζ′ (inj₂ l) e′) p′ et (f ξ ξ′ ζ ζ′ d dc z z′ (outVq l lz)))))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p | <ᴵ-dec (ac′ (e′ n (inj₁ refl) (tr< q δ))) p′
...   | injᵃ (via d₁ s₁) | injᵃ (via d₂ s₂) =
  rΩ {r = s₁} {r′ = s₂} (≅ᴵ-trans (≅ᴵ-sym d₁) (≅ᴵ-trans ek d₂)) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q (tr⁻Q d₁ u)))) (Ψ (tr< qH δ) ok′ (e-lo ζ′ (inj₁ refl) e′) p′ (h′ ξ′ ζ′ (intoV (tr< q δ) (tr⁻Q d₂ v))))) (sym (out-intoU (<→◃ s₁) z)) (sym (out-intoU (<→◃ s₂) z′))
        (D-Ψ δ qH ok (e-lo ζ (inj₁ refl) e) p ok′ (e-lo ζ′ (inj₁ refl) e′) p′ et (f ξ ξ′ ζ ζ′ d dc _ _ (R-tr⁻ˡ d₁ (R-tr⁻ʳ d₂ (outRq (<→◃ s₁) l)))))))
...   | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
...   | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
...   | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
...   | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
...   | injᵇ _ | injᵇ _ = rl (λ i → rwk (D-Ψ δ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD δ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᵇ _ | injᶜ _ = rl (λ i → rwk (D-Ψ δ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD δ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᶜ _ | injᵇ _ = rl (λ i → rwk (D-Ψ δ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD δ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᶜ _ | injᶜ _ = rl (λ i → rwk (D-Ψ δ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD δ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
D-Ψ {H} {t = t} {t′} δ qH ok e p ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) | tgt l =
  rl (λ i → rwk (D-Ψ δ qH ok (e⁺ n ok e) p ok′ (e⁺ n ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD δ q ok (e⁺ n ok (e↑ l e)) (ac ((e↑ l e) n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↑ l e′)) (ac′ ((e↑ l e′) n (inj₁ refl) (tr< q δ))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))

chD {n = n} δ q ok e* p₁ ok′ e′* p₂ ek sξ c f zero = rwk (RΩ̇ n ek)
chD {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} δ q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′} {a₁} {a₂} {h} {h′} ek sξ c f (suc i) =
  rwk (D-Ψ δ q ok e* p₁ ok′ e′* p₂ ek (f ξ ξ′ (Z* χ) (Z* ρ) sξ (Z∼ (λ j r → c j (tr< r q))) _ _ (chD δ q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂} {h = h} {h′ = h′} ek sξ c f i)))
D→≈ᵠ : ∀ {m m′ a b φ χ ψ ρ w w′} {δ : m <ᴸ m′} {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Dn δ a b x x′ → (ok : Ok w) (e : Eh h₀ m w χ) (ok′ : Ok w′) (e′ : Eh h₀ m′ w′ ρ) → ψ̄ᵠ ok e x ≈ᴿ ψ̄ᵠ ok′ e′ x′
D→≈ᵠ dz ok e ok′ e′ = wkR _ _ r∅
D→≈ᵠ (ds s c r) ok e ok′ e′ = sucR (D→≈ᵠ r ok e ok′ e′)
D→≈ᵠ (dl h) ok e ok′ e′ = limR (λ n → D→≈ᵠ (h n) ok e ok′ e′)
D→≈ᵠ (di {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) ok e ok′ e′ = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ᵠ ok e (f x)} {H′ = λ x → ψ̄ᵠ ok′ e′ (f′ x)} d (λ x y dd → D→≈ᵠ (h x y dd) ok e ok′ e′)
D→≈ᵠ (dŝ d r h) ok e ok′ e′ = ŝR d (D→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → D→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
D→≈ᵠ (dĉ d dz′ dg r h) ok e ok′ e′ = ĉR d dz′ dg (D→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → D→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
D→≈ᵠ (dclo {t = t} {t′} {g} {g′} s r h) ok e ok′ e′ = cloR {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} {t′ = ψ̄ᵠ ok′ e′ t′} {g′ = λ η → ψ̄ᵠ ok′ e′ (g′ η)} s (D→≈ᵠ r ok e ok′ e′) (λ η η′ d → D→≈ᵠ (h η η′ d) ok e ok′ e′)
D→≈ᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} {δ = δ} (dcl {n = n} {κ₁ = κ₁} {κ₂ = κ₂} {q = q} {s = s₁} {s′ = s₂} s r h) ok e ok′ e′ =
  ŝR (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (D→≈ᵠ r ok e ok′ e′)
      (λ η d η′ d′ eη → D→≈ᵠ (h η η′ eη)
         (upd-ok n w ok (tt , λ x → lim 0 (proj₂ (evF B₁) x))) (λ i k r₁ → upd-ev n i w χ (evη κ₁ B₁ η d) (e i k r₁))
         (upd-ok n w′ ok′ (tt , λ x → lim 0 (proj₂ (evF B₂) x))) (λ i k r₁ → upd-ev n i w′ ρ (evη κ₂ B₂ η′ d′) (e′ i k r₁)))
  where
  B₁ = bound (κ₁ ⊔ fk zero) (s₁ (e n (Hi-0 n) q)) (zr ok n)
  B₂ = bound (κ₂ ⊔ fk zero) (s₂ (e′ n (Hi-0 n) (tr< q δ))) (zr ok′ n)
D→≈ᵠ (dwkˡ {le = le} {lc = lc} r) ok e ok′ e′ = wkR le (λ v → v) (D→≈ᵠ r ok (λ i h r₁ → lc i r₁ (e i h r₁)) ok′ e′)
D→≈ᵠ (dwkʳ {le′ = le′} {lc′ = lc′} r) ok e ok′ e′ = wkR (λ v → v) le′ (D→≈ᵠ r ok e ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)))
D→≈ᵠ {δ = δ} (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {q = q} {fe = fe} {fe′} {ac} {ac′} {h} {h′} ek s c f) ok e ok′ e′ =
  limR (λ i → wkR _ _ (D→≈ᵠ (f φ ψ (Z* χ) (Z* ρ) s (Z∼ (λ j r → c j (tr< r q))) _ _ (chD δ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↓ e′)) (ac′ (e↓ e′ n (inj₁ refl) (tr< q δ))) {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {h = h} {h′ = h′} ek s c f i)) ok (e⁺ n ok e) ok′ (e⁺ n ok′ e′)))
```
