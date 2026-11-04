# 跨段, 下一步 (一): `ψ̄ᵀ ∘ ι↓T` 与 `ψ̄ᵠ` 同值

> 入口 [CrossNext](CrossNext.lagda.md). **判决: HOLDS (编译过, 无条件).** 这是 [CrossM](CrossM.lagda.md) 报告的障碍 (a). 世界 $M$ 里 `Ω̇ m 0` 的计值, 与它经 `ι↓T` 放进数据树 `T₊` 再由 `ψ̄ᵀ` 计值, 同值:
>
> - `D→≈ᵠ`: 关系 `Dn` 蕴含 `ψ̄ᵠ ≈ᴿ ψ̄ᵀ`. `D-self`: `Ω̇ m 0` 与 `ι↓T (Ω̇ m 0)` 有 `Dn`.
> - `branch≈ e`: `Tᵠ end 0 ≈ᴿ ψ̄ᵀ ok′ e′ (stepT e)`, 对一切 `e : M₀ ⊂ M`, 一切证据.
> - `D-Ψ`: `Ψ` 与 `ΨT` 同值 (目标在低高度).
>
> 由 `LadderOrdDn`, `LadderOrdDnSelf` 机械改写. 差别: 右边换成 `T₊`, `tr< q δ` 消失 (`T₊` 的节点不带 $n<m$ 的证明, 比 `Dn` 简单), 证据换成 `EhT`, `EA`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdPos using (Code; Pos; cs; end; <ᴾ-tri; HB; _<ᴾ_)
module OCF.Align.CrossNextDn (M : Code) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ; intoˢ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ᶻ_; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound; bound-≅; evF)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Free.Base using (clash; r∅)
open import OCF.Align.LadderOrdBase
open import OCF.Align.LadderOrdTree (HB M)
open import OCF.Align.LadderOrdRel (HB M)
open RestrQ
open import OCF.Free.Eq using (_≅ˢ_)
open import OCF.Align.CrossMUp using (_⊂_)
open import OCF.Align.CrossMTop using (QT; t0; ts; ti; tŝ; tĉ; tclo; tcl; twk; tΩ↓; _∪ᵀ_; ι↓T; ΨT; ψ̄ᵀ; EhT; EA; e⁺ᵀ; e-loᵀ; e↑ᵀ; stepT) renaming (tl to tlᵀ)
```

## §1 关系

```agda
module _ {m : Ht} (a b : Ordᴵ) where
  data Dn : ∀ {φ χ ψ ρ} → Q m a φ χ → QT b M ψ ρ → Set where
    dz : ∀ {φ χ ψ ρ} → Dn {φ} {χ} {ψ} {ρ} q0 t0
    ds : ∀ {φ χ ψ ρ} {p : Q m a φ χ} {p′ : QT b M ψ ρ} → φ ∼ᶠ ψ → Sim∼ m χ ρ → Dn p p′ → Dn (qs p) (ts p′)
    dl : ∀ {φ χ ψ ρ} {F : ℕ → Q m a φ χ} {F′ : ℕ → QT b M ψ ρ} → (∀ n → Dn (F n) (F′ n)) → Dn (ql F) (tlᵀ F′)
    di : ∀ {φ χ ψ ρ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → Q m a φ χ} {f′ : Ordˢ j′ → QT b M ψ ρ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → Dn (f x) (f′ y)) → Dn (qi ac f) (ti ac′ f′)
    dŝ : ∀ {φ χ ψ ρ c₁ c₂} {t : Q m a φ χ} {t′ : QT b M ψ ρ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → QT b M ψ ρ} →
         c₁ ≅ᴵ c₂ → Dn t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Dn (g η e) (g′ η′ e′)) → Dn (qŝ c₁ t g) (tŝ c₂ t′ g′)
    dĉ : ∀ {φ χ ψ ρ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : Q m a φ χ} {o₀′ : QT b M ψ ρ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → QT b M ψ ρ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → Dn o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → Dn (o η e) (o′ η′ e′)) → Dn (qĉ c₁ z zg o₀ o) (tĉ c₂ z′ zg′ o₀′ o′)
    dclo : ∀ {φ χ ψ ρ} {t : Q m a (φ ⊔ fk zero) χ} {t′ : QT b M (ψ ⊔ fk zero) ρ} {g : (η : Ordᴵ) → Q m a (φ ⊔ fk η) χ} {g′ : (η : Ordᴵ) → QT b M (ψ ⊔ fk η) ρ} →
         φ ∼ᶠ ψ → Dn t t′ → (∀ η η′ → η ≅ᴵ η′ → Dn (g η) (g′ η′)) → Dn (qclo t g) (tclo t′ g′)
    dcl : ∀ {φ χ ψ ρ n κ₁ κ₂} {q : n <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : Q m a φ χ} {t′ : QT b M ψ ρ} {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → QT b M ψ (upd ρ n (κ₂ ⊔ fk η))} →
         κ₁ ∼ᶠ κ₂ → Dn t t′ → (∀ η η′ → η ≅ᴵ η′ → Dn (g η) (g′ η′)) → Dn (qcl q κ₁ s t g) (tcl n κ₂ s′ t′ g′)
    dwkˡ : ∀ {φ φ′ χ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {x : Q m a φ χ} {x′ : QT b M ψ ρ} → Dn x x′ → Dn (qwk le lc x) x′
    dwkʳ : ∀ {φ χ ψ ψ′ ρ ρ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub∞ ρ′ ρ} {x : Q m a φ χ} {x′ : QT b M ψ ρ} → Dn x x′ → Dn x (twk le′ lc′ x′)
    dΩ↓ : ∀ {φ χ ψ ρ n k k′} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Q n k′ ξ ζ → QT b M (ξ ⊔ ψ) (lo n ζ ∪ᵀ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Dn (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ z′)) → Dn (qΩ↓ q fe ac h) (tΩ↓ n fe′ ac′ h′)
```

## §2 折叠

```agda
D-Ψ : ∀ {H m a b t t′ φ χ ψ ρ w w′} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) (ok′ : Ok w′) (e′ : EhT H w′ ρ) (p′ : t′ <ᴵ w′ H) → t ≅ᴵ t′ → {x : Q m a φ χ} {x′ : QT b M ψ ρ} → Dn a b x x′ → Rq H t t′ (Ψ qH ok e p x) (ΨT H ok′ e′ p′ x′)
chD : ∀ {m a b n k k′ φ χ ψ ρ ξ ξ′ w w′} (q : n <ᴸ m) (ok : Ok w) (e* : Eh n m w (lo n (Z* χ) ∪ χ)) (p₁ : k <ᴵ w n) (ok′ : Ok w′) (e′* : EhT n w′ (lo n (Z* ρ) ∪ᵀ ρ)) (p₂ : k′ <ᴵ w′ n)
       {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Q n k′ ξ ζ → QT b M (ξ ⊔ ψ) (lo n ζ ∪ᵀ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sim∼ m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Dn a b (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ z′)) →
       ∀ i → Rq n k k′ (chainᵠ fe fc* (λ z → qwk a₁ (⇑ (cv* n)) (Ψ q ok e* p₁ (h ξ (Z* χ) (intoV q z)))) i) (chainᵠ fe′ fc* (λ z → qwk a₂ (⇑ (cv* n)) (ΨT n ok′ e′* p₂ (h′ ξ′ (Z* ρ) z))) i)

D-Ψ {H} qH ok e p ok′ e′ p′ et dz = rwk (RΩ̇ H et)
D-Ψ qH ok e p ok′ e′ p′ et (ds sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ (λ i q → sb i (tr< q qH))) (D-Ψ qH ok e p ok′ e′ p′ et r))
D-Ψ qH ok e p ok′ e′ p′ et (dl h) = rl (λ n → D-Ψ qH ok e p ok′ e′ p′ et (h n))
D-Ψ qH ok e p ok′ e′ p′ et (di d h) = ri d (λ x y dd → D-Ψ qH ok e p ok′ e′ p′ et (h x y dd))
D-Ψ qH ok e p ok′ e′ p′ et (dŝ d r h) = rŝ d (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → D-Ψ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
D-Ψ qH ok e p ok′ e′ p′ et (dĉ d dz′ dg r h) = rĉ d dz′ dg (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → D-Ψ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
D-Ψ qH ok e p ok′ e′ p′ et (dclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (D-Ψ qH ok e p ok′ e′ p′ et r)) (λ η η′ d → rwk (D-Ψ qH ok e p ok′ e′ p′ et (h η η′ d))))
D-Ψ qH ok e p ok′ e′ p′ et (dwkˡ {lc = lc} r) = rwkˡ (D-Ψ qH ok (λ i h r₁ → lc i r₁ (e i h r₁)) p ok′ e′ p′ et r)
D-Ψ qH ok e p ok′ e′ p′ et (dwkʳ {lc′ = lc′} r) = rwkʳ (D-Ψ qH ok e p ok′ (λ i h → lc′ i (e′ i h)) p′ et r)
D-Ψ {H} qH ok e p ok′ e′ p′ et (dcl {n = n} s r h) with <ᴾ-tri n H
... | tlt l = rcl {q = l} same (⊔∼ (∼ᶠ-refl Fl) s) (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η η′ d → rwk (D-Ψ qH ok _ p ok′ _ p′ et (h η η′ d)))
... | teq refl = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ p _ p′ et) (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (D-Ψ qH _ _ _ _ _ _ et (h η η′ eη)))
... | tgt l = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (D-Ψ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (D-Ψ qH _ _ _ _ _ _ et (h η η′ eη)))
D-Ψ {H} {t = t} {t′} qH ok e p ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) with <ᴾ-tri n H
... | tlt l = rΩ↓ {q = l} same ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
      (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ lz → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q u))) (ΨT H ok′ (e-loᵀ ζ′ (inj₂ l) e′) p′ (h′ ξ′ ζ′ v))) (sym (out-intoV l z)) (sym (out-intoV l z′))
         (D-Ψ qH ok (e-lo ζ (inj₂ l) e) p ok′ (e-loᵀ ζ′ (inj₂ l) e′) p′ et (f ξ ξ′ ζ ζ′ d dc z z′ (outVq l lz)))))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p | <ᴵ-dec (ac′ (e′ n (inj₁ refl))) p′
...   | injᵃ (via d₁ s₁) | injᵃ (via d₂ s₂) =
  rΩ {r = s₁} {r′ = s₂} (≅ᴵ-trans (≅ᴵ-sym d₁) (≅ᴵ-trans ek d₂)) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q (tr⁻Q d₁ u)))) (ΨT H ok′ (e-loᵀ ζ′ (inj₁ refl) e′) p′ (h′ ξ′ ζ′ (tr⁻Q d₂ v)))) (sym (out-intoU (<→◃ s₁) z)) (sym (out-intoU (<→◃ s₂) z′))
        (D-Ψ qH ok (e-lo ζ (inj₁ refl) e) p ok′ (e-loᵀ ζ′ (inj₁ refl) e′) p′ et (f ξ ξ′ ζ ζ′ d dc _ _ (R-tr⁻ˡ d₁ (R-tr⁻ʳ d₂ (outRq (<→◃ s₁) l)))))))
...   | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
...   | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
...   | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
...   | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
...   | injᵇ _ | injᵇ _ = rl (λ i → rwk (D-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ᵀ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ᵀ n ok′ e′) (ac′ (e′ n (inj₁ refl))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᵇ _ | injᶜ _ = rl (λ i → rwk (D-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ᵀ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ᵀ n ok′ e′) (ac′ (e′ n (inj₁ refl))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᶜ _ | injᵇ _ = rl (λ i → rwk (D-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ᵀ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ᵀ n ok′ e′) (ac′ (e′ n (inj₁ refl))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
...   | injᶜ _ | injᶜ _ = rl (λ i → rwk (D-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ᵀ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ᵀ n ok′ e′) (ac′ (e′ n (inj₁ refl))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))
D-Ψ {H} {t = t} {t′} qH ok e p ok′ e′ p′ et (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) | tgt l =
  rl (λ i → rwk (D-Ψ qH ok (e⁺ n ok e) p ok′ (e⁺ᵀ n ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok (e↑ l e)) (ac ((e↑ l e) n (inj₁ refl) q)) ok′ (e⁺ᵀ n ok′ (e↑ᵀ l e′)) (ac′ ((e↑ᵀ l e′) n (inj₁ refl))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i))))

chD {n = n} q ok e* p₁ ok′ e′* p₂ ek sξ c f zero = rwk (RΩ̇ n ek)
chD {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′} {a₁} {a₂} {h} {h′} ek sξ c f (suc i) =
  rwk (D-Ψ q ok e* p₁ ok′ e′* p₂ ek (f ξ ξ′ (Z* χ) (Z* ρ) sξ (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂} {h = h} {h′ = h′} ek sξ c f i)))

```

## §3 计值

```agda
D→≈ᵠ : ∀ {m a b φ χ ψ ρ w w′} {x : Q m a φ χ} {x′ : QT b M ψ ρ} → Dn a b x x′ → (ok : Ok w) (e : Eh h₀ m w χ) (ok′ : Ok w′) (e′ : EA w′ ρ) → ψ̄ᵠ ok e x ≈ᴿ ψ̄ᵀ ok′ e′ x′
D→≈ᵠ dz ok e ok′ e′ = wkR _ _ r∅
D→≈ᵠ (ds s c r) ok e ok′ e′ = sucR (D→≈ᵠ r ok e ok′ e′)
D→≈ᵠ (dl h) ok e ok′ e′ = limR (λ n → D→≈ᵠ (h n) ok e ok′ e′)
D→≈ᵠ (di {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) ok e ok′ e′ = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ᵠ ok e (f x)} {H′ = λ x → ψ̄ᵀ ok′ e′ (f′ x)} d (λ x y dd → D→≈ᵠ (h x y dd) ok e ok′ e′)
D→≈ᵠ (dŝ d r h) ok e ok′ e′ = ŝR d (D→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → D→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
D→≈ᵠ (dĉ d dz′ dg r h) ok e ok′ e′ = ĉR d dz′ dg (D→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → D→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
D→≈ᵠ (dclo {t = t} {t′} {g} {g′} s r h) ok e ok′ e′ = cloR {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} {t′ = ψ̄ᵀ ok′ e′ t′} {g′ = λ η → ψ̄ᵀ ok′ e′ (g′ η)} s (D→≈ᵠ r ok e ok′ e′) (λ η η′ d → D→≈ᵠ (h η η′ d) ok e ok′ e′)
D→≈ᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} (dcl {n = n} {κ₁ = κ₁} {κ₂ = κ₂} {q = q} {s = s₁} {s′ = s₂} s r h) ok e ok′ e′ =
  ŝR (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (D→≈ᵠ r ok e ok′ e′)
      (λ η d η′ d′ eη → D→≈ᵠ (h η η′ eη)
         (upd-ok n w ok (tt , λ x → lim 0 (proj₂ (evF B₁) x))) (λ i k r₁ → upd-ev n i w χ (evη κ₁ B₁ η d) (e i k r₁))
         (upd-ok n w′ ok′ (tt , λ x → lim 0 (proj₂ (evF B₂) x))) (λ i → upd-ev n i w′ ρ (evη κ₂ B₂ η′ d′) (e′ i)))
  where
  B₁ = bound (κ₁ ⊔ fk zero) (s₁ (e n (Hi-0 n) q)) (zr ok n)
  B₂ = bound (κ₂ ⊔ fk zero) (s₂ (e′ n)) (zr ok′ n)
D→≈ᵠ (dwkˡ {le = le} {lc = lc} r) ok e ok′ e′ = wkR le (λ v → v) (D→≈ᵠ r ok (λ i h r₁ → lc i r₁ (e i h r₁)) ok′ e′)
D→≈ᵠ (dwkʳ {le′ = le′} {lc′ = lc′} r) ok e ok′ e′ = wkR (λ v → v) le′ (D→≈ᵠ r ok e ok′ (λ i → lc′ i (e′ i)))
D→≈ᵠ {ρ = ρ} (dΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {q = q} {fe = fe} {fe′} {ac} {ac′} {h} {h′} ek s c f) ok e ok′ e′ =
  limR (λ i → wkR _ _ (D→≈ᵠ (f φ ψ (Z* χ) (Z* ρ) s (Z∼ (λ j r → c j (tr< r q))) _ _ (chD q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) ok′ (e⁺ᵀ n ok′ (λ j′ _ → e′ j′)) (ac′ (e′ n)) {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {h = h} {h′ = h′} ek s c f i)) ok (e⁺ n ok e) ok′ (λ j → Ev-lo {Z* ρ} n j (ok′ j , e′ j) , e′ j)))

```

## §4 第 0 行

```agda
Sim-dd : ∀ {m} {χ ρ : Fv} {x y w} n → Sim∼ n χ ρ → x ∼ᶠ y → Sim∼ m (cap χ n x) (cap (cap ρ n y) m w)
Sim-dd {m} {χ} {ρ} {x} {y} {w} n s c i r = subst (cap χ n x i ∼ᶠ_) (sym (cap-lt (cap ρ n y) w r)) (cap∼ n s c i r)

D-ι↓ : ∀ {n m k k′ α α′ α₁ φ ψ χ ρ} (q₁ : n <ᴸ m) → k ≅ᴵ k′ → {x : Q n k φ χ} {x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Dn α α′ (ι↓ q₁ x) (ι↓T {α = α′} (ι↓ {α = α₁} q₁ x′))
D-ι↓ q₁ ek rz = dz
D-ι↓ {n = n} q₁ ek (rs sa sb r) = ds sa (Sim-dd n sb (flo-∼ ek)) (D-ι↓ q₁ ek r)
D-ι↓ q₁ ek (rl h) = dl (λ n → D-ι↓ q₁ ek (h n))
D-ι↓ q₁ ek (ri e h) = di e (λ x y d → D-ι↓ q₁ ek (h x y d))
D-ι↓ q₁ ek (rŝ e r h) = dŝ e (D-ι↓ q₁ ek r) (λ η ee η′ e′ d → D-ι↓ q₁ ek (h η ee η′ e′ d))
D-ι↓ q₁ ek (rĉ e dz′ dg r h) = dĉ e dz′ dg (D-ι↓ q₁ ek r) (λ η ee η′ e′ d → D-ι↓ q₁ ek (h η ee η′ e′ d))
D-ι↓ q₁ ek (rclo s r h) = dclo s (D-ι↓ q₁ ek r) (λ η η′ d → D-ι↓ q₁ ek (h η η′ d))
D-ι↓ q₁ ek (rcl {q = q} same s r h) = dcl {q = tr< q q₁} s (D-ι↓ q₁ ek r) (λ η η′ d → dwkˡ (dwkʳ (dwkʳ (D-ι↓ q₁ ek (h η η′ d)))))
D-ι↓ q₁ ek (rwkˡ r) = dwkˡ (D-ι↓ q₁ ek r)
D-ι↓ q₁ ek (rwkʳ r) = dwkʳ (D-ι↓ q₁ ek r)
D-ι↓ {n = n} {α = α} {α′ = α′} {α₁ = α₁} q₁ ek (rΩ↓ {q = q} {h = h} {h′ = h′} same ei s c f) =
  dΩ↓ {q = tr< q q₁} ei s (Sim-dd n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → dwkˡ (dwkʳ (dwkʳ
    (subst₂ (λ u v → Dn α α′ (ι↓ q₁ (h ξ ζ (intoV q u))) (ι↓T {α = α′} (ι↓ {α = α₁} q₁ (h′ ξ′ ζ′ (intoV q v)))))
       (sym (out-intoV (tr< q q₁) z))
       (sym (out-intoV (tr< q q₁) z′))
       (D-ι↓ q₁ ek (f ξ ξ′ ζ ζ′ d dc dc z z′ (intoVq q l)))))))
D-ι↓ {n = n} {α = α} {α′ = α′} {α₁ = α₁} q₁ ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ei s c f) =
  dΩ↓ {q = q₁} ei s (Sim-dd n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → dwkˡ (dwkʳ (dwkʳ
    (subst₂ (λ u v → Dn α α′ (ι↓ q₁ (h ξ ζ (intoU (<→◃ r) u))) (ι↓T {α = α′} (ι↓ {α = α₁} q₁ (h′ ξ′ ζ′ (intoU (<→◃ r′) v)))))
       (sym (out-intoV q₁ z))
       (sym (out-intoV q₁ z′))
       (D-ι↓ q₁ ek (f ξ ξ′ ζ ζ′ d dc z z′ (intoRq (<→◃ r) l)))))))
D-ι↓ q₁ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = dwkˡ (dwkʳ (D-ι↓ q₁ ea l))
D-ι↓ q₁ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = dwkˡ (dwkʳ (D-ι↓ q₁ ea l))

D-tl : ∀ {c c′ α₁ k₁ k₂ χ ρ} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       a ≅ˢ b → Dn {m = h₀} c c′ (tl {χ = χ} (flo k₁) cv a) (ι↓T {n = h₀} {k = α₁} (tl {χ = ρ} (flo k₂) cv′ b))
D-tl z≅ = dz
D-tl (s≅ le e) = ds (flo-∼ le) (λ i q → ⊥-elim (no< q)) (D-tl e)
D-tl (l≅ h) = dl (λ n → D-tl (h n))
D-tl (lᵢ≅ {p = q} e h) = di e (λ x y dd → D-tl (h x y (≅→Rˢ (<→◃ q) dd)))
D-tl {k₁ = suc k′} (upˡ {r = zero} d) = dwkˡ (D-tl d)
D-tl {k₁ = lim f s} (upˡ {r = self n} d) = dwkˡ (D-tl d)
D-tl {k₂ = suc k′} (upʳ {r = zero} d) = dwkʳ (D-tl d)
D-tl {k₂ = lim f s} (upʳ {r = self n} d) = dwkʳ (D-tl d)
D-tl {k₁ = zero} {k₂ = zero} (ŝ≅ k ec et eg) =
  dĉ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl {k₁ = zero} {k₂ = suc _}   (ŝ≅ k ec et eg) = ⊥-elim (tf k)
D-tl {k₁ = zero} {k₂ = lim _ _} (ŝ≅ k ec et eg) = ⊥-elim (tf k)
D-tl {k₁ = suc _}   {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
D-tl {k₁ = lim _ _} {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
D-tl {k₁ = suc _} {k₂ = suc _} (ŝ≅ k ec et eg) = dŝ ec (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl {k₁ = suc _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = dŝ ec (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl {k₁ = lim _ _} {k₂ = suc _} (ŝ≅ k ec et eg) = dŝ ec (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl {k₁ = lim _ _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = dŝ ec (D-tl et) (λ η e η′ e′ eη → D-tl (eg η e η′ e′ eη))
D-tl (ĉ≅ ec dt dg eo eO) = dĉ ec dt dg (D-tl eo) (λ η e η′ e′ eη → D-tl (eO η e η′ e′ eη))

D-tlΩ : ∀ {c c′ α₁ η η′ φ φ′ χ ρ} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ → Dn {m = h₀} c c′ (tl {χ = χ} φ cv (Ωˢ η)) (ι↓T {n = h₀} {k = α₁} (tl {χ = ρ} φ′ cv′ (Ωˢ η′)))
D-tlΩ z≅ s = ds s (λ i q → ⊥-elim (no< q)) dz
D-tlΩ (s≅ e) s = di e (λ x y d → dwkˡ (dwkʳ (D-tl d)))
D-tlΩ (l≅ h) s = dl (λ n → dwkˡ (dwkʳ (D-tl (Ωˢ-≅ (h n)))))

D-rowL : ∀ {m α} F (qs₁ : ∀ i → F i <ᴸ m) → ∀ i → Dn zero α (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i) (ι↓T {k = zero} (rowL F qs₁ (λ j → ΩI m (qs₁ j)) i))
D-rowL F qs₁ zero = dwkˡ (dwkʳ (ds fz∼ (λ i q → subst (fz ∼ᶠ_) (sym (cap-lt (κ fz) fz q)) fz∼) dz))
D-rowL {m} {α = α} F qs₁ (suc i) =
  subst (λ X → Dn zero α (stepL (qs₁ i) X) (ι↓T {k = zero} (stepL (qs₁ i) X))) (sym (ΩI≡ (qs₁ i)))
    (dwkˡ (dwkʳ (D-ι↓ (qs₁ i) z≅ (RΩ̇ (F i) z≅))))

D-row : ∀ {m α} (v : View _<ᴸ_ h₀ m) → Dn zero α (rowV m (ΩI m) v) (ι↓T {k = zero} (rowV m (ΩI m) v))
D-row base =
  dclo (∼ᶠ-refl fz)
    (D-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
    (λ η η′ eη → D-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
D-row {m} {α = α} (clos {n = n} q) =
  subst (λ X → Dn zero α (rowC q X) (ι↓T {k = zero} (rowC q X))) (sym (ΩI≡ q))
    (dcl {q = q} (∼ᶠ-refl fz)
      (dwkˡ (dwkʳ (D-ι↓ q (s≅ z≅) (RΩ̇ n (s≅ z≅)))))
      (λ η η′ eη → dwkˡ (dwkʳ (dwkʳ (D-ι↓ q eη (RΩ̇ n eη))))))
D-row (chain F qs₁) = dl (D-rowL F qs₁)

D-self : ∀ {m α} → Dn zero α (Ω̇ m zero) (ι↓T {k = zero} (Ω̇ m zero))
D-self {m} = D-row (view m)

```

## §5 分支

```agda
branch≈ : ∀ {M₀} (e : M₀ ⊂ M) {w′} (ok′ : Ok w′) (e′ : EA w′ _) → Tᵠ end zero ≈ᴿ ψ̄ᵀ ok′ e′ (stepT e)
branch≈ e ok′ e′ = D→≈ᵠ (dwkʳ D-self) ok₀ (λ i h r → ok₀ i) ok′ e′
```
