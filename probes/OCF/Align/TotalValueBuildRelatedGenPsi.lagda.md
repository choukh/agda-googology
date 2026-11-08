# 原 ψᵠ 的获准反馈生成闭包

反馈链逐步使用原 Ω 回调，坐标自相关从输入 Rq 证书取得。
保留分支按原 res 层同构反送，未量化所有 raw 坐标的自相关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRelatedGenPsi (𝕊 : HtB) where
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Tree using (Fl; dupr2)
open import OCF.Free.Floor using (Ev; fk; _⊔_; _∼ᶠ_; ∼ᶠ-refl)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdRel 𝕊
open import OCF.Align.TotalValueBuildRecoverRun 𝕊 using (ht-eq)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import OCF.Align.TotalValueBuildRelatedGenIf 𝕊
open import OCF.Align.TotalValueBuildRelatedGenUp 𝕊 using (C)
open import OCF.Align.TotalValueBuildRelatedGenFloor 𝕊 using (omega-gen)
open import OCF.Align.TotalValueBuildRelatedGenTransport 𝕊 using (transport-back)
open import OCF.Align.TotalValueBuildRelatedGenOps 𝕊 using (repeat-core; chain-gen)

subst-in-out : ∀ {ℓ ℓ′} {A : Set ℓ} {P : A → Set ℓ′} {a b : A}
  (e : a ≡ b) (x : P a) → subst P (sym e) (subst P e x) ≡ x
subst-in-out refl x = refl
into-outV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} (z : Vs m q k ξ ζ) → intoV q (outV q z) ≡ z
into-outV {m} q {k} {ξ} {ζ} z = subst-in-out {P = λ X → X k ξ ζ} (Rec-β XQ QV m q) z

unwk-left : ∀ {m a b φ χ ψ ρ φ′ χ′} {x : Q m a φ χ} {y : Q m b ψ ρ}
  {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} →
  Rq m a b (qwk le lc x) y → Rq m a b x y
unwk-left (rwkˡ r) = r
unwk-left (rwkʳ r) = rwkʳ (unwk-left r)
unwk-right : ∀ {m a b φ χ ψ ρ ψ′ ρ′} {x : Q m a φ χ} {y : Q m b ψ ρ}
  {le : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc : Sub m ρ′ ρ} →
  Rq m a b x (qwk le lc y) → Rq m a b x y
unwk-right (rwkˡ r) = rwkˡ (unwk-right r)
unwk-right (rwkʳ r) = r

cl-head : ∀ {m a b φ χ ψ ρ n n′ κ₁ κ₂} {r : n <ᴸ m} {r′ : n′ <ᴸ m}
  {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)}
  {s′ : ∀ {ℓ} → Ev ℓ (ρ n′) → Ev ℓ (κ₂ ⊔ fk zero)}
  {t : Q m a φ χ} {t′ : Q m b ψ ρ}
  {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))}
  {g′ : (η : Ordᴵ) → Q m b ψ (upd ρ n′ (κ₂ ⊔ fk η))} →
  Rq m a b (qcl r κ₁ s t g) (qcl r′ κ₂ s′ t′ g′) → Rq m a b t t′
cl-head (rcl eqn sf rt rg) = rt
cl-branch : ∀ {m a b φ χ ψ ρ n n′ κ₁ κ₂} {r : n <ᴸ m} {r′ : n′ <ᴸ m}
  {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)}
  {s′ : ∀ {ℓ} → Ev ℓ (ρ n′) → Ev ℓ (κ₂ ⊔ fk zero)}
  {t : Q m a φ χ} {t′ : Q m b ψ ρ}
  {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))}
  {g′ : (η : Ordᴵ) → Q m b ψ (upd ρ n′ (κ₂ ⊔ fk η))} →
  Rq m a b (qcl r κ₁ s t g) (qcl r′ κ₂ s′ t′ g′) →
  ∀ η η′ → η ≅ᴵ η′ → Rq m a b (g η) (g′ η′)
cl-branch (rcl eqn sf rt rg) = rg

module Down {m a b φ χ ψ ρ n n′ k k′} {r : n <ᴸ m} {r′ : n′ <ᴸ m}
  {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl}
  {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n′) → k′ <ᴵ L}
  {h : ∀ ξ ζ → Vs m r k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)}
  {h′ : ∀ ξ ζ → Vs m r′ k′ ξ ζ → Q m b (ξ ⊔ ψ) (lo n′ ζ ∪ ρ)} where
  Feed : n ≡ n′ → Set
  Feed eq = ∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ →
    (z : Q n k ξ ζ) (z′ : Q n′ k′ ξ′ ζ′) →
    Rq n k k′ z (subst (λ j → Q j k′ ξ′ ζ′) (sym eq) z′) →
    Rq m a b (h ξ ζ (intoV r z)) (h′ ξ′ ζ′ (intoV r′ z′))
  inspect : Rq m a b (qΩ↓ r fe ac h) (qΩ↓ r′ fe′ ac′ h′) → Σ (n ≡ n′) Feed
  inspect (rΩ↓ eqn ek sf sc rh) = refl , λ ξ ξ′ ζ ζ′ d dc z z′ rz →
    rh ξ ξ′ ζ ζ′ d dc dc z z′ (intoVq _ rz)

self-feed : ∀ {m a φ χ n k} {r : n <ᴸ m}
  {fe : ∀ {L} → Ev L φ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L}
  {h : ∀ ξ ζ → Vs m r k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} →
  Rq m a a (qΩ↓ r fe ac h) (qΩ↓ r fe ac h) →
  ∀ ξ ζ (z : Q n k ξ ζ) → Rq n k k z z →
  Rq m a a (h ξ ζ (intoV r z)) (h ξ ζ (intoV r z))
self-feed {r = r} {fe} {ac} {h} rx ξ ζ z rzz =
  let v = Down.inspect rx
      eq = proj₁ v
      rr = proj₂ v
  in
  subst (Down.Feed {r = r} {r′ = r} {fe = fe} {fe′ = fe} {ac = ac} {ac′ = ac} {h = h} {h′ = h})
    (Decidable⇒UIP.≡-irrelevant ht-eq eq refl) rr
    ξ ξ ζ ζ (∼ᶠ-refl ξ) (λ i p → ∼ᶠ-refl _) z z rzz

mutual
  psi-gen : ∀ {m a t φ χ} (q : t <ᴵ a) {x : Q m a φ χ} →
    Gen m a x → Gen m t (ψᵠ q x)
  psi-gen q {x} (rx , gx) = R-ψᵠ q q (≅ᴵ-refl _) rx , psi-core q x rx gx

  psi-core : ∀ {m a t φ χ} (q : t <ᴵ a) (x : Q m a φ χ) →
    Rq m a a x x → C m a x → C m t (ψᵠ q x)
  psi-core {m} {t = t} q q0 rx gx = proj₂ (omega-gen m t)
  psi-core q (qs x) (rs sf sc rx) gx = λ n → repeat-core (psi-core q x rx gx) n
  psi-core q (ql f) (rl rf) gf = λ i → psi-core q (f i) (rf i) (gf i)
  psi-core q (qi ac f) (ri ej rf) gf = λ x sx → psi-core q (f x) (rf x x sx) (gf x sx)
  psi-core q (qŝ c t g) (rŝ ec rt rg) (gt , gg) =
    psi-core q t rt gt , (λ η d → psi-core q (g η d) (rg η d η d (≅ᴵ-refl η)) (gg η d))
  psi-core q (qĉ c t g o h) (rĉ ec st sg ro rh) (st′ , sg′ , go , gh) =
    st′ , sg′ , psi-core q o ro go , (λ η d → psi-core q (h η d) (rh η d η d (≅ᴵ-refl η)) (gh η d))
  psi-core q (qclo t g) (rclo sf rt rg) (gt , gg) =
    psi-core q t rt gt , (λ η → psi-core q (g η) (rg η η (≅ᴵ-refl η)) (gg η))
  psi-core q (qcl r ψ s t g) rx (gt , gg) =
    psi-core q t (cl-head rx) gt , (λ η → psi-core q (g η) (cl-branch rx η η (≅ᴵ-refl η)) (gg η))
  psi-core q (qwk le lc x) rx gx = psi-core q x (unwk-right (unwk-left rx)) gx
  psi-core {m} q (qΩ↓ r fe ac h) rx gh = λ ξ ζ z gz →
    subst (λ z′ → C m _ (ψᵠ q (h ξ ζ z′))) (into-outV r z)
      (psi-core q (h ξ ζ (intoV r (outV r z)))
        (self-feed rx ξ ζ (outV r z) (proj₁ (height-out r gz)))
        (gh ξ ζ (intoV r (outV r z))
          (subst (GHeight m r) (sym (out-intoV r (outV r z))) gz)))
  psi-core {m} {φ = φ} {χ} q (qΩ fe r h) rx@(rΩ ek sf sc rh) gh with <ᴵ-dec r q
  ... | injᵃ (via e s) = λ ξ ζ z gz →
    let low = transport-back e (low-out (<→◃ s) gz)
        v = tr⁻Q e (outU (<→◃ s) z)
    in psi-core q (h ξ ζ (intoU (<→◃ r) v))
      (rh ξ ξ ζ ζ (∼ᶠ-refl ξ) (λ i p → ∼ᶠ-refl _) v v (intoRq (<→◃ r) (proj₁ low)))
      (gh ξ ζ (intoU (<→◃ r) v)
        (subst (Low m (GHeight m) _ (<→◃ r)) (sym (out-intoU (<→◃ r) v)) (low-in (<→◃ r) low)))
  ... | injᵇ ee = λ n →
    let
      run : (z : Q m _ (Fl ⊔ φ) (Z* χ)) → Gen m _ z →
        Gen m _ (qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z))))
      run z gz =
        let hz = h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)
            rg = rh _ _ _ _ (∼ᶠ-refl _) (λ i p → ∼ᶠ-refl _) z z (intoRq (<→◃ r) (proj₁ gz))
            cg = gh _ _ (intoU (<→◃ r) z)
              (subst (Low m (GHeight m) _ (<→◃ r)) (sym (out-intoU (<→◃ r) z)) (low-in (<→◃ r) gz))
        in rwk (R-ψᵠ r r (≅ᴵ-refl _) rg) , psi-core r hz rg cg
      z = chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n
      gz = chain-gen proj₁ fc* _ run n
    in psi-core q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z))
      (rh _ _ _ _ (∼ᶠ-refl _) (λ i p → ∼ᶠ-refl _) z z (intoRq (<→◃ r) (proj₁ gz)))
      (gh _ _ (intoU (<→◃ r) z)
        (subst (Low m (GHeight m) _ (<→◃ r)) (sym (out-intoU (<→◃ r) z)) (low-in (<→◃ r) gz)))
  ... | injᶜ ee = λ n →
    let
      run : (z : Q m _ (Fl ⊔ φ) (Z* χ)) → Gen m _ z →
        Gen m _ (qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z))))
      run z gz =
        let hz = h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)
            rg = rh _ _ _ _ (∼ᶠ-refl _) (λ i p → ∼ᶠ-refl _) z z (intoRq (<→◃ r) (proj₁ gz))
            cg = gh _ _ (intoU (<→◃ r) z)
              (subst (Low m (GHeight m) _ (<→◃ r)) (sym (out-intoU (<→◃ r) z)) (low-in (<→◃ r) gz))
        in rwk (R-ψᵠ r r (≅ᴵ-refl _) rg) , psi-core r hz rg cg
      z = chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n
      gz = chain-gen proj₁ fc* _ run n
    in psi-core q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z))
      (rh _ _ _ _ (∼ᶠ-refl _) (λ i p → ∼ᶠ-refl _) z z (intoRq (<→◃ r) (proj₁ gz)))
      (gh _ _ (intoU (<→◃ r) z)
        (subst (Low m (GHeight m) _ (<→◃ r)) (sym (out-intoU (<→◃ r) z)) (low-in (<→◃ r) gz)))
  psi-core q (omk r z x) (rob ek rz′ rx) (gz , gx , rel) = psi-core q x rx gx
```
