# 新跨层顶 Ω 关系

原 Dn 只配对已有低节点。本篇另立 Cross，新增原顶节点与同高度
下降节点的配对。低坐标条件逐字为原 Rq，并非任意 raw 自相关。
此合同覆盖可实填的回调域；不宣称全部 Balanced 已自动满足。
所有高度都在原 HtB 的字面共同段中，原程序与 Dn 均不改。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildRecoverIf (𝕊 : HtB) where
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

module _ {m m′ : Ht} (δ : m <ᴸ m′) (a b : Ordᴵ) where
  data Cross : ∀ {φ χ ψ ρ} → Q m a φ χ → Q m′ b ψ ρ → Set where
    dz : ∀ {φ χ ψ ρ} → Cross {φ} {χ} {ψ} {ρ} q0 q0
    ds : ∀ {φ χ ψ ρ} {p : Q m a φ χ} {p′ : Q m′ b ψ ρ} → φ ∼ᶠ ψ → Sim∼ m χ ρ → Cross p p′ → Cross (qs p) (qs p′)
    dl : ∀ {φ χ ψ ρ} {F : ℕ → Q m a φ χ} {F′ : ℕ → Q m′ b ψ ρ} → (∀ n → Cross (F n) (F′ n)) → Cross (ql F) (ql F′)
    di : ∀ {φ χ ψ ρ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → Q m a φ χ} {f′ : Ordˢ j′ → Q m′ b ψ ρ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → Cross (f x) (f′ y)) → Cross (qi ac f) (qi ac′ f′)
    dŝ : ∀ {φ χ ψ ρ c₁ c₂} {t : Q m a φ χ} {t′ : Q m′ b ψ ρ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q m′ b ψ ρ} →
         c₁ ≅ᴵ c₂ → Cross t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Cross (g η e) (g′ η′ e′)) → Cross (qŝ c₁ t g) (qŝ c₂ t′ g′)
    dĉ : ∀ {φ χ ψ ρ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : Q m a φ χ} {o₀′ : Q m′ b ψ ρ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q m′ b ψ ρ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → Cross o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → Cross (o η e) (o′ η′ e′)) → Cross (qĉ c₁ z zg o₀ o) (qĉ c₂ z′ zg′ o₀′ o′)
    dclo : ∀ {φ χ ψ ρ} {t : Q m a (φ ⊔ fk zero) χ} {t′ : Q m′ b (ψ ⊔ fk zero) ρ} {g : (η : Ordᴵ) → Q m a (φ ⊔ fk η) χ} {g′ : (η : Ordᴵ) → Q m′ b (ψ ⊔ fk η) ρ} →
         φ ∼ᶠ ψ → Cross t t′ → (∀ η η′ → η ≅ᴵ η′ → Cross (g η) (g′ η′)) → Cross (qclo t g) (qclo t′ g′)
    dcl : ∀ {φ χ ψ ρ n κ₁ κ₂} {q : n <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : Q m a φ χ} {t′ : Q m′ b ψ ρ} {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → Q m′ b ψ (upd ρ n (κ₂ ⊔ fk η))} →
         κ₁ ∼ᶠ κ₂ → Cross t t′ → (∀ η η′ → η ≅ᴵ η′ → Cross (g η) (g′ η′)) → Cross (qcl q κ₁ s t g) (qcl (tr< q δ) κ₂ s′ t′ g′)
    dwkˡ : ∀ {φ φ′ χ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Cross x x′ → Cross (qwk le lc x) x′
    dwkʳ : ∀ {φ χ ψ ψ′ ρ ρ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub m′ ρ′ ρ} {x : Q m a φ χ} {x′ : Q m′ b ψ ρ} → Cross x x′ → Cross x (qwk le′ lc′ x′)
    dΩ↓ : ∀ {φ χ ψ ρ n k k′} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs m′ (tr< q δ) k′ ξ ζ → Q m′ b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → Rq n k k′ z z′ → Cross (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV (tr< q δ) z′))) → Cross (qΩ↓ q fe ac h) (qΩ↓ (tr< q δ) fe′ ac′ h′)
    dΩtop : ∀ {φ χ ψ ρ k k′} {r : k <ᴵ a}
          {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl}
          {ac′ : ∀ {L} → Ev L (ρ m) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m a (ξ ⊔ φ) (lo m ζ ∪ χ)}
          {h′ : ∀ ξ ζ → Vs m′ δ k′ ξ ζ → Q m′ b (ξ ⊔ ψ) (lo m ζ ∪ ρ)} →
          k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ m ζ ζ′ →
            (z : Q m k ξ ζ) (z′ : Q m k′ ξ′ ζ′) → Rq m k k′ z z′ →
            Cross (h ξ ζ (intoU (<→◃ r) z)) (h′ ξ′ ζ′ (intoV δ z′))) →
          Cross (qΩ fe r h) (qΩ↓ δ fe′ ac′ h′)
    dmark : ∀ {φ χ ψ ρ k} {r : k ◃₁ a}
          {z : Us m k (◃₁→◃ r) φ χ} {x : Q m a φ χ} {y : Q m′ b ψ ρ} →
          Cross x y → Cross (omk r z x) y
```
