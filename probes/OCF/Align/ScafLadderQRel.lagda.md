# 阶梯 (十一): 塔上的互模拟

> 结论写在 [ScafLadder](ScafLadder.lagda.md). 与 [ScafLadderRel](ScafLadderRel.lagda.md) 同形.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderQRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.ScafLadderZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.ScafLadderZDecoupleBase using (ΩΩ)
open import OCF.Align.ScafLadderZStage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.ScafLadderZStandardOmega using ()
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base hiding (_⊕_; Ψ) renaming (FW to FW₀)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Depth2Class
open import OCF.Align.ScafLadderZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.ScafLadderZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.ScafLadderZUniform5Head
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2; _<ᴸ_; zero; suc; tr<)
open import OCF.Align.ScafLadderZUniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.ScafLadderZUniform4Two using (<◃)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Bachmann using (clash)
open import OCF.Align.ScafLadderQ
open import OCF.Align.ScafLadderQClass using (out-intoU)
open import OCF.Align.ScafLadderQPsi using (out-intoV)
open RestrQ
```

## §1 关系

```agda
data SameQ {m n : ℕ} (q : n <ᴸ m) : ∀ {n′} → n′ <ᴸ m → Set where
  same : SameQ q q

Sim∼ : ℕ → Fv → Fv → Set
Sim∼ m χ ρ = ∀ i → i <ᴸ m → χ i ∼ᶠ ρ i

module _ (m : ℕ) (a b : Ordᴵ) (LR : ∀ {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → Q m k ξ ζ → Q m k′ ξ′ ζ′ → Set)
         (Lv : ∀ {n n′} → n <ᴸ m → n′ <ᴸ m → ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n′ k′ ξ′ ζ′ → Set) where
  data R₊ : ∀ {φ χ ψ ρ} → Q m a φ χ → Q m b ψ ρ → Set where
    rz : ∀ {φ χ ψ ρ} → R₊ {φ} {χ} {ψ} {ρ} q0 q0
    rs : ∀ {φ χ ψ ρ} {p : Q m a φ χ} {p′ : Q m b ψ ρ} → φ ∼ᶠ ψ → Sim∼ m χ ρ → R₊ p p′ → R₊ (qs p) (qs p′)
    rl : ∀ {φ χ ψ ρ} {F : ℕ → Q m a φ χ} {F′ : ℕ → Q m b ψ ρ} → (∀ n → R₊ (F n) (F′ n)) → R₊ (ql F) (ql F′)
    ri : ∀ {φ χ ψ ρ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → Q m a φ χ} {f′ : Ordˢ j′ → Q m b ψ ρ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → R₊ (f x) (f′ y)) → R₊ (qi ac f) (qi ac′ f′)
    rŝ : ∀ {φ χ ψ ρ c₁ c₂} {t : Q m a φ χ} {t′ : Q m b ψ ρ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q m b ψ ρ} →
         c₁ ≅ᴵ c₂ → R₊ t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (g η e) (g′ η′ e′)) → R₊ (qŝ c₁ t g) (qŝ c₂ t′ g′)
    rĉ : ∀ {φ χ ψ ρ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : Q m a φ χ} {o₀′ : Q m b ψ ρ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → Q m a φ χ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Q m b ψ ρ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → R₊ o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → R₊ (o η e) (o′ η′ e′)) → R₊ (qĉ c₁ z zg o₀ o) (qĉ c₂ z′ zg′ o₀′ o′)
    rclo : ∀ {φ χ ψ ρ} {t : Q m a (φ ⊔ fk zero) χ} {t′ : Q m b (ψ ⊔ fk zero) ρ} {g : (η : Ordᴵ) → Q m a (φ ⊔ fk η) χ} {g′ : (η : Ordᴵ) → Q m b (ψ ⊔ fk η) ρ} →
         φ ∼ᶠ ψ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (qclo t g) (qclo t′ g′)
    rcl : ∀ {φ χ ψ ρ n n′ κ₁ κ₂} {q : n <ᴸ m} {q′ : n′ <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ n′) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : Q m a φ χ} {t′ : Q m b ψ ρ} {g : (η : Ordᴵ) → Q m a φ (upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → Q m b ψ (upd ρ n′ (κ₂ ⊔ fk η))} →
         SameQ q q′ → κ₁ ∼ᶠ κ₂ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (qcl q κ₁ s t g) (qcl q′ κ₂ s′ t′ g′)
    rwk : ∀ {φ φ′ χ χ′ ψ ψ′ ρ ρ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub m ρ′ ρ}
          {x : Q m a φ χ} {x′ : Q m b ψ ρ} → R₊ x x′ → R₊ (qwk le lc x) (qwk le′ lc′ x′)
    rΩ↓ : ∀ {φ χ ψ ρ n n′ k k′} {q : n <ᴸ m} {q′ : n′ <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ n′) → k′ <ᴵ L}
          {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs m q′ k′ ξ ζ → Q m b (ξ ⊔ ψ) (lo n′ ζ ∪ ρ)} → SameQ q q′ → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → Sim∼ n′ ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n′ k′ ξ′ ζ′) → Lv q q′ z z′ → R₊ (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV q′ z′))) → R₊ (qΩ↓ q fe ac h) (qΩ↓ q′ fe′ ac′ h′)
    rΩ : ∀ {φ χ ψ ρ k k′} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r : k <ᴵ a} {r′ : k′ <ᴵ b}
         {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m a (ξ ⊔ φ) (lo m ζ ∪ χ)} {h′ : ∀ ξ ζ → Us m k′ (<→◃ r′) ξ ζ → Q m b (ξ ⊔ ψ) (lo m ζ ∪ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sim∼ m χ ρ →
         (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ m ζ ζ′ → (z : Q m k ξ ζ) (z′ : Q m k′ ξ′ ζ′) → LR (<→◃ r) z z′ → R₊ (h ξ ζ (intoU (<→◃ r) z)) (h′ ξ′ ζ′ (intoU (<→◃ r′) z′))) → R₊ (qΩ fe r h) (qΩ fe′ r′ h′)
    rob : ∀ {φ χ ψ ρ k k′} {r : k ◃₁ a} {r′ : k′ ◃₁ b} {z : Us m k (◃₁→◃ r) φ χ} {z′ : Us m k′ (◃₁→◃ r′) ψ ρ} {x : Q m a φ χ} {x′ : Q m b ψ ρ} →
          k ≅ᴵ k′ → LR (◃₁→◃ r) (outU (◃₁→◃ r) z) (outU (◃₁→◃ r′) z′) → R₊ x x′ → R₊ (omk r z x) (omk r′ z′ x′)

Rq : ∀ m a b {φ χ ψ ρ} → Q m a φ χ → Q m b ψ ρ → Set
LRq : ∀ m a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → Q m k ξ ζ → Q m k′ ξ′ ζ′ → Set
LVq : ∀ m {n n′} → n <ᴸ m → n′ <ᴸ m → ∀ {k k′ ξ ζ ξ′ ζ′} → Q n k ξ ζ → Q n′ k′ ξ′ ζ′ → Set
Rq m a b x y = R₊ m a b (LRq m a) (LVq m) x y
LRq m (suc k)   zero      {k′} x y = Rq m k k′ x y
LRq m (suc c)   (suc r)   x y = LRq m c r x y
LRq m (lim f s) (self n)  {k′} x y = Rq m (f n) k′ x y
LRq m (lim f s) (lim n r) x y = LRq m (f n) r x y
LVq (suc m) zero    zero     {k} {k′} x y = Rq m k k′ x y
LVq (suc m) zero    (suc q′) x y = ⊥
LVq (suc m) (suc q) zero     x y = ⊥
LVq (suc m) (suc q) (suc q′) x y = LVq m q q′ x y

outRq : ∀ {m c k} (r : k ◃ c) {k′ ξ ζ ξ′ ζ′} {z : Q m k ξ ζ} {z′ : Q m k′ ξ′ ζ′} → LRq m c r z z′ → Rq m k k′ z z′
outRq zero      l = l
outRq (suc r)   l = outRq r l
outRq (self n)  l = l
outRq (lim n r) l = outRq r l

intoRq : ∀ {m c k} (r : k ◃ c) {k′ ξ ζ ξ′ ζ′} {z : Q m k ξ ζ} {z′ : Q m k′ ξ′ ζ′} → Rq m k k′ z z′ → LRq m c r z z′
intoRq zero      l = l
intoRq (suc r)   l = intoRq r l
intoRq (self n)  l = l
intoRq (lim n r) l = intoRq r l

outVq : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → LVq m q q z z′ → Rq n k k′ z z′
outVq zero l = l
outVq (suc q) l = outVq q l

intoVq : ∀ {m n} (q : n <ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : Q n k ξ ζ} {z′ : Q n k′ ξ′ ζ′} → Rq n k k′ z z′ → LVq m q q z z′
intoVq zero l = l
intoVq (suc q) l = intoVq q l

Z∼ : ∀ {m χ ρ} → Sim∼ m χ ρ → Sim∼ m (Z* χ) (Z* ρ)
Z∼ s i q = ⊔∼ (∼ᶠ-refl Fl) (s i q)

∪∼ : ∀ {m a b χ ρ} → Sim∼ m a b → Sim∼ m χ ρ → Sim∼ m (a ∪ χ) (b ∪ ρ)
∪∼ s c i q = ⊔∼ (s i q) (c i q)

lo∼ : ∀ {m} H {ζ ζ′} → Sim∼ H ζ ζ′ → Sim∼ m (lo H ζ) (lo H ζ′)
lo∼ zero s i q = fz∼
lo∼ (suc H) s zero q = s zero (z<s H)
lo∼ {suc m} (suc H) {ζ} {ζ′} s (suc i) q = lo∼ {m} H {λ k → ζ (suc k)} {λ k → ζ′ (suc k)} (λ j r → s (suc j) (s<s r)) i (dn q)

```

## §2 封闭性

```agda
R-⊞ : ∀ {m a b φ χ φ′ χ′ ψ ρ ψ′ ρ′} {W : Q m a φ χ} {W′ : Q m b φ′ χ′} {t : Q m a ψ ρ} {t′ : Q m b ψ′ ρ′} → φ ∼ᶠ φ′ → Sim∼ m χ χ′ → Rq m a b W W′ → Rq m a b t t′ → Rq m a b (W ⊞ t) (W′ ⊞ t′)
R-⊞ s c rW rz = rwk rW
R-⊞ s c rW (rs sa sb r) = rs (⊔∼ s sa) (∪∼ c sb) (R-⊞ s c rW r)
R-⊞ s c rW (rl h) = rl (λ n → R-⊞ s c rW (h n))
R-⊞ s c rW (ri e h) = ri e (λ x y d → R-⊞ s c rW (h x y d))
R-⊞ s c rW (rŝ e r h) = rŝ e (R-⊞ s c rW r) (λ η ee η′ e′ d → R-⊞ s c rW (h η ee η′ e′ d))
R-⊞ s c rW (rĉ e dz dg r h) = rĉ e dz dg (R-⊞ s c rW r) (λ η ee η′ e′ d → R-⊞ s c rW (h η ee η′ e′ d))
R-⊞ s c rW (rclo sψ r h) = rwk (rclo (⊔∼ s sψ) (rwk (R-⊞ s c rW r)) (λ η η′ d → rwk (R-⊞ s c rW (h η η′ d))))
R-⊞ s c rW (rcl {q = q} same sψ r h) = rcl same (⊔∼ (c _ q) sψ) (R-⊞ s c rW r) (λ η η′ d → rwk (R-⊞ s c rW (h η η′ d)))
R-⊞ s c rW (rwk r) = rwk (R-⊞ s c rW r)
R-⊞ s c rW (rΩ↓ eqn ek sψ cψ f) = rΩ↓ eqn ek (⊔∼ s sψ) (∪∼ c cψ) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk (R-⊞ s c rW (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l)))
R-⊞ s c rW (rΩ ek sψ cψ f) = rΩ ek (⊔∼ s sψ) (∪∼ c cψ) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-⊞ s c rW (f ξ ξ′ ζ ζ′ d dc z z′ l)))
R-⊞ s c rW (rob _ l r) = R-⊞ s c rW r

R-ι : ∀ {m a b c d φ χ ψ ρ} (q : a ◃ c) (q′ : b ◃ d) {x : Q m a φ χ} {x′ : Q m b ψ ρ} → Rq m a b x x′ → Rq m c d (ι q x) (ι q′ x′)
R-ι q q′ rz = rz
R-ι q q′ (rs sa sb r) = rs sa sb (R-ι q q′ r)
R-ι q q′ (rl h) = rl (λ n → R-ι q q′ (h n))
R-ι q q′ (ri e h) = ri e (λ x y d → R-ι q q′ (h x y d))
R-ι q q′ (rŝ e r h) = rŝ e (R-ι q q′ r) (λ η ee η′ e′ d → R-ι q q′ (h η ee η′ e′ d))
R-ι q q′ (rĉ e dz dg r h) = rĉ e dz dg (R-ι q q′ r) (λ η ee η′ e′ d → R-ι q q′ (h η ee η′ e′ d))
R-ι q q′ (rclo s r h) = rclo s (R-ι q q′ r) (λ η η′ d → R-ι q q′ (h η η′ d))
R-ι q q′ (rcl eqn s r h) = rcl eqn s (R-ι q q′ r) (λ η η′ d → R-ι q q′ (h η η′ d))
R-ι q q′ (rwk r) = rwk (R-ι q q′ r)
R-ι q q′ (rΩ↓ eqn ek s c f) = rΩ↓ eqn ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → R-ι q q′ (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
R-ι {m} {c = c} {d = dd} q q′ (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s c′ f) =
  rΩ {r = <◃ r q} {r′ = <◃ r′ q′} ek s c′
     (λ ξ ξ′ ζ ζ′ e dc z z′ l → subst₂ (λ w w′ → Rq m c dd (ι q (h ξ ζ (intoU (<→◃ r) w))) (ι q′ (h′ ξ′ ζ′ (intoU (<→◃ r′) w′)))) (sym (out-intoU (<→◃ (<◃ r q)) z)) (sym (out-intoU (<→◃ (<◃ r′ q′)) z′))
                                (R-ι q q′ (f ξ ξ′ ζ ζ′ e dc _ _ (intoRq (<→◃ r) (outRq (<→◃ (<◃ r q)) l)))))
R-ι q q′ (rob _ l r) = R-ι q q′ r

upd∼ : ∀ {χ ρ : Fv} {x y} n → Sim∼ n χ ρ → x ∼ᶠ y → Sim∼ (suc n) (upd χ n x) (upd ρ n y)
upd∼ zero s c zero q = c
upd∼ zero s c (suc i) (suc ())
upd∼ (suc n) s c zero q = s zero (z<s n)
upd∼ {χ} {ρ} (suc n) s c (suc i) q = upd∼ {λ m → χ (suc m)} {λ m → ρ (suc m)} n (λ j r → s (suc j) (s<s r)) c i (dn q)

R-ι↓ : ∀ {n k k′ φ ψ χ ρ} → k ≅ᴵ k′ → {x : Q n k φ χ} {x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Rq (suc n) zero zero (ι↓ {α = zero} x) (ι↓ {α = zero} x′)
R-ι↓ ek rz = rz
R-ι↓ {n = n} ek (rs sa sb r) = rs sa (upd∼ n sb (flo-∼ ek)) (R-ι↓ ek r)
R-ι↓ ek (rl h) = rl (λ n → R-ι↓ ek (h n))
R-ι↓ ek (ri e h) = ri e (λ x y d → R-ι↓ ek (h x y d))
R-ι↓ ek (rŝ e r h) = rŝ e (R-ι↓ ek r) (λ η ee η′ e′ d → R-ι↓ ek (h η ee η′ e′ d))
R-ι↓ ek (rĉ e dz dg r h) = rĉ e dz dg (R-ι↓ ek r) (λ η ee η′ e′ d → R-ι↓ ek (h η ee η′ e′ d))
R-ι↓ ek (rclo s r h) = rclo s (R-ι↓ ek r) (λ η η′ d → R-ι↓ ek (h η η′ d))
R-ι↓ ek (rcl {q = q} same s r h) = rcl {q = suc q} {q′ = suc q} same s (R-ι↓ ek r) (λ η η′ d → rwk (R-ι↓ ek (h η η′ d)))
R-ι↓ ek (rwk r) = rwk (R-ι↓ ek r)
R-ι↓ {n = n} ek (rΩ↓ {q = q} same ei s c f) = rΩ↓ {q = suc q} {q′ = suc q} same ei s (upd∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk (R-ι↓ ek (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l)))
R-ι↓ {n = n} ek (rΩ {r = r} {r′ = r′} ei s c f) = rΩ↓ {q = zero} {q′ = zero} same ei s (upd∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk (R-ι↓ ek (f ξ ξ′ ζ ζ′ d dc z z′ (intoRq (<→◃ r) l))))
R-ι↓ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓ ea l)
R-ι↓ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ ea l)

R-tl : ∀ {c c′ k₁ k₂ φ φ′ χ ρ} {cv : ∀ {L} → Ev L φ → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       k₁ ≅ᴵ k₂ → φ ∼ᶠ φ′ → a ≅ᴬ b → Rq 0 c c′ (tl {χ = χ} φ cv a) (tl {χ = ρ} φ′ cv′ b)
R-tl ek sφ zᴬ = rz
R-tl ek sφ (sᴬ e) = rs sφ (λ i ()) (R-tl ek sφ e)
R-tl ek sφ (lᴬ h) = rl (λ n → R-tl ek sφ (h n))
R-tl ek sφ (lᵢᴬ {p = q} e h) = ri e (λ x y dd → R-tl ek sφ (h x y (≅→Rᴬ (<→◃ q) dd)))
R-tl {k₁ = suc k′} {k₂ = suc k″} (s≅ ek) sφ (uᴬ uz dd) = rwk (R-tl ek (flo-∼ ek) dd)
R-tl {k₁ = lim f r} {k₂ = lim g t} (l≅ hh) sφ (uᴬ (us n) dd) = rwk (R-tl (hh n) (flo-∼ (hh n)) dd)
R-tl {k₁ = zero} {k₂ = zero} ek sφ (ŝᴬ k ec et eg) =
  rĉ ec (toZ-≅ (≅ᴬ→≅ˢ₀ et)) (λ η e η′ e′ eη → toZ-≅ (≅ᴬ→≅ˢ₀ (eg η e η′ e′ eη))) (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl {k₁ = zero} {k₂ = suc _}   ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = zero} {k₂ = lim _ _} ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = suc _}   {k₂ = zero} ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = lim _ _} {k₂ = zero} ek sφ (ŝᴬ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = suc _} {k₂ = suc _} ek sφ (ŝᴬ k ec et eg) = rŝ ec (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl {k₁ = suc _} {k₂ = lim _ _} ek sφ (ŝᴬ k ec et eg) = rŝ ec (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = suc _} ek sφ (ŝᴬ k ec et eg) = rŝ ec (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = lim _ _} ek sφ (ŝᴬ k ec et eg) = rŝ ec (R-tl ek sφ et) (λ η e η′ e′ eη → R-tl ek sφ (eg η e η′ e′ eη))
R-tl ek sφ (ĉᴬ ec dt dg eo eO) = rĉ ec dt dg (R-tl ek sφ eo) (λ η e η′ e′ eη → R-tl ek sφ (eO η e η′ e′ eη))

Fl∼ : ∀ {m} → Sim∼ m (κ Fl) (κ Fl)
Fl∼ i q = ∼ᶠ-refl Fl

RΩ̇ : ∀ m {a b} → a ≅ᴵ b → Rq m a b (Ω̇ m a) (Ω̇ m b)
RΩ̇ m (s≅ e) = rΩ e (⊔∼ fz∼ (fk∼ z≅)) Fl∼ (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rob {r = zero} {r′ = zero} e l (R-ι zero zero l)))
RΩ̇ m (l≅ h) = rl (λ n → rob {r = self n} {r′ = self n} (h n) (RΩ̇ m (h n)) (R-ι (self n) (self n) (RΩ̇ m (h n))))
RΩ̇ zero z≅ = rclo (∼ᶠ-refl fz)
  (R-tl (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)) (Ωˢ-≅ᴬ (≅ᴵ-refl (suc zero))))
  (λ η η′ eη → R-tl eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)) (Ωˢ-≅ᴬ eη))
RΩ̇ (suc m) z≅ = rcl {q = zero} {q′ = zero} same fz∼ (rwk (R-ι↓ (s≅ z≅) (RΩ̇ m (s≅ z≅)))) (λ η η′ eη → rwk (R-ι↓ eη (RΩ̇ m eη)))
```

## §3 搬运

```agda
R-trˡ  : ∀ {m a a′ b φ χ ψ ρ} (e : a ≅ᴵ a′) {x : Q m a φ χ} {y : Q m b ψ ρ} → Rq m a b x y → Rq m a′ b (trQ e x) y
R-tr⁻ˡ : ∀ {m a a′ b φ χ ψ ρ} (e : a′ ≅ᴵ a) {x : Q m a φ χ} {y : Q m b ψ ρ} → Rq m a b x y → Rq m a′ b (tr⁻Q e x) y
R-resˡ : ∀ {m j a a′ b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : a ≅ᴵ a′) {z : Q m (repQ (resQ q e)) ξ ζ} {y : Q m b ξ′ ζ′} → Rq m _ b z y → Rq m j b (backQ (resQ q e) z) y
R-res⁻ˡ : ∀ {m j a a′ b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : a′ ≅ᴵ a) {z : Q m (repQ (res⁻Q q e)) ξ ζ} {y : Q m b ξ′ ζ′} → Rq m _ b z y → Rq m j b (backQ (res⁻Q q e) z) y

R-trˡ e rz = rz
R-trˡ e (rs sa sb r) = rs sa sb (R-trˡ e r)
R-trˡ e (rl h) = rl (λ m → R-trˡ e (h m))
R-trˡ e (ri ej h) = ri ej (λ x y d → R-trˡ e (h x y d))
R-trˡ e (rŝ ec r h) = rŝ ec (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
R-trˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
R-trˡ e (rclo s r h) = rclo s (R-trˡ e r) (λ η η′ d → R-trˡ e (h η η′ d))
R-trˡ e (rcl eqn s r h) = rcl eqn s (R-trˡ e r) (λ η η′ d → R-trˡ e (h η η′ d))
R-trˡ e (rwk r) = rwk (R-trˡ e r)
R-trˡ e (rΩ↓ eqn ek s c f) = rΩ↓ eqn ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → R-trˡ e (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
R-trˡ (s≅ e) (rob {r = zero} ek l r) = rob (≅ᴵ-trans (≅ᴵ-sym e) ek) (R-trˡ e l) (R-trˡ (s≅ e) r)
R-trˡ (l≅ h) (rob {r = self n} ek l r) = rob (≅ᴵ-trans (≅ᴵ-sym (h n)) ek) (R-trˡ (h n) l) (R-trˡ (l≅ h) r)
R-trˡ {m} {a′ = a′} {b} e (rΩ {r = q} {r′} {h} {h′} ek s c f) =
  rΩ {r = ltQ (resQ q e)} (≅ᴵ-trans (≅ᴵ-sym (eqQ (resQ q e))) ek) s c
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rq m a′ b (trQ e (h ξ ζ (intoU (<→◃ q) (backQ (resQ q e) w)))) (h′ ξ′ ζ′ (intoU (<→◃ r′) z′))) (sym (out-intoU (<→◃ (ltQ (resQ q e))) z))
                              (R-trˡ e (f ξ ξ′ ζ ζ′ d dc _ z′ (intoRq (<→◃ q) (R-resˡ q e (outRq (<→◃ (ltQ (resQ q e))) l))))))

R-tr⁻ˡ e rz = rz
R-tr⁻ˡ e (rs sa sb r) = rs sa sb (R-tr⁻ˡ e r)
R-tr⁻ˡ e (rl h) = rl (λ m → R-tr⁻ˡ e (h m))
R-tr⁻ˡ e (ri ej h) = ri ej (λ x y d → R-tr⁻ˡ e (h x y d))
R-tr⁻ˡ e (rŝ ec r h) = rŝ ec (R-tr⁻ˡ e r) (λ η ee η′ e′ d → R-tr⁻ˡ e (h η ee η′ e′ d))
R-tr⁻ˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ˡ e r) (λ η ee η′ e′ d → R-tr⁻ˡ e (h η ee η′ e′ d))
R-tr⁻ˡ e (rclo s r h) = rclo s (R-tr⁻ˡ e r) (λ η η′ d → R-tr⁻ˡ e (h η η′ d))
R-tr⁻ˡ e (rcl eqn s r h) = rcl eqn s (R-tr⁻ˡ e r) (λ η η′ d → R-tr⁻ˡ e (h η η′ d))
R-tr⁻ˡ e (rwk r) = rwk (R-tr⁻ˡ e r)
R-tr⁻ˡ e (rΩ↓ eqn ek s c f) = rΩ↓ eqn ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → R-tr⁻ˡ e (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
R-tr⁻ˡ (s≅ e) (rob {r = zero} ek l r) = rob (≅ᴵ-trans e ek) (R-tr⁻ˡ e l) (R-tr⁻ˡ (s≅ e) r)
R-tr⁻ˡ (l≅ h) (rob {r = self n} ek l r) = rob (≅ᴵ-trans (h n) ek) (R-tr⁻ˡ (h n) l) (R-tr⁻ˡ (l≅ h) r)
R-tr⁻ˡ {m} {a′ = a′} {b} e (rΩ {r = q} {r′} {h} {h′} ek s c f) =
  rΩ {r = ltQ (res⁻Q q e)} (≅ᴵ-trans (≅ᴵ-sym (eqQ (res⁻Q q e))) ek) s c
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rq m a′ b (tr⁻Q e (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q e) w)))) (h′ ξ′ ζ′ (intoU (<→◃ r′) z′))) (sym (out-intoU (<→◃ (ltQ (res⁻Q q e))) z))
                              (R-tr⁻ˡ e (f ξ ξ′ ζ ζ′ d dc _ z′ (intoRq (<→◃ q) (R-res⁻ˡ q e (outRq (<→◃ (ltQ (res⁻Q q e))) l))))))

R-resˡ zero      (s≅ e) l = R-tr⁻ˡ e l
R-resˡ (suc q)   (s≅ e) l = R-resˡ q e l
R-resˡ (lim n q) (l≅ h) l = R-resˡ q (h n) l

R-res⁻ˡ zero      (s≅ e) l = R-trˡ e l
R-res⁻ˡ (suc q)   (s≅ e) l = R-res⁻ˡ q e l
R-res⁻ˡ (lim n q) (l≅ h) l = R-res⁻ˡ q (h n) l

R-trʳ  : ∀ {m a b b′ φ χ ψ ρ} (e : b ≅ᴵ b′) {x : Q m a φ χ} {y : Q m b ψ ρ} → Rq m a b x y → Rq m a b′ x (trQ e y)
R-tr⁻ʳ : ∀ {m a b b′ φ χ ψ ρ} (e : b′ ≅ᴵ b) {x : Q m a φ χ} {y : Q m b ψ ρ} → Rq m a b x y → Rq m a b′ x (tr⁻Q e y)
R-resʳ : ∀ {m j a b b′ ξ ζ ξ′ ζ′} (q : j <ᴵ b) (e : b ≅ᴵ b′) {z : Q m a ξ ζ} {y : Q m (repQ (resQ q e)) ξ′ ζ′} → Rq m a _ z y → Rq m a j z (backQ (resQ q e) y)
R-res⁻ʳ : ∀ {m j a b b′ ξ ζ ξ′ ζ′} (q : j <ᴵ b) (e : b′ ≅ᴵ b) {z : Q m a ξ ζ} {y : Q m (repQ (res⁻Q q e)) ξ′ ζ′} → Rq m a _ z y → Rq m a j z (backQ (res⁻Q q e) y)

R-trʳ e rz = rz
R-trʳ e (rs sa sb r) = rs sa sb (R-trʳ e r)
R-trʳ e (rl h) = rl (λ m → R-trʳ e (h m))
R-trʳ e (ri ej h) = ri ej (λ x y d → R-trʳ e (h x y d))
R-trʳ e (rŝ ec r h) = rŝ ec (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rclo s r h) = rclo s (R-trʳ e r) (λ η η′ d → R-trʳ e (h η η′ d))
R-trʳ e (rcl eqn s r h) = rcl eqn s (R-trʳ e r) (λ η η′ d → R-trʳ e (h η η′ d))
R-trʳ e (rwk r) = rwk (R-trʳ e r)
R-trʳ e (rΩ↓ eqn ek s c f) = rΩ↓ eqn ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → R-trʳ e (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
R-trʳ (s≅ e) (rob {r = zero} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek e) (R-trʳ e l) (R-trʳ (s≅ e) r)
R-trʳ (s≅ e) (rob {r = self i} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek e) (R-trʳ e l) (R-trʳ (s≅ e) r)
R-trʳ (l≅ h) (rob {r = zero} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (h n)) (R-trʳ (h n) l) (R-trʳ (l≅ h) r)
R-trʳ (l≅ h) (rob {r = self i} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (h n)) (R-trʳ (h n) l) (R-trʳ (l≅ h) r)
R-trʳ {m} {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s c f) =
  rΩ {r = r} {r′ = ltQ (resQ q e)} (≅ᴵ-trans ek (eqQ (resQ q e))) s c
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rq m a b′ (h ξ ζ (intoU (<→◃ r) z)) (trQ e (h′ ξ′ ζ′ (intoU (<→◃ q) (backQ (resQ q e) w))))) (sym (out-intoU (<→◃ (ltQ (resQ q e))) z′))
                              (R-trʳ e (f ξ ξ′ ζ ζ′ d dc z _ (intoRq (<→◃ r) (R-resʳ q e (outRq (<→◃ r) l))))))

R-tr⁻ʳ e rz = rz
R-tr⁻ʳ e (rs sa sb r) = rs sa sb (R-tr⁻ʳ e r)
R-tr⁻ʳ e (rl h) = rl (λ m → R-tr⁻ʳ e (h m))
R-tr⁻ʳ e (ri ej h) = ri ej (λ x y d → R-tr⁻ʳ e (h x y d))
R-tr⁻ʳ e (rŝ ec r h) = rŝ ec (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
R-tr⁻ʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
R-tr⁻ʳ e (rclo s r h) = rclo s (R-tr⁻ʳ e r) (λ η η′ d → R-tr⁻ʳ e (h η η′ d))
R-tr⁻ʳ e (rcl eqn s r h) = rcl eqn s (R-tr⁻ʳ e r) (λ η η′ d → R-tr⁻ʳ e (h η η′ d))
R-tr⁻ʳ e (rwk r) = rwk (R-tr⁻ʳ e r)
R-tr⁻ʳ e (rΩ↓ eqn ek s c f) = rΩ↓ eqn ek s c (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → R-tr⁻ʳ e (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l))
R-tr⁻ʳ (s≅ e) (rob {r = zero} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym e)) (R-tr⁻ʳ e l) (R-tr⁻ʳ (s≅ e) r)
R-tr⁻ʳ (s≅ e) (rob {r = self i} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym e)) (R-tr⁻ʳ e l) (R-tr⁻ʳ (s≅ e) r)
R-tr⁻ʳ (l≅ h) (rob {r = zero} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym (h n))) (R-tr⁻ʳ (h n) l) (R-tr⁻ʳ (l≅ h) r)
R-tr⁻ʳ (l≅ h) (rob {r = self i} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym (h n))) (R-tr⁻ʳ (h n) l) (R-tr⁻ʳ (l≅ h) r)
R-tr⁻ʳ {m} {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s c f) =
  rΩ {r = r} {r′ = ltQ (res⁻Q q e)} (≅ᴵ-trans ek (eqQ (res⁻Q q e))) s c
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rq m a b′ (h ξ ζ (intoU (<→◃ r) z)) (tr⁻Q e (h′ ξ′ ζ′ (intoU (<→◃ q) (backQ (res⁻Q q e) w))))) (sym (out-intoU (<→◃ (ltQ (res⁻Q q e))) z′))
                              (R-tr⁻ʳ e (f ξ ξ′ ζ ζ′ d dc z _ (intoRq (<→◃ r) (R-res⁻ʳ q e (outRq (<→◃ r) l))))))

R-resʳ zero      (s≅ e) l = R-tr⁻ʳ e l
R-resʳ (suc q)   (s≅ e) l = R-resʳ q e l
R-resʳ (lim n q) (l≅ h) l = R-resʳ q (h n) l

R-res⁻ʳ zero      (s≅ e) l = R-trʳ e l
R-res⁻ʳ (suc q)   (s≅ e) l = R-res⁻ʳ q e l
R-res⁻ʳ (lim n q) (l≅ h) l = R-res⁻ʳ q (h n) l
```

## §4 字面目标

```agda
R-repᵠ : ∀ {m a b φ χ ψ ρ} {X : Q m a φ χ} {X′ : Q m b ψ ρ} → φ ∼ᶠ ψ → Sim∼ m χ ρ → Rq m a b X X′ → ∀ n → Rq m a b (repᵠ X n) (repᵠ X′ n)
R-repᵠ s c r zero = rz
R-repᵠ s c r (suc zero) = r
R-repᵠ s c r (suc (suc n)) = rwk (R-⊞ s c (R-repᵠ s c r (suc n)) r)

R-ψᵠ : ∀ {m a b t t′ φ χ ψ ρ} (q : t <ᴵ a) (q′ : t′ <ᴵ b) → t ≅ᴵ t′ → {x : Q m a φ χ} {x′ : Q m b ψ ρ} → Rq m a b x x′ → Rq m t t′ (ψᵠ q x) (ψᵠ q′ x′)
chRG : ∀ {m a b k k′ φ χ ψ ρ ξ ξ′} {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {r : k <ᴵ a} {r′ : k′ <ᴵ b} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m a (ξ ⊔ φ) (lo m ζ ∪ χ)} {h′ : ∀ ξ ζ → Us m k′ (<→◃ r′) ξ ζ → Q m b (ξ ⊔ ψ) (lo m ζ ∪ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sim∼ m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ m ζ ζ′ → (z : Q m k ξ ζ) (z′ : Q m k′ ξ′ ζ′) → LRq m a (<→◃ r) z z′ → Rq m a b (h ξ ζ (intoU (<→◃ r) z)) (h′ ξ′ ζ′ (intoU (<→◃ r′) z′))) →
       ∀ n → Rq m k k′ (chainᵠ fe fc* (λ z → qwk a₁ (⇑ (cv* m)) (ψᵠ r (h ξ (Z* χ) (intoU (<→◃ r) z)))) n) (chainᵠ fe′ fc* (λ z → qwk a₂ (⇑ (cv* m)) (ψᵠ r′ (h′ ξ′ (Z* ρ) (intoU (<→◃ r′) z)))) n)

R-ψᵠ {m} q q′ et rz = rwk (RΩ̇ m et)
R-ψᵠ q q′ et (rs sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ sb) (R-ψᵠ q q′ et r))
R-ψᵠ q q′ et (rl h) = rl (λ n → R-ψᵠ q q′ et (h n))
R-ψᵠ q q′ et (ri e h) = ri e (λ x y d → R-ψᵠ q q′ et (h x y d))
R-ψᵠ q q′ et (rŝ e r h) = rŝ e (R-ψᵠ q q′ et r) (λ η ee η′ e′ d → R-ψᵠ q q′ et (h η ee η′ e′ d))
R-ψᵠ q q′ et (rĉ e dz dg r h) = rĉ e dz dg (R-ψᵠ q q′ et r) (λ η ee η′ e′ d → R-ψᵠ q q′ et (h η ee η′ e′ d))
R-ψᵠ q q′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψᵠ q q′ et r)) (λ η η′ d → rwk (R-ψᵠ q q′ et (h η η′ d))))
R-ψᵠ q q′ et (rcl eqn s r h) = rcl eqn (⊔∼ (∼ᶠ-refl Fl) s) (R-ψᵠ q q′ et r) (λ η η′ d → rwk (R-ψᵠ q q′ et (h η η′ d)))
R-ψᵠ q q′ et (rwk r) = rwk (R-ψᵠ q q′ et r)
R-ψᵠ q q′ et (rob _ l r) = R-ψᵠ q q′ et r
R-ψᵠ q q′ et (rΩ↓ eqn ek s c f) = rΩ↓ eqn ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk (R-ψᵠ q q′ et (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l)))
R-ψᵠ {m} {t = t} {t′} q q′ et (rΩ {φ = φ} {χ} {ψ} {ρ} {k} {k′} {r = r} {r′} {h} {h′} ek s c f) with <ᴵ-dec r q | <ᴵ-dec r′ q′
... | injᵃ (via e p) | injᵃ (via e′ p′) =
  rΩ {r = p} {r′ = p′} (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans ek e′)) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c)
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ w w′ → Rq m t t′ (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e w)))) (ψᵠ q′ (h′ ξ′ ζ′ (intoU (<→◃ r′) (tr⁻Q e′ w′))))) (sym (out-intoU (<→◃ p) z)) (sym (out-intoU (<→◃ p′) z′))
                                    (R-ψᵠ q q′ et (f ξ ξ′ ζ ζ′ d dc _ _ (intoRq (<→◃ r) (R-tr⁻ˡ e (R-tr⁻ʳ e′ (outRq (<→◃ p) l))))))))
... | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
... | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
... | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
... | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
... | injᵇ _ | injᵇ _ = rl (λ n → rwk (R-ψᵠ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f n)))))
... | injᵇ _ | injᶜ _ = rl (λ n → rwk (R-ψᵠ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f n)))))
... | injᶜ _ | injᵇ _ = rl (λ n → rwk (R-ψᵠ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f n)))))
... | injᶜ _ | injᶜ _ = rl (λ n → rwk (R-ψᵠ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f n)))))

chRG {m} ek sξ c f zero = rwk (RΩ̇ m ek)
chRG {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} {fe = fe} {fe′} {a₁} {a₂} {r = r} {r′ = r′} {h = h} {h′ = h′} ek sξ c f (suc n) =
  rwk (R-ψᵠ r r′ ek (f ξ ξ′ (Z* χ) (Z* ρ) sξ (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂} {r = r} {r′ = r′} {h = h} {h′ = h′} ek sξ c f n))))
```

## §5 目标在高度 $H$

```agda
R-Ψ : ∀ {H m a b t t′ φ χ ψ ρ w w′} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) (ok′ : Ok w′) (e′ : Eh H m w′ ρ) (p′ : t′ <ᴵ w′ H) → t ≅ᴵ t′ → {x : Q m a φ χ} {x′ : Q m b ψ ρ} → Rq m a b x x′ → Rq H t t′ (Ψ qH ok e p x) (Ψ qH ok′ e′ p′ x′)
chRΨ : ∀ {m a b n k k′ φ χ ψ ρ ξ ξ′ w w′} (q : n <ᴸ m) (ok : Ok w) (e* : Eh n m w (lo n (Z* χ) ∪ χ)) (p₁ : k <ᴵ w n) (ok′ : Ok w′) (e′* : Eh n m w′ (lo n (Z* ρ) ∪ ρ)) (p₂ : k′ <ᴵ w′ n)
       {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m a (ξ ⊔ φ) (lo n ζ ∪ χ)} {h′ : ∀ ξ ζ → Vs m q k′ ξ ζ → Q m b (ξ ⊔ ψ) (lo n ζ ∪ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sim∼ m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sim∼ n ζ ζ′ → Sim∼ n ζ ζ′ → (z : Q n k ξ ζ) (z′ : Q n k′ ξ′ ζ′) → LVq m q q z z′ → Rq m a b (h ξ ζ (intoV q z)) (h′ ξ′ ζ′ (intoV q z′))) →
       ∀ i → Rq n k k′ (chainᵠ fe fc* (λ z → qwk a₁ (⇑ (cv* n)) (Ψ q ok e* p₁ (h ξ (Z* χ) (intoV q z)))) i) (chainᵠ fe′ fc* (λ z → qwk a₂ (⇑ (cv* n)) (Ψ q ok′ e′* p₂ (h′ ξ′ (Z* ρ) (intoV q z)))) i)

R-Ψ {H} qH ok e p ok′ e′ p′ et rz = rwk (RΩ̇ H et)
R-Ψ qH ok e p ok′ e′ p′ et (rs sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ (λ i q → sb i (tr< q qH))) (R-Ψ qH ok e p ok′ e′ p′ et r))
R-Ψ qH ok e p ok′ e′ p′ et (rl h) = rl (λ n → R-Ψ qH ok e p ok′ e′ p′ et (h n))
R-Ψ qH ok e p ok′ e′ p′ et (ri d h) = ri d (λ x y dd → R-Ψ qH ok e p ok′ e′ p′ et (h x y dd))
R-Ψ qH ok e p ok′ e′ p′ et (rŝ d r h) = rŝ d (R-Ψ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → R-Ψ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
R-Ψ qH ok e p ok′ e′ p′ et (rĉ d dz dg r h) = rĉ d dz dg (R-Ψ qH ok e p ok′ e′ p′ et r) (λ η ee η′ e₁ dd → R-Ψ qH ok e p ok′ e′ p′ et (h η ee η′ e₁ dd))
R-Ψ qH ok e p ok′ e′ p′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-Ψ qH ok e p ok′ e′ p′ et r)) (λ η η′ d → rwk (R-Ψ qH ok e p ok′ e′ p′ et (h η η′ d))))
R-Ψ qH ok e p ok′ e′ p′ et (rwk {lc = lc} {lc′ = lc′} r) = rwk (R-Ψ qH ok (λ i h r₁ → lc i r₁ (e i h r₁)) p ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)) p′ et r)
R-Ψ qH ok e p ok′ e′ p′ et (rob _ l r) = R-Ψ qH ok e p ok′ e′ p′ et r
R-Ψ {H} qH ok e p ok′ e′ p′ et (rcl {n = n} same s r h) with tri n H
... | tlt l = rcl {q = l} {q′ = l} same (⊔∼ (∼ᶠ-refl Fl) s) (R-Ψ qH ok e p ok′ e′ p′ et r) (λ η η′ d → rwk (R-Ψ qH ok _ p ok′ _ p′ et (h η η′ d)))
... | teq refl = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ p _ p′ et) (R-Ψ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (R-Ψ qH _ _ _ _ _ _ et (h η η′ eη)))
... | tgt l = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (R-Ψ qH ok e p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (R-Ψ qH _ _ _ _ _ _ et (h η η′ eη)))
R-Ψ {H} {t = t} {t′} qH ok e p ok′ e′ p′ et (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} same ek s c f) with tri n H
... | tlt l = rΩ↓ {q = l} {q′ = l} same ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
      (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ lz → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q u))) (Ψ qH ok′ (e-lo ζ′ (inj₂ l) e′) p′ (h′ ξ′ ζ′ (intoV q v)))) (sym (out-intoV l z)) (sym (out-intoV l z′))
         (R-Ψ qH ok (e-lo ζ (inj₂ l) e) p ok′ (e-lo ζ′ (inj₂ l) e′) p′ et (f ξ ξ′ ζ ζ′ d dc dc′ z z′ (intoVq q (outVq l lz))))))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p | <ᴵ-dec (ac′ (e′ n (inj₁ refl) q)) p′
...   | injᵃ (via d₁ s₁) | injᵃ (via d₂ s₂) =
  rΩ {r = s₁} {r′ = s₂} (≅ᴵ-trans (≅ᴵ-sym d₁) (≅ᴵ-trans ek d₂)) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ i r → c i (tr< r qH)))
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ u v → Rq H t t′ (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q (tr⁻Q d₁ u)))) (Ψ qH ok′ (e-lo ζ′ (inj₁ refl) e′) p′ (h′ ξ′ ζ′ (intoV q (tr⁻Q d₂ v))))) (sym (out-intoU (<→◃ s₁) z)) (sym (out-intoU (<→◃ s₂) z′))
        (R-Ψ qH ok (e-lo ζ (inj₁ refl) e) p ok′ (e-lo ζ′ (inj₁ refl) e′) p′ et (f ξ ξ′ ζ ζ′ d dc dc _ _ (intoVq q (R-tr⁻ˡ d₁ (R-tr⁻ʳ d₂ (outRq (<→◃ s₁) l))))))))
...   | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
...   | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
...   | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
...   | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
...   | injᵇ _ | injᵇ _ = rl (λ i → rwk (R-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVq q (chRΨ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) q)) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
...   | injᵇ _ | injᶜ _ = rl (λ i → rwk (R-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVq q (chRΨ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) q)) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
...   | injᶜ _ | injᵇ _ = rl (λ i → rwk (R-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVq q (chRΨ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) q)) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
...   | injᶜ _ | injᶜ _ = rl (λ i → rwk (R-Ψ qH ok (e⁺ H ok e) p ok′ (e⁺ H ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVq q (chRΨ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) ok′ (e⁺ n ok′ e′) (ac′ (e′ n (inj₁ refl) q)) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
R-Ψ {H} {t = t} {t′} qH ok e p ok′ e′ p′ et (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} same ek s c f) | tgt l =
  rl (λ i → rwk (R-Ψ qH ok (e⁺ n ok e) p ok′ (e⁺ n ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVq q (chRΨ q ok (e⁺ n ok (e↑ l e)) (ac ((e↑ l e) n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↑ l e′)) (ac′ ((e↑ l e′) n (inj₁ refl) q)) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
R-Ψ {H} {m} qH ok e p ok′ e′ p′ et (rΩ {φ = φ} {χ} {ψ} {ρ} {r = r} {r′} {h} {h′} ek s c f) =
  rl (λ i → rwk (R-Ψ qH ok (e⁺ m ok e) p ok′ (e⁺ m ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Z* χ) (Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))

chRΨ {n = n} q ok e* p₁ ok′ e′* p₂ ek sξ c f zero = rwk (RΩ̇ n ek)
chRΨ {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′} {a₁} {a₂} {h} {h′} ek sξ c f (suc i) =
  rwk (R-Ψ q ok e* p₁ ok′ e′* p₂ ek (f ξ ξ′ (Z* χ) (Z* ρ) sξ (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVq q (chRΨ q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂} {h = h} {h′ = h′} ek sξ c f i))))
```
