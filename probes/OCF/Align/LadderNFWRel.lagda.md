> **机械克隆, 验收用.** 由 `LadderNFRel` 经脚本复制, 只改导入, 把证书搬到标签阶梯的世界. 见 [LadderNFAccept](LadderNFAccept.lagda.md).

# 阶梯去记号 (二): 塔上的互模拟

> 结论写在 [LadderNF](LadderNF.lagda.md). 行与 [ScafLadderQRel](ScafLadderQRel.lagda.md) 一一对应, 值层关系换成主线的 $\cong^\mathsf S$ (`≅ˢ`), `rwk` 拆成单侧. 不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderNFWRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.LadderNFWPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ)
open import OCF.Align.LadderNFWAux using (tf)
open import OCF.Align.LadderNFWEq using (_≅ᶻ_; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Align.LadderNFWFloor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound; bound-≅; evF)
open import OCF.Align.LadderNFWFT using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Align.LadderNFWBase using (clash; r∅)
open import OCF.Align.LadderNFWTree
open RestrQ

flo-∼ : ∀ {k k′} → k ≅ᴵ k′ → flo k ∼ᶠ flo k′
flo-∼ z≅     = fz∼
flo-∼ (s≅ e) = fk∼ e
flo-∼ (l≅ h) = fb∼ (l≅ h)

out-intoU : ∀ {m c k} (r : k ◃ c) {ξ ζ} (z : Q m k ξ ζ) → outU r (intoU r z) ≡ z
out-intoU zero      z = refl
out-intoU (suc r)   z = out-intoU r z
out-intoU (self n)  z = refl
out-intoU (lim n r) z = out-intoU r z

out-intoV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} (z : Q n k ξ ζ) → outV q (intoV q z) ≡ z
out-intoV zero    z = refl
out-intoV (suc q) z = out-intoV q z
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
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → R₊ (f x) (f′ y)) → R₊ (qi ac f) (qi ac′ f′)
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
    rwkˡ : ∀ {φ φ′ χ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {x : Q m a φ χ} {x′ : Q m b ψ ρ} → R₊ x x′ → R₊ (qwk le lc x) x′
    rwkʳ : ∀ {φ χ ψ ψ′ ρ ρ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub m ρ′ ρ} {x : Q m a φ χ} {x′ : Q m b ψ ρ} → R₊ x x′ → R₊ x (qwk le′ lc′ x′)
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

rwk : ∀ {m a b φ φ′ χ χ′ ψ ψ′ ρ ρ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : Sub m χ′ χ} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : Sub m ρ′ ρ}
      {x : Q m a φ χ} {x′ : Q m b ψ ρ} → Rq m a b x x′ → Rq m a b (qwk le lc x) (qwk le′ lc′ x′)
rwk r = rwkˡ (rwkʳ r)

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
R-⊞ s c rW (rwkˡ r) = rwkˡ (R-⊞ s c rW r)
R-⊞ s c rW (rwkʳ r) = rwkʳ (R-⊞ s c rW r)
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
R-ι q q′ (rwkˡ r) = rwkˡ (R-ι q q′ r)
R-ι q q′ (rwkʳ r) = rwkʳ (R-ι q q′ r)
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

R-ι↓ : ∀ {n k k′ α α′ φ ψ χ ρ} → k ≅ᴵ k′ → {x : Q n k φ χ} {x′ : Q n k′ ψ ρ} → Rq n k k′ x x′ → Rq (suc n) α α′ (ι↓ x) (ι↓ x′)
R-ι↓ ek rz = rz
R-ι↓ {n = n} ek (rs sa sb r) = rs sa (upd∼ n sb (flo-∼ ek)) (R-ι↓ ek r)
R-ι↓ ek (rl h) = rl (λ n → R-ι↓ ek (h n))
R-ι↓ ek (ri e h) = ri e (λ x y d → R-ι↓ ek (h x y d))
R-ι↓ ek (rŝ e r h) = rŝ e (R-ι↓ ek r) (λ η ee η′ e′ d → R-ι↓ ek (h η ee η′ e′ d))
R-ι↓ ek (rĉ e dz dg r h) = rĉ e dz dg (R-ι↓ ek r) (λ η ee η′ e′ d → R-ι↓ ek (h η ee η′ e′ d))
R-ι↓ ek (rclo s r h) = rclo s (R-ι↓ ek r) (λ η η′ d → R-ι↓ ek (h η η′ d))
R-ι↓ ek (rcl {q = q} same s r h) = rcl {q = suc q} {q′ = suc q} same s (R-ι↓ ek r) (λ η η′ d → rwk (R-ι↓ ek (h η η′ d)))
R-ι↓ ek (rwkˡ r) = rwkˡ (R-ι↓ ek r)
R-ι↓ ek (rwkʳ r) = rwkʳ (R-ι↓ ek r)
R-ι↓ {n = n} ek (rΩ↓ {q = q} same ei s c f) = rΩ↓ {q = suc q} {q′ = suc q} same ei s (upd∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk (R-ι↓ ek (f ξ ξ′ ζ ζ′ d dc dc′ z z′ l)))
R-ι↓ {n = n} ek (rΩ {r = r} {r′ = r′} ei s c f) = rΩ↓ {q = zero} {q′ = zero} same ei s (upd∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc dc′ z z′ l → rwk (R-ι↓ ek (f ξ ξ′ ζ ζ′ d dc z z′ (intoRq (<→◃ r) l))))
R-ι↓ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓ ea l)
R-ι↓ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ ea l)

R-tl : ∀ {c c′ k₁ k₂ χ ρ} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       a ≅ˢ b → Rq 0 c c′ (tl {χ = χ} (flo k₁) cv a) (tl {χ = ρ} (flo k₂) cv′ b)
R-tl z≅ = rz
R-tl (s≅ le e) = rs (flo-∼ le) (λ i ()) (R-tl e)
R-tl (l≅ h) = rl (λ n → R-tl (h n))
R-tl (lᵢ≅ {p = q} e h) = ri e (λ x y dd → R-tl (h x y (≅→Rˢ (<→◃ q) dd)))
R-tl {k₁ = suc k′} (upˡ {r = zero} d) = rwkˡ (R-tl d)
R-tl {k₁ = lim f s} (upˡ {r = self n} d) = rwkˡ (R-tl d)
R-tl {k₂ = suc k′} (upʳ {r = zero} d) = rwkʳ (R-tl d)
R-tl {k₂ = lim f s} (upʳ {r = self n} d) = rwkʳ (R-tl d)
R-tl {k₁ = zero} {k₂ = zero} (ŝ≅ k ec et eg) =
  rĉ ec (toZ-≅ et) (λ η e η′ e′ eη → toZ-≅ (eg η e η′ e′ eη)) (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = zero} {k₂ = suc _}   (ŝ≅ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = zero} {k₂ = lim _ _} (ŝ≅ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = suc _}   {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = lim _ _} {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = suc _} {k₂ = suc _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = suc _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = suc _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e η′ e′ eη → R-tl (eg η e η′ e′ eη))
R-tl (ĉ≅ ec dt dg eo eO) = rĉ ec dt dg (R-tl eo) (λ η e η′ e′ eη → R-tl (eO η e η′ e′ eη))

R-tlΩ : ∀ {c c′ η η′ φ φ′ χ ρ} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ → Rq 0 c c′ (tl {χ = χ} φ cv (Ωˢ η)) (tl {χ = ρ} φ′ cv′ (Ωˢ η′))
R-tlΩ z≅ s = rs s (λ i ()) rz
R-tlΩ (s≅ e) s = ri e (λ x y d → rwk (R-tl d))
R-tlΩ (l≅ h) s = rl (λ n → rwk (R-tl (Ωˢ-≅ (h n))))

Fl∼ : ∀ {m} → Sim∼ m (κ Fl) (κ Fl)
Fl∼ i q = ∼ᶠ-refl Fl

RΩ̇ : ∀ m {a b} → a ≅ᴵ b → Rq m a b (Ω̇ m a) (Ω̇ m b)
RΩ̇ m (s≅ e) = rΩ e (⊔∼ fz∼ (fk∼ z≅)) Fl∼ (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rob {r = zero} {r′ = zero} e l (R-ι zero zero l)))
RΩ̇ m (l≅ h) = rl (λ n → rob {r = self n} {r′ = self n} (h n) (RΩ̇ m (h n)) (R-ι (self n) (self n) (RΩ̇ m (h n))))
RΩ̇ zero z≅ = rclo (∼ᶠ-refl fz)
  (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
  (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη)))
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
R-trˡ e (rwkˡ r) = rwkˡ (R-trˡ e r)
R-trˡ e (rwkʳ r) = rwkʳ (R-trˡ e r)
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
R-tr⁻ˡ e (rwkˡ r) = rwkˡ (R-tr⁻ˡ e r)
R-tr⁻ˡ e (rwkʳ r) = rwkʳ (R-tr⁻ˡ e r)
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
R-trʳ e (rwkˡ r) = rwkˡ (R-trʳ e r)
R-trʳ e (rwkʳ r) = rwkʳ (R-trʳ e r)
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
R-tr⁻ʳ e (rwkˡ r) = rwkˡ (R-tr⁻ʳ e r)
R-tr⁻ʳ e (rwkʳ r) = rwkʳ (R-tr⁻ʳ e r)
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
R-ψᵠ q q′ et (rwkˡ r) = rwkˡ (R-ψᵠ q q′ et r)
R-ψᵠ q q′ et (rwkʳ r) = rwkʳ (R-ψᵠ q q′ et r)
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
R-Ψ qH ok e p ok′ e′ p′ et (rwkˡ {lc = lc} r) = rwkˡ (R-Ψ qH ok (λ i h r₁ → lc i r₁ (e i h r₁)) p ok′ e′ p′ et r)
R-Ψ qH ok e p ok′ e′ p′ et (rwkʳ {lc′ = lc′} r) = rwkʳ (R-Ψ qH ok e p ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)) p′ et r)
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

## §6 求值

```agda
R→≈ᵠ : ∀ {m a b φ χ ψ ρ w w′} {x : Q m a φ χ} {x′ : Q m b ψ ρ} → Rq m a b x x′ → (ok : Ok w) (e : Eh zero m w χ) (ok′ : Ok w′) (e′ : Eh zero m w′ ρ) → ψ̄ᵠ ok e x ≈ᴿ ψ̄ᵠ ok′ e′ x′
R→≈ᵠ rz ok e ok′ e′ = wkR _ _ r∅
R→≈ᵠ (rs s c r) ok e ok′ e′ = sucR (R→≈ᵠ r ok e ok′ e′)
R→≈ᵠ (rl h) ok e ok′ e′ = limR (λ n → R→≈ᵠ (h n) ok e ok′ e′)
R→≈ᵠ (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) ok e ok′ e′ = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ᵠ ok e (f x)} {H′ = λ x → ψ̄ᵠ ok′ e′ (f′ x)} d (λ x y dd → R→≈ᵠ (h x y dd) ok e ok′ e′)
R→≈ᵠ (rŝ d r h) ok e ok′ e′ = ŝR d (R→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → R→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
R→≈ᵠ (rĉ d dz dg r h) ok e ok′ e′ = ĉR d dz dg (R→≈ᵠ r ok e ok′ e′) (λ η ee η′ e₁ dd → R→≈ᵠ (h η ee η′ e₁ dd) ok e ok′ e′)
R→≈ᵠ (rclo {t = t} {t′} {g} {g′} s r h) ok e ok′ e′ = cloR {t = ψ̄ᵠ ok e t} {g = λ η → ψ̄ᵠ ok e (g η)} {t′ = ψ̄ᵠ ok′ e′ t′} {g′ = λ η → ψ̄ᵠ ok′ e′ (g′ η)} s (R→≈ᵠ r ok e ok′ e′) (λ η η′ d → R→≈ᵠ (h η η′ d) ok e ok′ e′)
R→≈ᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} (rcl {n = n} {κ₁ = κ₁} {κ₂ = κ₂} {q = q} {s = s₁} {s′ = s₂} same s r h) ok e ok′ e′ =
  ŝR (bound-≅ (⊔∼ s (fk∼ z≅)) _ (zr ok n) _ (zr ok′ n) z≅) (R→≈ᵠ r ok e ok′ e′)
      (λ η d η′ d′ eη → R→≈ᵠ (h η η′ eη)
         (upd-ok n w ok (tt , λ x → lim 0 (proj₂ (evF B₁) x))) (λ i k r₁ → upd-ev n i w χ (evη κ₁ B₁ η d) (e i k r₁))
         (upd-ok n w′ ok′ (tt , λ x → lim 0 (proj₂ (evF B₂) x))) (λ i k r₁ → upd-ev n i w′ ρ (evη κ₂ B₂ η′ d′) (e′ i k r₁)))
  where
  B₁ = bound (κ₁ ⊔ fk zero) (s₁ (e n (Hi-0 n) q)) (zr ok n)
  B₂ = bound (κ₂ ⊔ fk zero) (s₂ (e′ n (Hi-0 n) q)) (zr ok′ n)
R→≈ᵠ (rwkˡ {le = le} {lc = lc} r) ok e ok′ e′ = wkR le (λ v → v) (R→≈ᵠ r ok (λ i h r₁ → lc i r₁ (e i h r₁)) ok′ e′)
R→≈ᵠ (rwkʳ {le′ = le′} {lc′ = lc′} r) ok e ok′ e′ = wkR (λ v → v) le′ (R→≈ᵠ r ok e ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)))
R→≈ᵠ (rob _ l r) ok e ok′ e′ = R→≈ᵠ r ok e ok′ e′
R→≈ᵠ (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {q = q} {fe = fe} {fe′} {ac} {ac′} {h} {h′} same ek s c f) ok e ok′ e′ =
  limR (λ i → wkR _ _ (R→≈ᵠ (f φ ψ (Z* χ) (Z* ρ) s (Z∼ (λ j r → c j (tr< r q))) (Z∼ (λ j r → c j (tr< r q))) _ _ (intoVq q (chRΨ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) ok′ (e⁺ n ok′ (e↓ e′)) (ac′ (e↓ e′ n (inj₁ refl) q)) {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {h = h} {h′ = h′} ek s c f i))) ok (e⁺ n ok e) ok′ (e⁺ n ok′ e′)))
R→≈ᵠ {m} (rΩ {φ = φ} {χ} {ψ} {ρ} {fe = fe} {fe′} {r} {r′} {h} {h′} ek s c f) ok e ok′ e′ =
  limR (λ i → wkR _ _ (R→≈ᵠ (f φ ψ (Z* χ) (Z* ρ) s (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s c f i))) ok (e⁺ m ok e) ok′ (e⁺ m ok′ e′)))
```
