# 序数高度: 跨世界的模拟

> **判决: HOLDS (对结构参数, 编译过; 条件是下面三个参数).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 由 `Survey/scripts/ladderord/mk_cross.py` 从 [LadderInfBridge](LadderInfBridge.lagda.md) 改写. 左边是 `LadderInfTree 𝕊`, 右边是 `LadderOrdTree 𝔹`. 参数: 保序映射 `e`, `ε`; 右边 `tri` 在对角线上是 `teq refl` (`tri-self`); 第 0 行的写法对齐 (`rowq`). 这些是结构参数, 每个实例都要闭合地给出. **`bridge m α α′ d : N.Tᵠ m α ≈ᴿ I.Tᵠ (e m) α′`**.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase using (HtS)
open import OCF.Align.LadderOrdBase
import OCF.Align.LadderOrdCrossEq as CE
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module OCF.Align.LadderOrdCross (𝕊 : HtS) (𝔹 : HtB) (e : HtS.Ht 𝕊 → HtB.Ht 𝔹) (ε : ∀ {n m} → HtS._<ᴸ_ 𝕊 n m → HtB._<ᴸ_ 𝔹 (e n) (e m))
  (tri-self : ∀ a → HtB.tri 𝔹 a a ≡ teq refl) (rowq : ∀ m → CE.RowEq 𝕊 𝔹 e ε m (HtS.view 𝕊 m)) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst; subst₂; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ; toZ)
open import OCF.Free.Aux using (tf)
open import OCF.Free.Eq using (_≅ᶻ_; _≅ˢ_; Eq₊ˢ; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ; ŝ≅; ĉ≅; ≅→Rˢ; Ωˢ-≅; toZ-≅; _≈ᴿ_; limR; sucR; limᵢR; ŝR; ĉR; cloR; wkR)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; flo; cvFlo; toFlo; wk; limA; ∅ᴿ; _∼ᶠ_; fz∼; fk∼; fb∼; ⊔∼; ∼ᶠ-refl; bound; bound-≅; evF)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
open import OCF.Free.Base using (clash; r∅)
import OCF.Align.LadderInfTree
import OCF.Align.LadderInfRel
import OCF.Align.LadderOrdTree
import OCF.Align.LadderOrdRel
module N = OCF.Align.LadderInfTree 𝕊
module NR = OCF.Align.LadderInfRel 𝕊
module I = OCF.Align.LadderOrdTree 𝔹
module IR = OCF.Align.LadderOrdRel 𝔹
open NR using (flo-∼)

-- 两边的三歧对齐: 只用 ε 保序, 右边 irr, 右边 < 是命题, 右边对角线
data Al : ∀ n H → Tri N._<ᴸ_ n H → Tri I._<ᴸ_ (e n) (e H) → Set where
  all : ∀ {n H} (l : n N.<ᴸ H) → Al n H (tlt l) (tlt (ε l))
  ale : ∀ {n} → Al n n (teq refl) (teq refl)
  alg : ∀ {n H} (l : H N.<ᴸ n) → Al n H (tgt l) (tgt (ε l))

al-lt : ∀ {n H} (l : n N.<ᴸ H) (t : Tri I._<ᴸ_ (e n) (e H)) → Al n H (tlt l) t
al-lt l (tlt l′) = subst (λ w → Al _ _ (tlt l) (tlt w)) (I.<-prop (ε l) l′) (all l)
al-lt {n} {H} l (teq x) = ⊥-elim (I.irr (subst (I._<ᴸ e H) x (ε l)))
al-lt l (tgt l′) = ⊥-elim (I.irr (I.tr< (ε l) l′))

al-gt : ∀ {n H} (l : H N.<ᴸ n) (t : Tri I._<ᴸ_ (e n) (e H)) → Al n H (tgt l) t
al-gt l (tgt l′) = subst (λ w → Al _ _ (tgt l) (tgt w)) (I.<-prop (ε l) l′) (alg l)
al-gt {n} {H} l (teq x) = ⊥-elim (I.irr (subst (e H I.<ᴸ_) x (ε l)))
al-gt l (tlt l′) = ⊥-elim (I.irr (I.tr< (ε l) l′))

al : ∀ n H → Al n H (N.tri n H) (I.tri (e n) (e H))
al n H with N.tri n H
... | tlt l = al-lt l (I.tri (e n) (e H))
... | tgt l = al-gt l (I.tri (e n) (e H))
... | teq refl = subst (Al n n (teq refl)) (sym (tri-self (e n))) ale

record Sm (m : N.Ht) (χ : N.Fv) (ρ : I.Fv) : Set where
  constructor sm
  field
    unSm : ∀ i → i N.<ᴸ m → χ i ∼ᶠ ρ (e i)
open Sm

sm↓ : ∀ {H m χ ρ} → H N.<ᴸ m → Sm m χ ρ → Sm H χ ρ
sm↓ qH s = sm (λ i q → unSm s i (N.tr< q qH))

module _ (m : N.Ht) (a b : Ordᴵ) (LR : ∀ {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → N.Q m k ξ ζ → I.Q (e m) k′ ξ′ ζ′ → Set)
         (Lv : ∀ {n} → n N.<ᴸ m → ∀ {k k′ ξ ζ ξ′ ζ′} → N.Q n k ξ ζ → I.Q (e n) k′ ξ′ ζ′ → Set) where
  data R₊ : ∀ {φ χ ψ ρ} → N.Q m a φ χ → I.Q (e m) b ψ ρ → Set where
    rz : ∀ {φ χ ψ ρ} → R₊ {φ} {χ} {ψ} {ρ} N.q0 I.q0
    rs : ∀ {φ χ ψ ρ} {p : N.Q m a φ χ} {p′ : I.Q (e m) b ψ ρ} → φ ∼ᶠ ψ → Sm m χ ρ → R₊ p p′ → R₊ (N.qs p) (I.qs p′)
    rl : ∀ {φ χ ψ ρ} {F : ℕ → N.Q m a φ χ} {F′ : ℕ → I.Q (e m) b ψ ρ} → (∀ n → R₊ (F n) (F′ n)) → R₊ (N.ql F) (I.ql F′)
    ri : ∀ {φ χ ψ ρ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → N.Q m a φ χ} {f′ : Ordˢ j′ → I.Q (e m) b ψ ρ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ˢ y → R₊ (f x) (f′ y)) → R₊ (N.qi ac f) (I.qi ac′ f′)
    rŝ : ∀ {φ χ ψ ρ c₁ c₂} {t : N.Q m a φ χ} {t′ : I.Q (e m) b ψ ρ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → N.Q m a φ χ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → I.Q (e m) b ψ ρ} →
         c₁ ≅ᴵ c₂ → R₊ t t′ → (∀ η ee η′ e′ → η ≅ᴵ η′ → R₊ (g η ee) (g′ η′ e′)) → R₊ (N.qŝ c₁ t g) (I.qŝ c₂ t′ g′)
    rĉ : ∀ {φ χ ψ ρ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : N.Q m a φ χ} {o₀′ : I.Q (e m) b ψ ρ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → N.Q m a φ χ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → I.Q (e m) b ψ ρ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η ee η′ e′ → η ≅ᴵ η′ → zg η ee ≅ᶻ zg′ η′ e′) → R₊ o₀ o₀′ →
         (∀ η ee η′ e′ → η ≅ᴵ η′ → R₊ (o η ee) (o′ η′ e′)) → R₊ (N.qĉ c₁ z zg o₀ o) (I.qĉ c₂ z′ zg′ o₀′ o′)
    rclo : ∀ {φ χ ψ ρ} {t : N.Q m a (φ ⊔ fk zero) χ} {t′ : I.Q (e m) b (ψ ⊔ fk zero) ρ} {g : (η : Ordᴵ) → N.Q m a (φ ⊔ fk η) χ} {g′ : (η : Ordᴵ) → I.Q (e m) b (ψ ⊔ fk η) ρ} →
         φ ∼ᶠ ψ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (N.qclo t g) (I.qclo t′ g′)
    rcl : ∀ {φ χ ψ ρ n κ₁ κ₂} {q : n N.<ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ (e n)) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : N.Q m a φ χ} {t′ : I.Q (e m) b ψ ρ} {g : (η : Ordᴵ) → N.Q m a φ (N.upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → I.Q (e m) b ψ (I.upd ρ (e n) (κ₂ ⊔ fk η))} →
         κ₁ ∼ᶠ κ₂ → R₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → R₊ (g η) (g′ η′)) → R₊ (N.qcl q κ₁ s t g) (I.qcl (ε q) κ₂ s′ t′ g′)
    rwkˡ : ∀ {φ φ′ χ χ′ ψ ρ} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : N.Sub m χ′ χ} {x : N.Q m a φ χ} {x′ : I.Q (e m) b ψ ρ} → R₊ x x′ → R₊ (N.qwk le lc x) x′
    rwkʳ : ∀ {φ χ ψ ψ′ ρ ρ′} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : I.Sub (e m) ρ′ ρ} {x : N.Q m a φ χ} {x′ : I.Q (e m) b ψ ρ} → R₊ x x′ → R₊ x (I.qwk le′ lc′ x′)
    rΩ↓ : ∀ {φ χ ψ ρ n k k′} {q : n N.<ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ (e n)) → k′ <ᴵ L}
          {h : ∀ ξ ζ → N.Vs m q k ξ ζ → N.Q m a (ξ ⊔ φ) (N.lo n ζ N.∪ χ)} {h′ : ∀ ξ ζ → I.Vs (e m) (ε q) k′ ξ ζ → I.Q (e m) b (ξ ⊔ ψ) (I.lo (e n) ζ I.∪ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sm m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sm n ζ ζ′ → (z : N.Q n k ξ ζ) (z′ : I.Q (e n) k′ ξ′ ζ′) → Lv q z z′ → R₊ (h ξ ζ (N.intoV q z)) (h′ ξ′ ζ′ (I.intoV (ε q) z′))) → R₊ (N.qΩ↓ q fe ac h) (I.qΩ↓ (ε q) fe′ ac′ h′)
    rΩ : ∀ {φ χ ψ ρ k k′} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r : k <ᴵ a} {r′ : k′ <ᴵ b}
         {h : ∀ ξ ζ → N.Us m k (<→◃ r) ξ ζ → N.Q m a (ξ ⊔ φ) (N.lo m ζ N.∪ χ)} {h′ : ∀ ξ ζ → I.Us (e m) k′ (<→◃ r′) ξ ζ → I.Q (e m) b (ξ ⊔ ψ) (I.lo (e m) ζ I.∪ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sm m χ ρ →
         (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sm m ζ ζ′ → (z : N.Q m k ξ ζ) (z′ : I.Q (e m) k′ ξ′ ζ′) → LR (<→◃ r) z z′ → R₊ (h ξ ζ (N.intoU (<→◃ r) z)) (h′ ξ′ ζ′ (I.intoU (<→◃ r′) z′))) → R₊ (N.qΩ fe r h) (I.qΩ fe′ r′ h′)
    rob : ∀ {φ χ ψ ρ k k′} {r : k ◃₁ a} {r′ : k′ ◃₁ b} {z : N.Us m k (◃₁→◃ r) φ χ} {z′ : I.Us (e m) k′ (◃₁→◃ r′) ψ ρ} {x : N.Q m a φ χ} {x′ : I.Q (e m) b ψ ρ} →
          k ≅ᴵ k′ → LR (◃₁→◃ r) (N.outU (◃₁→◃ r) z) (I.outU (◃₁→◃ r′) z′) → R₊ x x′ → R₊ (N.omk r z x) (I.omk r′ z′ x′)

XR : N.Ht → Set₁
XR n = ∀ {k k′ ξ ζ ξ′ ζ′} → N.Q n k ξ ζ → I.Q (e n) k′ ξ′ ζ′ → Set

RV : ∀ m (v : ∀ {n} → n N.<ᴸ m → XR n) a b {φ χ ψ ρ} → N.Q m a φ χ → I.Q (e m) b ψ ρ → Set
LRV : ∀ m (v : ∀ {n} → n N.<ᴸ m → XR n) a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → N.Q m k ξ ζ → I.Q (e m) k′ ξ′ ζ′ → Set
RV m v a b x y = R₊ m a b (LRV m v a) v x y
LRV m v (suc k)   zero      {k′} x y = RV m v k k′ x y
LRV m v (suc c)   (suc r)   x y = LRV m v c r x y
LRV m v (lim f s) (self n)  {k′} x y = RV m v (f n) k′ x y
LRV m v (lim f s) (lim n r) x y = LRV m v (f n) r x y

FR : ∀ m → (∀ {n} → n N.<ᴸ m → XR n) → XR m
FR m v {k} {k′} x y = RV m v k k′ x y

LVq : ∀ m {n} → n N.<ᴸ m → XR n
LVq = N.Rec XR FR

Rq : ∀ m a b {φ χ ψ ρ} → N.Q m a φ χ → I.Q (e m) b ψ ρ → Set
Rq m = RV m (LVq m)

LRq : ∀ m a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → N.Q m k ξ ζ → I.Q (e m) k′ ξ′ ζ′ → Set
LRq m = LRV m (LVq m)

outRq : ∀ {m c k} (r : k ◃ c) {k′ ξ ζ ξ′ ζ′} {z : N.Q m k ξ ζ} {z′ : I.Q (e m) k′ ξ′ ζ′} → LRq m c r z z′ → Rq m k k′ z z′
outRq zero      l = l
outRq (suc r)   l = outRq r l
outRq (self n)  l = l
outRq (lim n r) l = outRq r l

intoRq : ∀ {m c k} (r : k ◃ c) {k′ ξ ζ ξ′ ζ′} {z : N.Q m k ξ ζ} {z′ : I.Q (e m) k′ ξ′ ζ′} → Rq m k k′ z z′ → LRq m c r z z′
intoRq zero      l = l
intoRq (suc r)   l = intoRq r l
intoRq (self n)  l = l
intoRq (lim n r) l = intoRq r l

outVq : ∀ {m n} (q : n N.<ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : N.Q n k ξ ζ} {z′ : I.Q (e n) k′ ξ′ ζ′} → LVq m q z z′ → Rq n k k′ z z′
outVq {m} q {z = z} {z′ = z′} l = subst (λ X → X z z′) (N.Rec-β XR FR m q) l

intoVq : ∀ {m n} (q : n N.<ᴸ m) {k k′ ξ ζ ξ′ ζ′} {z : N.Q n k ξ ζ} {z′ : I.Q (e n) k′ ξ′ ζ′} → Rq n k k′ z z′ → LVq m q z z′
intoVq {m} q {z = z} {z′ = z′} l = subst (λ X → X z z′) (sym (N.Rec-β XR FR m q)) l

rwk : ∀ {m a b φ φ′ χ χ′ ψ ψ′ ρ ρ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : N.Sub m χ′ χ} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : I.Sub (e m) ρ′ ρ}
      {x : N.Q m a φ χ} {x′ : I.Q (e m) b ψ ρ} → Rq m a b x x′ → Rq m a b (N.qwk le lc x) (I.qwk le′ lc′ x′)
rwk r = rwkˡ (rwkʳ r)

Z∼ : ∀ {m χ ρ} → Sm m χ ρ → Sm m (N.Z* χ) (I.Z* ρ)
Z∼ s = sm (λ i q → ⊔∼ (∼ᶠ-refl Fl) (unSm s i q))

∪∼ : ∀ {m a b χ ρ} → Sm m a b → Sm m χ ρ → Sm m (a N.∪ χ) (b I.∪ ρ)
∪∼ s c = sm (λ i q → ⊔∼ (unSm s i q) (unSm c i q))

R-⊞ : ∀ {m a b φ χ φ′ χ′ ψ ρ ψ′ ρ′} {W : N.Q m a φ χ} {W′ : I.Q (e m) b φ′ χ′} {t : N.Q m a ψ ρ} {t′ : I.Q (e m) b ψ′ ρ′} → φ ∼ᶠ φ′ → Sm m χ χ′ → Rq m a b W W′ → Rq m a b t t′ → Rq m a b (W N.⊞ t) (W′ I.⊞ t′)
R-⊞ s c rW rz = rwk rW
R-⊞ s c rW (rs sa sb r) = rs (⊔∼ s sa) (∪∼ c sb) (R-⊞ s c rW r)
R-⊞ s c rW (rl h) = rl (λ n → R-⊞ s c rW (h n))
R-⊞ s c rW (ri e₁ h) = ri e₁ (λ x y d → R-⊞ s c rW (h x y d))
R-⊞ s c rW (rŝ e₁ r h) = rŝ e₁ (R-⊞ s c rW r) (λ η ee η′ e′ d → R-⊞ s c rW (h η ee η′ e′ d))
R-⊞ s c rW (rĉ e₁ dz dg r h) = rĉ e₁ dz dg (R-⊞ s c rW r) (λ η ee η′ e′ d → R-⊞ s c rW (h η ee η′ e′ d))
R-⊞ s c rW (rclo sψ r h) = rwk (rclo (⊔∼ s sψ) (rwk (R-⊞ s c rW r)) (λ η η′ d → rwk (R-⊞ s c rW (h η η′ d))))
R-⊞ s c rW (rcl {q = q} sψ r h) = rcl {q = q} (⊔∼ (unSm c _ q) sψ) (R-⊞ s c rW r) (λ η η′ d → rwk (R-⊞ s c rW (h η η′ d)))
R-⊞ s c rW (rwkˡ r) = rwkˡ (R-⊞ s c rW r)
R-⊞ s c rW (rwkʳ r) = rwkʳ (R-⊞ s c rW r)
R-⊞ s c rW (rΩ↓ ek sψ cψ f) = rΩ↓ ek (⊔∼ s sψ) (∪∼ c cψ) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-⊞ s c rW (f ξ ξ′ ζ ζ′ d dc z z′ l)))
R-⊞ s c rW (rΩ ek sψ cψ f) = rΩ ek (⊔∼ s sψ) (∪∼ c cψ) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-⊞ s c rW (f ξ ξ′ ζ ζ′ d dc z z′ l)))
R-⊞ s c rW (rob _ l r) = R-⊞ s c rW r

R-ι : ∀ {m a b c d φ χ ψ ρ} (q : a ◃ c) (q′ : b ◃ d) {x : N.Q m a φ χ} {x′ : I.Q (e m) b ψ ρ} → Rq m a b x x′ → Rq m c d (N.ι q x) (I.ι q′ x′)
R-ι q q′ rz = rz
R-ι q q′ (rs sa sb r) = rs sa sb (R-ι q q′ r)
R-ι q q′ (rl h) = rl (λ n → R-ι q q′ (h n))
R-ι q q′ (ri e₁ h) = ri e₁ (λ x y d → R-ι q q′ (h x y d))
R-ι q q′ (rŝ e₁ r h) = rŝ e₁ (R-ι q q′ r) (λ η ee η′ e′ d → R-ι q q′ (h η ee η′ e′ d))
R-ι q q′ (rĉ e₁ dz dg r h) = rĉ e₁ dz dg (R-ι q q′ r) (λ η ee η′ e′ d → R-ι q q′ (h η ee η′ e′ d))
R-ι q q′ (rclo s r h) = rclo s (R-ι q q′ r) (λ η η′ d → R-ι q q′ (h η η′ d))
R-ι q q′ (rcl s r h) = rcl s (R-ι q q′ r) (λ η η′ d → R-ι q q′ (h η η′ d))
R-ι q q′ (rwkˡ r) = rwkˡ (R-ι q q′ r)
R-ι q q′ (rwkʳ r) = rwkʳ (R-ι q q′ r)
R-ι q q′ (rΩ↓ ek s c f) = rΩ↓ ek s c (λ ξ ξ′ ζ ζ′ d dc z z′ l → R-ι q q′ (f ξ ξ′ ζ ζ′ d dc z z′ l))
R-ι {m} {c = c} {d = dd} q q′ (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s c′ f) =
  rΩ {r = <◃ r q} {r′ = <◃ r′ q′} ek s c′
     (λ ξ ξ′ ζ ζ′ e₁ dc z z′ l → subst₂ (λ w w′ → Rq m c dd (N.ι q (h ξ ζ (N.intoU (<→◃ r) w))) (I.ι q′ (h′ ξ′ ζ′ (I.intoU (<→◃ r′) w′)))) (sym (NR.out-intoU (<→◃ (<◃ r q)) z)) (sym (IR.out-intoU (<→◃ (<◃ r′ q′)) z′))
                                (R-ι q q′ (f ξ ξ′ ζ ζ′ e₁ dc _ _ (intoRq (<→◃ r) (outRq (<→◃ (<◃ r q)) l)))))
R-ι q q′ (rob _ l r) = R-ι q q′ r

-- 两边三歧对齐
cap∼ : ∀ {m χ ρ x y} n → Sm n χ ρ → x ∼ᶠ y → Sm m (N.cap χ n x) (I.cap ρ (e n) y)
cap∼ {m} {χ} {ρ} {x} {y} n s c = sm go
  where
  go : ∀ i → i N.<ᴸ m → N.cap χ n x i ∼ᶠ I.cap ρ (e n) y (e i)
  go i q with N.tri i n
  ... | tlt l = subst₂ _∼ᶠ_ refl (sym (I.cap-lt ρ y (ε l))) (unSm s i l)
  ... | teq refl = subst₂ _∼ᶠ_ refl (sym (I.cap-self ρ (e n) y)) c
  ... | tgt l = subst₂ _∼ᶠ_ refl (sym (I.cap-gt ρ y (ε l))) fz∼

-- 右边的节点号只差命题相等
R-Ω↓-castʳ : ∀ {m a b n k k′ φ χ ψ ρ} {q : n N.<ᴸ m} {Q₂ : e n I.<ᴸ e m} → Q₂ ≡ ε q → {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {ac′ : ∀ {L} → Ev L (ρ (e n)) → k′ <ᴵ L}
          {h : ∀ ξ ζ → N.Vs m q k ξ ζ → N.Q m a (ξ ⊔ φ) (N.lo n ζ N.∪ χ)} {h′ : ∀ ξ ζ → I.Vs (e m) Q₂ k′ ξ ζ → I.Q (e m) b (ξ ⊔ ψ) (I.lo (e n) ζ I.∪ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → Sm m χ ρ →
          (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sm n ζ ζ′ → (z : N.Q n k ξ ζ) (z′ : I.Q (e n) k′ ξ′ ζ′) → LVq m q z z′ → Rq m a b (h ξ ζ (N.intoV q z)) (h′ ξ′ ζ′ (I.intoV Q₂ z′))) → Rq m a b (N.qΩ↓ q fe ac h) (I.qΩ↓ Q₂ fe′ ac′ h′)
R-Ω↓-castʳ refl ek s c f = rΩ↓ ek s c f

R-cl-castʳ : ∀ {m a b n κ₁ κ₂ φ χ ψ ρ} {q : n N.<ᴸ m} {Q₂ : e n I.<ᴸ e m} → Q₂ ≡ ε q → {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (κ₁ ⊔ fk zero)} {s′ : ∀ {ℓ} → Ev ℓ (ρ (e n)) → Ev ℓ (κ₂ ⊔ fk zero)}
         {t : N.Q m a φ χ} {t′ : I.Q (e m) b ψ ρ} {g : (η : Ordᴵ) → N.Q m a φ (N.upd χ n (κ₁ ⊔ fk η))} {g′ : (η : Ordᴵ) → I.Q (e m) b ψ (I.upd ρ (e n) (κ₂ ⊔ fk η))} →
         κ₁ ∼ᶠ κ₂ → Rq m a b t t′ → (∀ η η′ → η ≅ᴵ η′ → Rq m a b (g η) (g′ η′)) → Rq m a b (N.qcl q κ₁ s t g) (I.qcl Q₂ κ₂ s′ t′ g′)
R-cl-castʳ refl e₂ r h = rcl e₂ r h

R-ι↓ : ∀ {n m k k′ α α′ φ ψ χ ρ} (dq : n N.<ᴸ m) → k ≅ᴵ k′ → {x : N.Q n k φ χ} {x′ : I.Q (e n) k′ ψ ρ} → Rq n k k′ x x′ → Rq m α α′ (N.ι↓ dq x) (I.ι↓ (ε dq) x′)
R-ι↓ dq ek rz = rz
R-ι↓ {n = n} dq ek (rs sa sb r) = rs sa (cap∼ n sb (flo-∼ ek)) (R-ι↓ dq ek r)
R-ι↓ dq ek (rl h) = rl (λ n → R-ι↓ dq ek (h n))
R-ι↓ dq ek (ri e₁ h) = ri e₁ (λ x y d → R-ι↓ dq ek (h x y d))
R-ι↓ dq ek (rŝ e₁ r h) = rŝ e₁ (R-ι↓ dq ek r) (λ η ee η′ e′ d → R-ι↓ dq ek (h η ee η′ e′ d))
R-ι↓ dq ek (rĉ e₁ dz dg r h) = rĉ e₁ dz dg (R-ι↓ dq ek r) (λ η ee η′ e′ d → R-ι↓ dq ek (h η ee η′ e′ d))
R-ι↓ dq ek (rclo s r h) = rclo s (R-ι↓ dq ek r) (λ η η′ d → R-ι↓ dq ek (h η η′ d))
R-ι↓ dq ek (rcl {q = q} s r h) = R-cl-castʳ {q = N.tr< q dq} (I.<-prop _ _) s (R-ι↓ dq ek r) (λ η η′ d → rwk (R-ι↓ dq ek (h η η′ d)))
R-ι↓ dq ek (rwkˡ r) = rwkˡ (R-ι↓ dq ek r)
R-ι↓ dq ek (rwkʳ r) = rwkʳ (R-ι↓ dq ek r)
R-ι↓ {n = n} {m = m} {α = α} {α′ = α′} dq ek (rΩ↓ {q = q} {h = h} {h′ = h′} ei s c f) =
  R-Ω↓-castʳ {q = N.tr< q dq} (I.<-prop _ _) ei s (cap∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk
    (subst₂ (λ u v → Rq m α α′ (N.ι↓ dq (h ξ ζ (N.intoV q u))) (I.ι↓ (ε dq) (h′ ξ′ ζ′ (I.intoV (ε q) v)))) (sym (N.out-intoV (N.tr< q dq) z)) (sym (I.out-intoV (I.tr< (ε q) (ε dq)) z′))
      (R-ι↓ dq ek (f ξ ξ′ ζ ζ′ d dc _ _ (intoVq q (outVq (N.tr< q dq) l))))))
R-ι↓ {n = n} {m = m} {α = α} {α′ = α′} dq ek (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ei s c f) =
  rΩ↓ {q = dq} ei s (cap∼ n c (flo-∼ ek)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk
    (subst₂ (λ u v → Rq m α α′ (N.ι↓ dq (h ξ ζ (N.intoU (<→◃ r) u))) (I.ι↓ (ε dq) (h′ ξ′ ζ′ (I.intoU (<→◃ r′) v)))) (sym (N.out-intoV dq z)) (sym (I.out-intoV (ε dq) z′))
      (R-ι↓ dq ek (f ξ ξ′ ζ ζ′ d dc _ _ (intoRq (<→◃ r) (outVq dq l))))))
R-ι↓ dq (s≅ e₁) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓ dq ea l)
R-ι↓ dq (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ dq ea l)

R-tl : ∀ {c c′ k₁ k₂ χ ρ} {cv : ∀ {L} → Ev L (flo k₁) → Simᴵ k₁ L} {cv′ : ∀ {L} → Ev L (flo k₂) → Simᴵ k₂ L} {a : Ordˢ k₁} {b : Ordˢ k₂} →
       a ≅ˢ b → Rq N.h₀ c c′ (N.tl {χ = χ} (flo k₁) cv a) (I.tl {χ = ρ} (flo k₂) cv′ b)
R-tl z≅ = rz
R-tl (s≅ le e₁) = rs (flo-∼ le) (sm (λ i q → ⊥-elim (N.no< q))) (R-tl e₁)
R-tl (l≅ h) = rl (λ n → R-tl (h n))
R-tl (lᵢ≅ {p = q} e₁ h) = ri e₁ (λ x y dd → R-tl (h x y (≅→Rˢ (<→◃ q) dd)))
R-tl {k₁ = suc k′} (upˡ {r = zero} d) = rwkˡ (R-tl d)
R-tl {k₁ = lim f s} (upˡ {r = self n} d) = rwkˡ (R-tl d)
R-tl {k₂ = suc k′} (upʳ {r = zero} d) = rwkʳ (R-tl d)
R-tl {k₂ = lim f s} (upʳ {r = self n} d) = rwkʳ (R-tl d)
R-tl {k₁ = zero} {k₂ = zero} (ŝ≅ k ec et eg) =
  rĉ ec (toZ-≅ et) (λ η e₁ η′ e′ eη → toZ-≅ (eg η e₁ η′ e′ eη)) (R-tl et) (λ η e₁ η′ e′ eη → R-tl (eg η e₁ η′ e′ eη))
R-tl {k₁ = zero} {k₂ = suc _}   (ŝ≅ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = zero} {k₂ = lim _ _} (ŝ≅ k ec et eg) = ⊥-elim (tf k)
R-tl {k₁ = suc _}   {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = lim _ _} {k₂ = zero} (ŝ≅ k ec et eg) = ⊥-elim (tf (sym k))
R-tl {k₁ = suc _} {k₂ = suc _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e₁ η′ e′ eη → R-tl (eg η e₁ η′ e′ eη))
R-tl {k₁ = suc _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e₁ η′ e′ eη → R-tl (eg η e₁ η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = suc _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e₁ η′ e′ eη → R-tl (eg η e₁ η′ e′ eη))
R-tl {k₁ = lim _ _} {k₂ = lim _ _} (ŝ≅ k ec et eg) = rŝ ec (R-tl et) (λ η e₁ η′ e′ eη → R-tl (eg η e₁ η′ e′ eη))
R-tl (ĉ≅ ec dt dg eo eO) = rĉ ec dt dg (R-tl eo) (λ η e₁ η′ e′ eη → R-tl (eO η e₁ η′ e′ eη))

R-tlΩ : ∀ {c c′ η η′ φ φ′ χ ρ} {cv : ∀ {L} → Ev L φ → Simᴵ η L} {cv′ : ∀ {L} → Ev L φ′ → Simᴵ η′ L} → η ≅ᴵ η′ → φ ∼ᶠ φ′ → Rq N.h₀ c c′ (N.tl {χ = χ} φ cv (Ωˢ η)) (I.tl {χ = ρ} φ′ cv′ (Ωˢ η′))
R-tlΩ z≅ s = rs s (sm (λ i q → ⊥-elim (N.no< q))) rz
R-tlΩ (s≅ e₁) s = ri e₁ (λ x y d → rwk (R-tl d))
R-tlΩ (l≅ h) s = rl (λ n → rwk (R-tl (Ωˢ-≅ (h n))))

Fl∼ : ∀ {m} → Sm m (N.κ Fl) (I.κ Fl)
Fl∼ = sm (λ i q → ∼ᶠ-refl Fl)

-- 主定理的树: 两边的 Ω̇ 互模拟
XRΩ : N.Ht → Set
XRΩ m = ∀ {a b} → a ≅ᴵ b → Rq m a b (N.Ω̇ m a) (I.Ω̇ (e m) b)

R-rowC : ∀ {m n} (q : n N.<ᴸ m) → XRΩ n → Rq m zero zero (N.rowC q (N.Ω̇ n)) (I.rowC (ε q) (I.Ω̇ (e n)))
R-rowC q I₁ = rcl {q = q} fz∼ (rwk (R-ι↓ q (s≅ z≅) (I₁ (s≅ z≅)))) (λ η η′ eη → rwk (R-ι↓ q eη (I₁ eη)))

R-𝟏L : ∀ {m} → Rq m zero zero (N.𝟏L {m}) (I.𝟏L {e m})
R-𝟏L = rwk (rs fz∼ (sm (λ i q → fz∼)) rz)

R-stepL : ∀ {m n} (q : n N.<ᴸ m) → XRΩ n → Rq m zero zero (N.stepL q (N.Ω̇ n)) (I.stepL (ε q) (I.Ω̇ (e n)))
R-stepL q I₁ = rwk (R-ι↓ q z≅ (I₁ z≅))

R-rowL : ∀ {m} F (qs₁ : ∀ i → F i N.<ᴸ m) → (∀ {n} → n N.<ᴸ m → XRΩ n) → ∀ i →
         Rq m zero zero (N.rowL F qs₁ (λ i₁ → N.ΩI m (qs₁ i₁)) i) (I.rowL (λ i₁ → e (F i₁)) (λ i₁ → ε (qs₁ i₁)) (λ i₁ → I.ΩI (e m) (ε (qs₁ i₁))) i)
R-rowL F qs₁ I₁ zero = R-𝟏L
R-rowL {m} F qs₁ I₁ (suc i) = subst₂ (λ X Y → Rq m zero zero (N.stepL (qs₁ i) X) (I.stepL (ε (qs₁ i)) Y)) (sym (N.ΩI≡ (qs₁ i))) (sym (I.ΩI≡ (ε (qs₁ i)))) (R-stepL (qs₁ i) (I₁ (qs₁ i)))

R-row : ∀ m → (∀ {n} → n N.<ᴸ m → XRΩ n) → (v : View N._<ᴸ_ N.h₀ m) → CE.RowEq 𝕊 𝔹 e ε m v → Rq m zero zero (N.rowV m (N.ΩI m) v) (I.Ω̇ (e m) zero)
R-row _ I₁ base rq = subst (Rq N.h₀ zero zero (N.rowB {N.h₀})) (sym rq)
  (rclo (∼ᶠ-refl fz)
    (R-tlΩ (≅ᴵ-refl (suc zero)) (⊔∼ (∼ᶠ-refl fz) (fk∼ z≅)))
    (λ η η′ eη → R-tlΩ eη (⊔∼ (∼ᶠ-refl fz) (fk∼ eη))))
R-row m I₁ (clos q) rq = subst (Rq m zero zero (N.rowC q (N.ΩI m q))) (sym (cong (I.rowV (e m) (I.ΩI (e m))) rq))
  (subst₂ (λ X Y → Rq m zero zero (N.rowC q X) (I.rowC (ε q) Y)) (sym (N.ΩI≡ q)) (sym (I.ΩI≡ (ε q))) (R-rowC q (I₁ q)))
R-row m I₁ (chain F qs₁) rq = subst (Rq m zero zero (N.ql (N.rowL F qs₁ (λ i → N.ΩI m (qs₁ i))))) (sym (cong (I.rowV (e m) (I.ΩI (e m))) rq))
  (rl (R-rowL F qs₁ I₁))

FRΩ : ∀ m → (∀ {n} → n N.<ᴸ m → XRΩ n) → XRΩ m
FRΩ m I₁ (s≅ e₁) = rΩ e₁ (⊔∼ fz∼ (fk∼ z≅)) Fl∼ (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (rob {r = zero} {r′ = zero} e₁ l (R-ι zero zero l)))
FRΩ m I₁ (l≅ h) = rl (λ n → rob {r = self n} {r′ = self n} (h n) (FRΩ m I₁ (h n)) (R-ι (self n) (self n) (FRΩ m I₁ (h n))))
FRΩ m I₁ z≅ = R-row m I₁ (N.view m) (rowq m)

RΩ̇ : ∀ m {a b} → a ≅ᴵ b → Rq m a b (N.Ω̇ m a) (I.Ω̇ (e m) b)
RΩ̇ m = FRΩ m (N.Rec XRΩ FRΩ m)

R-trˡ  : ∀ {m a a′ b φ χ ψ ρ} (e₁ : a ≅ᴵ a′) {x : N.Q m a φ χ} {y : I.Q (e m) b ψ ρ} → Rq m a b x y → Rq m a′ b (N.trQ e₁ x) y
R-tr⁻ˡ : ∀ {m a a′ b φ χ ψ ρ} (e₁ : a′ ≅ᴵ a) {x : N.Q m a φ χ} {y : I.Q (e m) b ψ ρ} → Rq m a b x y → Rq m a′ b (N.tr⁻Q e₁ x) y
R-resˡ : ∀ {m j a a′ b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e₁ : a ≅ᴵ a′) {z : N.Q m (N.repQ (N.resQ q e₁)) ξ ζ} {y : I.Q (e m) b ξ′ ζ′} → Rq m _ b z y → Rq m j b (N.backQ (N.resQ q e₁) z) y
R-res⁻ˡ : ∀ {m j a a′ b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e₁ : a′ ≅ᴵ a) {z : N.Q m (N.repQ (N.res⁻Q q e₁)) ξ ζ} {y : I.Q (e m) b ξ′ ζ′} → Rq m _ b z y → Rq m j b (N.backQ (N.res⁻Q q e₁) z) y

R-trˡ e₁ rz = rz
R-trˡ e₁ (rs sa sb r) = rs sa sb (R-trˡ e₁ r)
R-trˡ e₁ (rl h) = rl (λ m → R-trˡ e₁ (h m))
R-trˡ e₁ (ri ej h) = ri ej (λ x y d → R-trˡ e₁ (h x y d))
R-trˡ e₁ (rŝ ec r h) = rŝ ec (R-trˡ e₁ r) (λ η ee η′ e′ d → R-trˡ e₁ (h η ee η′ e′ d))
R-trˡ e₁ (rĉ ec dz dg r h) = rĉ ec dz dg (R-trˡ e₁ r) (λ η ee η′ e′ d → R-trˡ e₁ (h η ee η′ e′ d))
R-trˡ e₁ (rclo s r h) = rclo s (R-trˡ e₁ r) (λ η η′ d → R-trˡ e₁ (h η η′ d))
R-trˡ e₁ (rcl s r h) = rcl s (R-trˡ e₁ r) (λ η η′ d → R-trˡ e₁ (h η η′ d))
R-trˡ e₁ (rwkˡ r) = rwkˡ (R-trˡ e₁ r)
R-trˡ e₁ (rwkʳ r) = rwkʳ (R-trˡ e₁ r)
R-trˡ e₁ (rΩ↓ ek s c f) = rΩ↓ ek s c (λ ξ ξ′ ζ ζ′ d dc z z′ l → R-trˡ e₁ (f ξ ξ′ ζ ζ′ d dc z z′ l))
R-trˡ (s≅ e₁) (rob {r = zero} ek l r) = rob (≅ᴵ-trans (≅ᴵ-sym e₁) ek) (R-trˡ e₁ l) (R-trˡ (s≅ e₁) r)
R-trˡ (l≅ h) (rob {r = self n} ek l r) = rob (≅ᴵ-trans (≅ᴵ-sym (h n)) ek) (R-trˡ (h n) l) (R-trˡ (l≅ h) r)
R-trˡ {m} {a′ = a′} {b} e₁ (rΩ {r = q} {r′} {h} {h′} ek s c f) =
  rΩ {r = N.ltQ (N.resQ q e₁)} (≅ᴵ-trans (≅ᴵ-sym (N.eqQ (N.resQ q e₁))) ek) s c
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rq m a′ b (N.trQ e₁ (h ξ ζ (N.intoU (<→◃ q) (N.backQ (N.resQ q e₁) w)))) (h′ ξ′ ζ′ (I.intoU (<→◃ r′) z′))) (sym (NR.out-intoU (<→◃ (N.ltQ (N.resQ q e₁))) z))
                              (R-trˡ e₁ (f ξ ξ′ ζ ζ′ d dc _ z′ (intoRq (<→◃ q) (R-resˡ q e₁ (outRq (<→◃ (N.ltQ (N.resQ q e₁))) l))))))

R-tr⁻ˡ e₁ rz = rz
R-tr⁻ˡ e₁ (rs sa sb r) = rs sa sb (R-tr⁻ˡ e₁ r)
R-tr⁻ˡ e₁ (rl h) = rl (λ m → R-tr⁻ˡ e₁ (h m))
R-tr⁻ˡ e₁ (ri ej h) = ri ej (λ x y d → R-tr⁻ˡ e₁ (h x y d))
R-tr⁻ˡ e₁ (rŝ ec r h) = rŝ ec (R-tr⁻ˡ e₁ r) (λ η ee η′ e′ d → R-tr⁻ˡ e₁ (h η ee η′ e′ d))
R-tr⁻ˡ e₁ (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ˡ e₁ r) (λ η ee η′ e′ d → R-tr⁻ˡ e₁ (h η ee η′ e′ d))
R-tr⁻ˡ e₁ (rclo s r h) = rclo s (R-tr⁻ˡ e₁ r) (λ η η′ d → R-tr⁻ˡ e₁ (h η η′ d))
R-tr⁻ˡ e₁ (rcl s r h) = rcl s (R-tr⁻ˡ e₁ r) (λ η η′ d → R-tr⁻ˡ e₁ (h η η′ d))
R-tr⁻ˡ e₁ (rwkˡ r) = rwkˡ (R-tr⁻ˡ e₁ r)
R-tr⁻ˡ e₁ (rwkʳ r) = rwkʳ (R-tr⁻ˡ e₁ r)
R-tr⁻ˡ e₁ (rΩ↓ ek s c f) = rΩ↓ ek s c (λ ξ ξ′ ζ ζ′ d dc z z′ l → R-tr⁻ˡ e₁ (f ξ ξ′ ζ ζ′ d dc z z′ l))
R-tr⁻ˡ (s≅ e₁) (rob {r = zero} ek l r) = rob (≅ᴵ-trans e₁ ek) (R-tr⁻ˡ e₁ l) (R-tr⁻ˡ (s≅ e₁) r)
R-tr⁻ˡ (l≅ h) (rob {r = self n} ek l r) = rob (≅ᴵ-trans (h n) ek) (R-tr⁻ˡ (h n) l) (R-tr⁻ˡ (l≅ h) r)
R-tr⁻ˡ {m} {a′ = a′} {b} e₁ (rΩ {r = q} {r′} {h} {h′} ek s c f) =
  rΩ {r = N.ltQ (N.res⁻Q q e₁)} (≅ᴵ-trans (≅ᴵ-sym (N.eqQ (N.res⁻Q q e₁))) ek) s c
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rq m a′ b (N.tr⁻Q e₁ (h ξ ζ (N.intoU (<→◃ q) (N.backQ (N.res⁻Q q e₁) w)))) (h′ ξ′ ζ′ (I.intoU (<→◃ r′) z′))) (sym (NR.out-intoU (<→◃ (N.ltQ (N.res⁻Q q e₁))) z))
                              (R-tr⁻ˡ e₁ (f ξ ξ′ ζ ζ′ d dc _ z′ (intoRq (<→◃ q) (R-res⁻ˡ q e₁ (outRq (<→◃ (N.ltQ (N.res⁻Q q e₁))) l))))))

R-resˡ zero      (s≅ e₁) l = R-tr⁻ˡ e₁ l
R-resˡ (suc q)   (s≅ e₁) l = R-resˡ q e₁ l
R-resˡ (lim n q) (l≅ h) l = R-resˡ q (h n) l

R-res⁻ˡ zero      (s≅ e₁) l = R-trˡ e₁ l
R-res⁻ˡ (suc q)   (s≅ e₁) l = R-res⁻ˡ q e₁ l
R-res⁻ˡ (lim n q) (l≅ h) l = R-res⁻ˡ q (h n) l

R-trʳ  : ∀ {m a b b′ φ χ ψ ρ} (e₁ : b ≅ᴵ b′) {x : N.Q m a φ χ} {y : I.Q (e m) b ψ ρ} → Rq m a b x y → Rq m a b′ x (I.trQ e₁ y)
R-tr⁻ʳ : ∀ {m a b b′ φ χ ψ ρ} (e₁ : b′ ≅ᴵ b) {x : N.Q m a φ χ} {y : I.Q (e m) b ψ ρ} → Rq m a b x y → Rq m a b′ x (I.tr⁻Q e₁ y)
R-resʳ : ∀ {m j a b b′ ξ ζ ξ′ ζ′} (q : j <ᴵ b) (e₁ : b ≅ᴵ b′) {z : N.Q m a ξ ζ} {y : I.Q (e m) (I.repQ (I.resQ q e₁)) ξ′ ζ′} → Rq m a _ z y → Rq m a j z (I.backQ (I.resQ q e₁) y)
R-res⁻ʳ : ∀ {m j a b b′ ξ ζ ξ′ ζ′} (q : j <ᴵ b) (e₁ : b′ ≅ᴵ b) {z : N.Q m a ξ ζ} {y : I.Q (e m) (I.repQ (I.res⁻Q q e₁)) ξ′ ζ′} → Rq m a _ z y → Rq m a j z (I.backQ (I.res⁻Q q e₁) y)

R-trʳ e₁ rz = rz
R-trʳ e₁ (rs sa sb r) = rs sa sb (R-trʳ e₁ r)
R-trʳ e₁ (rl h) = rl (λ m → R-trʳ e₁ (h m))
R-trʳ e₁ (ri ej h) = ri ej (λ x y d → R-trʳ e₁ (h x y d))
R-trʳ e₁ (rŝ ec r h) = rŝ ec (R-trʳ e₁ r) (λ η ee η′ e′ d → R-trʳ e₁ (h η ee η′ e′ d))
R-trʳ e₁ (rĉ ec dz dg r h) = rĉ ec dz dg (R-trʳ e₁ r) (λ η ee η′ e′ d → R-trʳ e₁ (h η ee η′ e′ d))
R-trʳ e₁ (rclo s r h) = rclo s (R-trʳ e₁ r) (λ η η′ d → R-trʳ e₁ (h η η′ d))
R-trʳ e₁ (rcl s r h) = rcl s (R-trʳ e₁ r) (λ η η′ d → R-trʳ e₁ (h η η′ d))
R-trʳ e₁ (rwkˡ r) = rwkˡ (R-trʳ e₁ r)
R-trʳ e₁ (rwkʳ r) = rwkʳ (R-trʳ e₁ r)
R-trʳ e₁ (rΩ↓ ek s c f) = rΩ↓ ek s c (λ ξ ξ′ ζ ζ′ d dc z z′ l → R-trʳ e₁ (f ξ ξ′ ζ ζ′ d dc z z′ l))
R-trʳ (s≅ e₁) (rob {r = zero} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek e₁) (R-trʳ e₁ l) (R-trʳ (s≅ e₁) r)
R-trʳ (s≅ e₁) (rob {r = self i} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek e₁) (R-trʳ e₁ l) (R-trʳ (s≅ e₁) r)
R-trʳ (l≅ h) (rob {r = zero} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (h n)) (R-trʳ (h n) l) (R-trʳ (l≅ h) r)
R-trʳ (l≅ h) (rob {r = self i} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (h n)) (R-trʳ (h n) l) (R-trʳ (l≅ h) r)
R-trʳ {m} {a} {b′ = b′} e₁ (rΩ {r = r} {r′ = q} {h} {h′} ek s c f) =
  rΩ {r = r} {r′ = I.ltQ (I.resQ q e₁)} (≅ᴵ-trans ek (I.eqQ (I.resQ q e₁))) s c
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rq m a b′ (h ξ ζ (N.intoU (<→◃ r) z)) (I.trQ e₁ (h′ ξ′ ζ′ (I.intoU (<→◃ q) (I.backQ (I.resQ q e₁) w))))) (sym (IR.out-intoU (<→◃ (I.ltQ (I.resQ q e₁))) z′))
                              (R-trʳ e₁ (f ξ ξ′ ζ ζ′ d dc z _ (intoRq (<→◃ r) (R-resʳ q e₁ (outRq (<→◃ r) l))))))

R-tr⁻ʳ e₁ rz = rz
R-tr⁻ʳ e₁ (rs sa sb r) = rs sa sb (R-tr⁻ʳ e₁ r)
R-tr⁻ʳ e₁ (rl h) = rl (λ m → R-tr⁻ʳ e₁ (h m))
R-tr⁻ʳ e₁ (ri ej h) = ri ej (λ x y d → R-tr⁻ʳ e₁ (h x y d))
R-tr⁻ʳ e₁ (rŝ ec r h) = rŝ ec (R-tr⁻ʳ e₁ r) (λ η ee η′ e′ d → R-tr⁻ʳ e₁ (h η ee η′ e′ d))
R-tr⁻ʳ e₁ (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ʳ e₁ r) (λ η ee η′ e′ d → R-tr⁻ʳ e₁ (h η ee η′ e′ d))
R-tr⁻ʳ e₁ (rclo s r h) = rclo s (R-tr⁻ʳ e₁ r) (λ η η′ d → R-tr⁻ʳ e₁ (h η η′ d))
R-tr⁻ʳ e₁ (rcl s r h) = rcl s (R-tr⁻ʳ e₁ r) (λ η η′ d → R-tr⁻ʳ e₁ (h η η′ d))
R-tr⁻ʳ e₁ (rwkˡ r) = rwkˡ (R-tr⁻ʳ e₁ r)
R-tr⁻ʳ e₁ (rwkʳ r) = rwkʳ (R-tr⁻ʳ e₁ r)
R-tr⁻ʳ e₁ (rΩ↓ ek s c f) = rΩ↓ ek s c (λ ξ ξ′ ζ ζ′ d dc z z′ l → R-tr⁻ʳ e₁ (f ξ ξ′ ζ ζ′ d dc z z′ l))
R-tr⁻ʳ (s≅ e₁) (rob {r = zero} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym e₁)) (R-tr⁻ʳ e₁ l) (R-tr⁻ʳ (s≅ e₁) r)
R-tr⁻ʳ (s≅ e₁) (rob {r = self i} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym e₁)) (R-tr⁻ʳ e₁ l) (R-tr⁻ʳ (s≅ e₁) r)
R-tr⁻ʳ (l≅ h) (rob {r = zero} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym (h n))) (R-tr⁻ʳ (h n) l) (R-tr⁻ʳ (l≅ h) r)
R-tr⁻ʳ (l≅ h) (rob {r = self i} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym (h n))) (R-tr⁻ʳ (h n) l) (R-tr⁻ʳ (l≅ h) r)
R-tr⁻ʳ {m} {a} {b′ = b′} e₁ (rΩ {r = r} {r′ = q} {h} {h′} ek s c f) =
  rΩ {r = r} {r′ = I.ltQ (I.res⁻Q q e₁)} (≅ᴵ-trans ek (I.eqQ (I.res⁻Q q e₁))) s c
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rq m a b′ (h ξ ζ (N.intoU (<→◃ r) z)) (I.tr⁻Q e₁ (h′ ξ′ ζ′ (I.intoU (<→◃ q) (I.backQ (I.res⁻Q q e₁) w))))) (sym (IR.out-intoU (<→◃ (I.ltQ (I.res⁻Q q e₁))) z′))
                              (R-tr⁻ʳ e₁ (f ξ ξ′ ζ ζ′ d dc z _ (intoRq (<→◃ r) (R-res⁻ʳ q e₁ (outRq (<→◃ r) l))))))

R-resʳ zero      (s≅ e₁) l = R-tr⁻ʳ e₁ l
R-resʳ (suc q)   (s≅ e₁) l = R-resʳ q e₁ l
R-resʳ (lim n q) (l≅ h) l = R-resʳ q (h n) l

R-res⁻ʳ zero      (s≅ e₁) l = R-trʳ e₁ l
R-res⁻ʳ (suc q)   (s≅ e₁) l = R-res⁻ʳ q e₁ l
R-res⁻ʳ (lim n q) (l≅ h) l = R-res⁻ʳ q (h n) l

R-repᵠ : ∀ {m a b φ χ ψ ρ} {X : N.Q m a φ χ} {X′ : I.Q (e m) b ψ ρ} → φ ∼ᶠ ψ → Sm m χ ρ → Rq m a b X X′ → ∀ n → Rq m a b (N.repᵠ X n) (I.repᵠ X′ n)
R-repᵠ s c r zero = rz
R-repᵠ s c r (suc zero) = r
R-repᵠ s c r (suc (suc n)) = rwk (R-⊞ s c (R-repᵠ s c r (suc n)) r)

R-ψᵠ : ∀ {m a b t t′ φ χ ψ ρ} (q : t <ᴵ a) (q′ : t′ <ᴵ b) → t ≅ᴵ t′ → {x : N.Q m a φ χ} {x′ : I.Q (e m) b ψ ρ} → Rq m a b x x′ → Rq m t t′ (N.ψᵠ q x) (I.ψᵠ q′ x′)
chRG : ∀ {m a b k k′ φ χ ψ ρ ξ ξ′} {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {r : k <ᴵ a} {r′ : k′ <ᴵ b} {h : ∀ ξ ζ → N.Us m k (<→◃ r) ξ ζ → N.Q m a (ξ ⊔ φ) (N.lo m ζ N.∪ χ)} {h′ : ∀ ξ ζ → I.Us (e m) k′ (<→◃ r′) ξ ζ → I.Q (e m) b (ξ ⊔ ψ) (I.lo (e m) ζ I.∪ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sm m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sm m ζ ζ′ → (z : N.Q m k ξ ζ) (z′ : I.Q (e m) k′ ξ′ ζ′) → LRq m a (<→◃ r) z z′ → Rq m a b (h ξ ζ (N.intoU (<→◃ r) z)) (h′ ξ′ ζ′ (I.intoU (<→◃ r′) z′))) →
       ∀ n → Rq m k k′ (N.chainᵠ fe N.fc* (λ z → N.qwk a₁ (N.⇑ (N.cv* m)) (N.ψᵠ r (h ξ (N.Z* χ) (N.intoU (<→◃ r) z)))) n) (I.chainᵠ fe′ I.fc* (λ z → I.qwk a₂ (I.⇑ (I.cv* (e m))) (I.ψᵠ r′ (h′ ξ′ (I.Z* ρ) (I.intoU (<→◃ r′) z)))) n)

R-ψᵠ {m} q q′ et rz = rwk (RΩ̇ m et)
R-ψᵠ q q′ et (rs sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ sb) (R-ψᵠ q q′ et r))
R-ψᵠ q q′ et (rl h) = rl (λ n → R-ψᵠ q q′ et (h n))
R-ψᵠ q q′ et (ri e₁ h) = ri e₁ (λ x y d → R-ψᵠ q q′ et (h x y d))
R-ψᵠ q q′ et (rŝ e₁ r h) = rŝ e₁ (R-ψᵠ q q′ et r) (λ η ee η′ e′ d → R-ψᵠ q q′ et (h η ee η′ e′ d))
R-ψᵠ q q′ et (rĉ e₁ dz dg r h) = rĉ e₁ dz dg (R-ψᵠ q q′ et r) (λ η ee η′ e′ d → R-ψᵠ q q′ et (h η ee η′ e′ d))
R-ψᵠ q q′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψᵠ q q′ et r)) (λ η η′ d → rwk (R-ψᵠ q q′ et (h η η′ d))))
R-ψᵠ q q′ et (rcl s r h) = rcl (⊔∼ (∼ᶠ-refl Fl) s) (R-ψᵠ q q′ et r) (λ η η′ d → rwk (R-ψᵠ q q′ et (h η η′ d)))
R-ψᵠ q q′ et (rwkˡ r) = rwkˡ (R-ψᵠ q q′ et r)
R-ψᵠ q q′ et (rwkʳ r) = rwkʳ (R-ψᵠ q q′ et r)
R-ψᵠ q q′ et (rob _ l r) = R-ψᵠ q q′ et r
R-ψᵠ q q′ et (rΩ↓ ek s c f) = rΩ↓ ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-ψᵠ q q′ et (f ξ ξ′ ζ ζ′ d dc z z′ l)))
R-ψᵠ {m} {t = t} {t′} q q′ et (rΩ {φ = φ} {χ} {ψ} {ρ} {k} {k′} {r = r} {r′} {h} {h′} ek s c f) with <ᴵ-dec r q | <ᴵ-dec r′ q′
... | injᵃ (via e₁ p) | injᵃ (via e′ p′) =
  rΩ {r = p} {r′ = p′} (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans ek e′)) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c)
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ w w′ → Rq m t t′ (N.ψᵠ q (h ξ ζ (N.intoU (<→◃ r) (N.tr⁻Q e₁ w)))) (I.ψᵠ q′ (h′ ξ′ ζ′ (I.intoU (<→◃ r′) (I.tr⁻Q e′ w′))))) (sym (NR.out-intoU (<→◃ p) z)) (sym (IR.out-intoU (<→◃ p′) z′))
                                    (R-ψᵠ q q′ et (f ξ ξ′ ζ ζ′ d dc _ _ (intoRq (<→◃ r) (R-tr⁻ˡ e₁ (R-tr⁻ʳ e′ (outRq (<→◃ p) l))))))))
... | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
... | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
... | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
... | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
... | injᵇ _ | injᵇ _ = rl (λ n → rwk (R-ψᵠ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f n)))))
... | injᵇ _ | injᶜ _ = rl (λ n → rwk (R-ψᵠ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f n)))))
... | injᶜ _ | injᵇ _ = rl (λ n → rwk (R-ψᵠ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f n)))))
... | injᶜ _ | injᶜ _ = rl (λ n → rwk (R-ψᵠ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f n)))))

chRG {m} ek sξ c f zero = rwk (RΩ̇ m ek)
chRG {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} {fe = fe} {fe′} {a₁} {a₂} {r = r} {r′ = r′} {h = h} {h′ = h′} ek sξ c f (suc n) =
  rwk (R-ψᵠ r r′ ek (f ξ ξ′ (N.Z* χ) (I.Z* ρ) sξ (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂} {r = r} {r′ = r′} {h = h} {h′ = h′} ek sξ c f n))))

R-Ψ : ∀ {H m a b t t′ φ χ ψ ρ w w′} (qH : H N.<ᴸ m) (ok : N.Ok w) (e₁ : N.Eh H m w χ) (p : t <ᴵ w H) (ok′ : I.Ok w′) (e′ : I.Eh (e H) (e m) w′ ρ) (p′ : t′ <ᴵ w′ (e H)) → t ≅ᴵ t′ → {x : N.Q m a φ χ} {x′ : I.Q (e m) b ψ ρ} → Rq m a b x x′ → Rq H t t′ (N.Ψ qH ok e₁ p x) (I.Ψ (ε qH) ok′ e′ p′ x′)
chRΨ : ∀ {m a b n k k′ φ χ ψ ρ ξ ξ′ w w′} (q : n N.<ᴸ m) (ok : N.Ok w) (e* : N.Eh n m w (N.lo n (N.Z* χ) N.∪ χ)) (p₁ : k <ᴵ w n) (ok′ : I.Ok w′) (e′* : I.Eh (e n) (e m) w′ (I.lo (e n) (I.Z* ρ) I.∪ ρ)) (p₂ : k′ <ᴵ w′ (e n))
       {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {a₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {a₂ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))}
       {h : ∀ ξ ζ → N.Vs m q k ξ ζ → N.Q m a (ξ ⊔ φ) (N.lo n ζ N.∪ χ)} {h′ : ∀ ξ ζ → I.Vs (e m) (ε q) k′ ξ ζ → I.Q (e m) b (ξ ⊔ ψ) (I.lo (e n) ζ I.∪ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → Sm m χ ρ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → Sm n ζ ζ′ → (z : N.Q n k ξ ζ) (z′ : I.Q (e n) k′ ξ′ ζ′) → LVq m q z z′ → Rq m a b (h ξ ζ (N.intoV q z)) (h′ ξ′ ζ′ (I.intoV (ε q) z′))) →
       ∀ i → Rq n k k′ (N.chainᵠ fe N.fc* (λ z → N.qwk a₁ (N.⇑ (N.cv* n)) (N.Ψ q ok e* p₁ (h ξ (N.Z* χ) (N.intoV q z)))) i) (I.chainᵠ fe′ I.fc* (λ z → I.qwk a₂ (I.⇑ (I.cv* (e n))) (I.Ψ (ε q) ok′ e′* p₂ (h′ ξ′ (I.Z* ρ) (I.intoV (ε q) z)))) i)

R-Ψ {H} qH ok e₁ p ok′ e′ p′ et rz = rwk (RΩ̇ H et)
R-Ψ qH ok e₁ p ok′ e′ p′ et (rs sa sb r) = rl (R-repᵠ (⊔∼ (∼ᶠ-refl Fl) sa) (Z∼ (sm↓ qH sb)) (R-Ψ qH ok e₁ p ok′ e′ p′ et r))
R-Ψ qH ok e₁ p ok′ e′ p′ et (rl h) = rl (λ n → R-Ψ qH ok e₁ p ok′ e′ p′ et (h n))
R-Ψ qH ok e₁ p ok′ e′ p′ et (ri d h) = ri d (λ x y dd → R-Ψ qH ok e₁ p ok′ e′ p′ et (h x y dd))
R-Ψ qH ok e₁ p ok′ e′ p′ et (rŝ d r h) = rŝ d (R-Ψ qH ok e₁ p ok′ e′ p′ et r) (λ η ee η′ e₂ dd → R-Ψ qH ok e₁ p ok′ e′ p′ et (h η ee η′ e₂ dd))
R-Ψ qH ok e₁ p ok′ e′ p′ et (rĉ d dz dg r h) = rĉ d dz dg (R-Ψ qH ok e₁ p ok′ e′ p′ et r) (λ η ee η′ e₂ dd → R-Ψ qH ok e₁ p ok′ e′ p′ et (h η ee η′ e₂ dd))
R-Ψ qH ok e₁ p ok′ e′ p′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-Ψ qH ok e₁ p ok′ e′ p′ et r)) (λ η η′ d → rwk (R-Ψ qH ok e₁ p ok′ e′ p′ et (h η η′ d))))
R-Ψ qH ok e₁ p ok′ e′ p′ et (rwkˡ {lc = lc} r) = rwkˡ (R-Ψ qH ok (λ i h r₁ → lc i r₁ (e₁ i h r₁)) p ok′ e′ p′ et r)
R-Ψ qH ok e₁ p ok′ e′ p′ et (rwkʳ {lc′ = lc′} r) = rwkʳ (R-Ψ qH ok e₁ p ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)) p′ et r)
R-Ψ qH ok e₁ p ok′ e′ p′ et (rob _ l r) = R-Ψ qH ok e₁ p ok′ e′ p′ et r
R-Ψ {H} qH ok e₁ p ok′ e′ p′ et (rcl {n = n} s r h) with N.tri n H | I.tri (e n) (e H) | al n H
... | _ | _ | all l = rcl {q = l} (⊔∼ (∼ᶠ-refl Fl) s) (R-Ψ qH ok e₁ p ok′ e′ p′ et r) (λ η η′ d → rwk (R-Ψ qH ok _ p ok′ _ p′ et (h η η′ d)))
... | _ | _ | ale = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ p _ p′ et) (R-Ψ qH ok e₁ p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (R-Ψ qH _ _ _ _ _ _ et (h η η′ eη)))
... | _ | _ | alg l = rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) _ (N.zr ok n) _ (I.zr ok′ (e n)) z≅) (R-Ψ qH ok e₁ p ok′ e′ p′ et r) (λ η d η′ d′ eη → rwk (R-Ψ qH _ _ _ _ _ _ et (h η η′ eη)))
R-Ψ {H} {t = t} {t′} qH ok e₁ p ok′ e′ p′ et (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) with N.tri n H | I.tri (e n) (e H) | al n H
... | _ | _ | all l = rΩ↓ {q = l} ek (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (sm↓ qH c))
      (λ ξ ξ′ ζ ζ′ d dc z z′ lz → rwk (subst₂ (λ u v → Rq H t t′ (N.Ψ qH ok (N.e-lo ζ (inj₂ l) e₁) p (h ξ ζ (N.intoV q u))) (I.Ψ (ε qH) ok′ (I.e-lo ζ′ (inj₂ (ε l)) e′) p′ (h′ ξ′ ζ′ (I.intoV (ε q) v)))) (sym (N.out-intoV l z)) (sym (I.out-intoV (ε l) z′))
         (R-Ψ qH ok (N.e-lo ζ (inj₂ l) e₁) p ok′ (I.e-lo ζ′ (inj₂ (ε l)) e′) p′ et (f ξ ξ′ ζ ζ′ d dc z z′ (intoVq q (outVq l lz))))))
... | _ | _ | ale with <ᴵ-dec (ac (e₁ n (inj₁ refl) q)) p | <ᴵ-dec (ac′ (e′ (e n) (inj₁ refl) (ε q))) p′
...   | injᵃ (via d₁ s₁) | injᵃ (via d₂ s₂) =
  rΩ {r = s₁} {r′ = s₂} (≅ᴵ-trans (≅ᴵ-sym d₁) (≅ᴵ-trans ek d₂)) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (sm↓ qH c))
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ u v → Rq H t t′ (N.Ψ qH ok (N.e-lo ζ (inj₁ refl) e₁) p (h ξ ζ (N.intoV q (N.tr⁻Q d₁ u)))) (I.Ψ (ε qH) ok′ (I.e-lo ζ′ (inj₁ refl) e′) p′ (h′ ξ′ ζ′ (I.intoV (ε q) (I.tr⁻Q d₂ v))))) (sym (NR.out-intoU (<→◃ s₁) z)) (sym (IR.out-intoU (<→◃ s₂) z′))
        (R-Ψ qH ok (N.e-lo ζ (inj₁ refl) e₁) p ok′ (I.e-lo ζ′ (inj₁ refl) e′) p′ et (f ξ ξ′ ζ ζ′ d dc _ _ (intoVq q (R-tr⁻ˡ d₁ (R-tr⁻ʳ d₂ (outRq (<→◃ s₁) l))))))))
...   | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
...   | injᵃ a | injᶜ c₁ = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c₁) (≅ᴵ-sym ek)))))
...   | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
...   | injᶜ c₁ | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c₁) ek))))
...   | injᵇ _ | injᵇ _ = rl (λ i → rwk (R-Ψ qH ok (N.e⁺ H ok e₁) p ok′ (I.e⁺ (e H) ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (sm↓ q c)) _ _ (intoVq q (chRΨ q ok (N.e⁺ n ok e₁) (ac (e₁ n (inj₁ refl) q)) ok′ (I.e⁺ (e n) ok′ e′) (ac′ (e′ (e n) (inj₁ refl) (ε q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
...   | injᵇ _ | injᶜ _ = rl (λ i → rwk (R-Ψ qH ok (N.e⁺ H ok e₁) p ok′ (I.e⁺ (e H) ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (sm↓ q c)) _ _ (intoVq q (chRΨ q ok (N.e⁺ n ok e₁) (ac (e₁ n (inj₁ refl) q)) ok′ (I.e⁺ (e n) ok′ e′) (ac′ (e′ (e n) (inj₁ refl) (ε q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
...   | injᶜ _ | injᵇ _ = rl (λ i → rwk (R-Ψ qH ok (N.e⁺ H ok e₁) p ok′ (I.e⁺ (e H) ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (sm↓ q c)) _ _ (intoVq q (chRΨ q ok (N.e⁺ n ok e₁) (ac (e₁ n (inj₁ refl) q)) ok′ (I.e⁺ (e n) ok′ e′) (ac′ (e′ (e n) (inj₁ refl) (ε q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
...   | injᶜ _ | injᶜ _ = rl (λ i → rwk (R-Ψ qH ok (N.e⁺ H ok e₁) p ok′ (I.e⁺ (e H) ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (sm↓ q c)) _ _ (intoVq q (chRΨ q ok (N.e⁺ n ok e₁) (ac (e₁ n (inj₁ refl) q)) ok′ (I.e⁺ (e n) ok′ e′) (ac′ (e′ (e n) (inj₁ refl) (ε q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
R-Ψ {H} {t = t} {t′} qH ok e₁ p ok′ e′ p′ et (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {k = k} {k′} {q} {ac = ac} {ac′ = ac′} {h} {h′} ek s c f) | _ | _ | alg l =
  rl (λ i → rwk (R-Ψ qH ok (N.e⁺ n ok e₁) p ok′ (I.e⁺ (e n) ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ (sm↓ q c)) _ _ (intoVq q (chRΨ q ok (N.e⁺ n ok (N.e↑ l e₁)) (ac ((N.e↑ l e₁) n (inj₁ refl) q)) ok′ (I.e⁺ (e n) ok′ (I.e↑ (ε l) e′)) (ac′ ((I.e↑ (ε l) e′) (e n) (inj₁ refl) (ε q))) {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))
R-Ψ {H} {m} qH ok e₁ p ok′ e′ p′ et (rΩ {φ = φ} {χ} {ψ} {ρ} {r = r} {r′} {h} {h′} ek s c f) =
  rl (λ i → rwk (R-Ψ qH ok (N.e⁺ m ok e₁) p ok′ (I.e⁺ (e m) ok′ e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (N.Z* χ) (I.Z* ρ) (⊔∼ (∼ᶠ-refl Fl) s) (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {a₁ = dupr2} {a₂ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) c f i)))))

chRΨ {n = n} q ok e* p₁ ok′ e′* p₂ ek sξ c f zero = rwk (RΩ̇ n ek)
chRΨ {χ = χ} {ρ = ρ} {ξ = ξ} {ξ′} q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′} {a₁} {a₂} {h} {h′} ek sξ c f (suc i) =
  rwk (R-Ψ q ok e* p₁ ok′ e′* p₂ ek (f ξ ξ′ (N.Z* χ) (I.Z* ρ) sξ (Z∼ (sm↓ q c)) _ _ (intoVq q (chRΨ q ok e* p₁ ok′ e′* p₂ {fe = fe} {fe′ = fe′} {a₁ = a₁} {a₂ = a₂} {h = h} {h′ = h′} ek sξ c f i))))

R→≈ᵠ : ∀ {m a b φ χ ψ ρ w w′} {x : N.Q m a φ χ} {x′ : I.Q (e m) b ψ ρ} → Rq m a b x x′ → (ok : N.Ok w) (e₁ : N.Eh N.h₀ m w χ) (ok′ : I.Ok w′) (e′ : I.Eh I.h₀ (e m) w′ ρ) → N.ψ̄ᵠ ok e₁ x ≈ᴿ I.ψ̄ᵠ ok′ e′ x′
R→≈ᵠ rz ok e₁ ok′ e′ = wkR _ _ r∅
R→≈ᵠ (rs s c r) ok e₁ ok′ e′ = sucR (R→≈ᵠ r ok e₁ ok′ e′)
R→≈ᵠ (rl h) ok e₁ ok′ e′ = limR (λ n → R→≈ᵠ (h n) ok e₁ ok′ e′)
R→≈ᵠ (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) ok e₁ ok′ e′ = limᵢR {ac = ac} {ac′ = ac′} {H = λ x → N.ψ̄ᵠ ok e₁ (f x)} {H′ = λ x → I.ψ̄ᵠ ok′ e′ (f′ x)} d (λ x y dd → R→≈ᵠ (h x y dd) ok e₁ ok′ e′)
R→≈ᵠ (rŝ d r h) ok e₁ ok′ e′ = ŝR d (R→≈ᵠ r ok e₁ ok′ e′) (λ η ee η′ e₂ dd → R→≈ᵠ (h η ee η′ e₂ dd) ok e₁ ok′ e′)
R→≈ᵠ (rĉ d dz dg r h) ok e₁ ok′ e′ = ĉR d dz dg (R→≈ᵠ r ok e₁ ok′ e′) (λ η ee η′ e₂ dd → R→≈ᵠ (h η ee η′ e₂ dd) ok e₁ ok′ e′)
R→≈ᵠ (rclo {t = t} {t′} {g} {g′} s r h) ok e₁ ok′ e′ = cloR {t = N.ψ̄ᵠ ok e₁ t} {g = λ η → N.ψ̄ᵠ ok e₁ (g η)} {t′ = I.ψ̄ᵠ ok′ e′ t′} {g′ = λ η → I.ψ̄ᵠ ok′ e′ (g′ η)} s (R→≈ᵠ r ok e₁ ok′ e′) (λ η η′ d → R→≈ᵠ (h η η′ d) ok e₁ ok′ e′)
R→≈ᵠ {χ = χ} {ρ = ρ} {w = w} {w′ = w′} (rcl {n = n} {κ₁ = κ₁} {κ₂ = κ₂} {q = q} {s = s₁} {s′ = s₂} s r h) ok e₁ ok′ e′ =
  ŝR (bound-≅ (⊔∼ s (fk∼ z≅)) _ (N.zr ok n) _ (I.zr ok′ (e n)) z≅) (R→≈ᵠ r ok e₁ ok′ e′)
      (λ η d η′ d′ eη → R→≈ᵠ (h η η′ eη)
         (N.upd-ok n w ok (tt , λ x → lim 0 (proj₂ (evF B₁) x))) (λ i k r₁ → N.upd-ev n i w χ (N.evη κ₁ B₁ η d) (e₁ i k r₁))
         (I.upd-ok (e n) w′ ok′ (tt , λ x → lim 0 (proj₂ (evF B₂) x))) (λ i k r₁ → I.upd-ev (e n) i w′ ρ (I.evη κ₂ B₂ η′ d′) (e′ i k r₁)))
  where
  B₁ = bound (κ₁ ⊔ fk zero) (s₁ (e₁ n (N.Hi-0 n) q)) (N.zr ok n)
  B₂ = bound (κ₂ ⊔ fk zero) (s₂ (e′ (e n) (I.Hi-0 (e n)) (ε q))) (I.zr ok′ (e n))
R→≈ᵠ (rwkˡ {le = le} {lc = lc} r) ok e₁ ok′ e′ = wkR le (λ v → v) (R→≈ᵠ r ok (λ i h r₁ → lc i r₁ (e₁ i h r₁)) ok′ e′)
R→≈ᵠ (rwkʳ {le′ = le′} {lc′ = lc′} r) ok e₁ ok′ e′ = wkR (λ v → v) le′ (R→≈ᵠ r ok e₁ ok′ (λ i h r₁ → lc′ i r₁ (e′ i h r₁)))
R→≈ᵠ (rob _ l r) ok e₁ ok′ e′ = R→≈ᵠ r ok e₁ ok′ e′
R→≈ᵠ (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {n} {q = q} {fe = fe} {fe′} {ac} {ac′} {h} {h′} ek s c f) ok e₁ ok′ e′ =
  limR (λ i → wkR _ _ (R→≈ᵠ (f φ ψ (N.Z* χ) (I.Z* ρ) s (Z∼ (sm↓ q c)) _ _ (intoVq q (chRΨ q ok (N.e⁺ n ok (N.e↓ e₁)) (ac (N.e↓ e₁ n (inj₁ refl) q)) ok′ (I.e⁺ (e n) ok′ (I.e↓ e′)) (ac′ (I.e↓ e′ (e n) (inj₁ refl) (ε q))) {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {h = h} {h′ = h′} ek s c f i))) ok (N.e⁺ n ok e₁) ok′ (I.e⁺ (e n) ok′ e′)))
R→≈ᵠ {m} (rΩ {φ = φ} {χ} {ψ} {ρ} {fe = fe} {fe′} {r} {r′} {h} {h′} ek s c f) ok e₁ ok′ e′ =
  limR (λ i → wkR _ _ (R→≈ᵠ (f φ ψ (N.Z* χ) (I.Z* ρ) s (Z∼ c) _ _ (intoRq (<→◃ r) (chRG {fe = fe} {fe′ = fe′} {a₁ = λ v → fe v , (v , v)} {a₂ = λ v → fe′ v , (v , v)} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s c f i))) ok (N.e⁺ m ok e₁) ok′ (I.e⁺ (e m) ok′ e′)))

-- 主定理: 实例上的树与原来的树同值
bridge : ∀ m α α′ → α ≅ᴵ α′ → N.Tᵠ m α ≈ᴿ I.Tᵠ (e m) α′
bridge m α α′ d = R→≈ᵠ (RΩ̇ m d) N.ok₀ (λ i h r → N.ok₀ i) I.ok₀ (λ i h r → I.ok₀ i)
```
