# 阶梯 (五): `P` 上的互模拟

> 结论写在 [ScafLadder](ScafLadder.lagda.md). 由 [Uniform5Rel](Uniform5Rel.lagda.md), [Uniform5RelPsi](Uniform5RelPsi.lagda.md) 改写. 跨层, 两边的世界独立. `R-Ψ`: 比较结果在 $\cong$ 下一致, 非对角由 `clash` 排除; 高度 1 的闭包落成 `rŝ`, 界 $\cong$ 由 `bound-≅`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderRel where

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
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ)
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
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.ScafLadderZUniform4Two renaming (ι to ιᵒ)
open import OCF.Align.ScafLadderZUniform5Class
open import OCF.Align.ScafLadderZUniform5Close
open import OCF.Align.ScafLadderZUniform5Tail
open import OCF.Align.ScafLadderZUniform5Tr
open import OCF.Align.ScafLadderZUniform5Psi
open import OCF.Align.ScafLadderZUniform5Rel hiding (R-ι; R-trˡ; R-tr⁻ˡ; R-resˡ; R-res⁻ˡ)
open import OCF.Align.ScafLadderZUniform5RelPsi hiding (R-trʳ; R-tr⁻ʳ; R-resʳ; R-res⁻ʳ)
open import OCF.Align.ScafLadderZUniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.ScafLadderTree
open import OCF.Align.ScafLadderClass
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Bachmann using (clash)
open RestrP
import OCF.Align.ScafLadderZUniform5Rel as OR
import OCF.Align.ScafLadderZUniform5RelPsi as OR′
```

## §1 关系

```agda
module _ (a b : Ordᴵ) (LR : ∀ {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → P k ξ ζ → P k′ ξ′ ζ′ → Set) where
  data Q₊ : ∀ {φ χ ψ ρ} → P a φ χ → P b ψ ρ → Set where
    rz : ∀ {φ χ ψ ρ} → Q₊ {φ} {χ} {ψ} {ρ} p0 p0
    rs : ∀ {φ χ ψ ρ} {p : P a φ χ} {p′ : P b ψ ρ} → φ ∼ᶠ ψ → χ ∼ᶠ ρ → Q₊ p p′ → Q₊ (psu p) (psu p′)
    rl : ∀ {φ χ ψ ρ} {F : ℕ → P a φ χ} {F′ : ℕ → P b ψ ρ} → (∀ n → Q₊ (F n) (F′ n)) → Q₊ (pl F) (pl F′)
    ri : ∀ {φ χ ψ ρ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L} {f : Ordˢ j → P a φ χ} {f′ : Ordˢ j′ → P b ψ ρ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → Q₊ (f x) (f′ y)) → Q₊ (pi ac f) (pi ac′ f′)
    rŝ : ∀ {φ χ ψ ρ c₁ c₂} {t : P a φ χ} {t′ : P b ψ ρ} {g : (η : Ordᴵ) → c₁ ⊑ᴵ η → P a φ χ} {g′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → P b ψ ρ} →
         c₁ ≅ᴵ c₂ → Q₊ t t′ → (∀ η e η′ e′ → η ≅ᴵ η′ → Q₊ (g η e) (g′ η′ e′)) → Q₊ (pŝ c₁ t g) (pŝ c₂ t′ g′)
    rĉ : ∀ {φ χ ψ ρ c₁ c₂ z z′} {zg : (η : Ordᴵ) → c₁ ⊑ᴵ η → Z} {zg′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → Z}
         {o₀ : P a φ χ} {o₀′ : P b ψ ρ} {o : (η : Ordᴵ) → c₁ ⊑ᴵ η → P a φ χ} {o′ : (η : Ordᴵ) → c₂ ⊑ᴵ η → P b ψ ρ} →
         c₁ ≅ᴵ c₂ → z ≅ᶻ z′ → (∀ η e η′ e′ → η ≅ᴵ η′ → zg η e ≅ᶻ zg′ η′ e′) → Q₊ o₀ o₀′ →
         (∀ η e η′ e′ → η ≅ᴵ η′ → Q₊ (o η e) (o′ η′ e′)) → Q₊ (pĉ c₁ z zg o₀ o) (pĉ c₂ z′ zg′ o₀′ o′)
    rclo : ∀ {φ χ ψ ρ} {t : P a (φ ⊔ fk zero) χ} {t′ : P b (ψ ⊔ fk zero) ρ} {g : (η : Ordᴵ) → P a (φ ⊔ fk η) χ} {g′ : (η : Ordᴵ) → P b (ψ ⊔ fk η) ρ} →
         φ ∼ᶠ ψ → Q₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → Q₊ (g η) (g′ η′)) → Q₊ (pclo t g) (pclo t′ g′)
    rcl : ∀ {φ χ ψ ρ} {t : P a φ (χ ⊔ fk zero)} {t′ : P b ψ (ρ ⊔ fk zero)} {g : (η : Ordᴵ) → P a φ (χ ⊔ fk η)} {g′ : (η : Ordᴵ) → P b ψ (ρ ⊔ fk η)} →
         χ ∼ᶠ ρ → Q₊ t t′ → (∀ η η′ → η ≅ᴵ η′ → Q₊ (g η) (g′ η′)) → Q₊ (pcl t g) (pcl t′ g′)
    rwk : ∀ {φ φ′ χ χ′ ψ ψ′ ρ ρ′} {le : ∀ {L} → Ev L φ′ → Ev L φ} {lc : ∀ {L} → Ev L χ′ → Ev L χ} {le′ : ∀ {L} → Ev L ψ′ → Ev L ψ} {lc′ : ∀ {L} → Ev L ρ′ → Ev L ρ}
          {x : P a φ χ} {x′ : P b ψ ρ} → Q₊ x x′ → Q₊ (pwk le lc x) (pwk le′ lc′ x′)
    rΩ↓ : ∀ {φ χ ψ ρ k k′} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {ac : ∀ {L} → Ev L χ → k <ᴵ L} {ac′ : ∀ {L} → Ev L ρ → k′ <ᴵ L}
          {h : ∀ ξ → O k ξ → P a (ξ ⊔ φ) χ} {h′ : ∀ ξ → O k′ ξ → P b (ξ ⊔ ψ) ρ} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
          (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → Rᵒ k k′ z z′ → Q₊ (h ξ z) (h′ ξ′ z′)) → Q₊ (pΩ↓ fe ac h) (pΩ↓ fe′ ac′ h′)
    rΩ : ∀ {φ χ ψ ρ k k′} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {fc : ∀ {L} → Ev L χ → Ev L Fl} {fc′ : ∀ {L} → Ev L ρ → Ev L Fl} {r : k <ᴵ a} {r′ : k′ <ᴵ b}
         {h : ∀ ξ ζ → Vs k (<→◃ r) ξ ζ → P a (ξ ⊔ φ) (ζ ⊔ χ)} {h′ : ∀ ξ ζ → Vs k′ (<→◃ r′) ξ ζ → P b (ξ ⊔ ψ) (ζ ⊔ ρ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ → χ ∼ᶠ ρ →
         (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → ζ ∼ᶠ ζ′ → (z : P k ξ ζ) (z′ : P k′ ξ′ ζ′) → LR (<→◃ r) z z′ → Q₊ (h ξ ζ (intoV (<→◃ r) z)) (h′ ξ′ ζ′ (intoV (<→◃ r′) z′))) → Q₊ (pΩ fe fc r h) (pΩ fe′ fc′ r′ h′)

Rᴾ : ∀ a b {φ χ ψ ρ} → P a φ χ → P b ψ ρ → Set
LRᴾ : ∀ a {k} → k ◃ a → ∀ {k′ ξ ζ ξ′ ζ′} → P k ξ ζ → P k′ ξ′ ζ′ → Set
Rᴾ a b x y = Q₊ a b (LRᴾ a) x y
LRᴾ (suc k)   zero      {k′} x y = Rᴾ k k′ x y
LRᴾ (suc c)   (suc r)   x y = LRᴾ c r x y
LRᴾ (lim f s) (self n)  {k′} x y = Rᴾ (f n) k′ x y
LRᴾ (lim f s) (lim n r) x y = LRᴾ (f n) r x y

outRᴾ : ∀ {c k} (r : k ◃ c) {k′ ξ ζ ξ′ ζ′} {z : P k ξ ζ} {z′ : P k′ ξ′ ζ′} → LRᴾ c r z z′ → Rᴾ k k′ z z′
outRᴾ zero      l = l
outRᴾ (suc r)   l = outRᴾ r l
outRᴾ (self n)  l = l
outRᴾ (lim n r) l = outRᴾ r l

intoRᴾ : ∀ {c k} (r : k ◃ c) {k′ ξ ζ ξ′ ζ′} {z : P k ξ ζ} {z′ : P k′ ξ′ ζ′} → Rᴾ k k′ z z′ → LRᴾ c r z z′
intoRᴾ zero      l = l
intoRᴾ (suc r)   l = intoRᴾ r l
intoRᴾ (self n)  l = l
intoRᴾ (lim n r) l = intoRᴾ r l
```

## §2 封闭性

```agda
R-⊞ : ∀ {a b φ χ φ′ χ′ ψ ρ ψ′ ρ′} {W : P a φ χ} {W′ : P b φ′ χ′} {t : P a ψ ρ} {t′ : P b ψ′ ρ′} → φ ∼ᶠ φ′ → χ ∼ᶠ χ′ → Rᴾ a b W W′ → Rᴾ a b t t′ → Rᴾ a b (W ⊞ t) (W′ ⊞ t′)
R-⊞ s c rW rz = rwk rW
R-⊞ s c rW (rs sa sb r) = rs (⊔∼ s sa) (⊔∼ c sb) (R-⊞ s c rW r)
R-⊞ s c rW (rl h) = rl (λ n → R-⊞ s c rW (h n))
R-⊞ s c rW (ri e h) = ri e (λ x y d → R-⊞ s c rW (h x y d))
R-⊞ s c rW (rŝ e r h) = rŝ e (R-⊞ s c rW r) (λ η ee η′ e′ d → R-⊞ s c rW (h η ee η′ e′ d))
R-⊞ s c rW (rĉ e dz dg r h) = rĉ e dz dg (R-⊞ s c rW r) (λ η ee η′ e′ d → R-⊞ s c rW (h η ee η′ e′ d))
R-⊞ s c rW (rclo sψ r h) = rwk (rclo (⊔∼ s sψ) (rwk (R-⊞ s c rW r)) (λ η η′ d → rwk (R-⊞ s c rW (h η η′ d))))
R-⊞ s c rW (rcl sψ r h) = rwk (rcl (⊔∼ c sψ) (rwk (R-⊞ s c rW r)) (λ η η′ d → rwk (R-⊞ s c rW (h η η′ d))))
R-⊞ s c rW (rwk r) = rwk (R-⊞ s c rW r)
R-⊞ s c rW (rΩ↓ ek sψ f) = rΩ↓ ek (⊔∼ s sψ) (λ ξ ξ′ d z z′ l → rwk (R-⊞ s c rW (f ξ ξ′ d z z′ l)))
R-⊞ s c rW (rΩ ek sψ sρ f) = rΩ ek (⊔∼ s sψ) (⊔∼ c sρ) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-⊞ s c rW (f ξ ξ′ ζ ζ′ d dc z z′ l)))

R-ι : ∀ {a b c d φ χ ψ ρ} (q : a ◃ c) (q′ : b ◃ d) {x : P a φ χ} {x′ : P b ψ ρ} → Rᴾ a b x x′ → Rᴾ c d (ι q x) (ι q′ x′)
R-ι q q′ rz = rz
R-ι q q′ (rs sa sb r) = rs sa sb (R-ι q q′ r)
R-ι q q′ (rl h) = rl (λ n → R-ι q q′ (h n))
R-ι q q′ (ri e h) = ri e (λ x y d → R-ι q q′ (h x y d))
R-ι q q′ (rŝ e r h) = rŝ e (R-ι q q′ r) (λ η ee η′ e′ d → R-ι q q′ (h η ee η′ e′ d))
R-ι q q′ (rĉ e dz dg r h) = rĉ e dz dg (R-ι q q′ r) (λ η ee η′ e′ d → R-ι q q′ (h η ee η′ e′ d))
R-ι q q′ (rclo s r h) = rclo s (R-ι q q′ r) (λ η η′ d → R-ι q q′ (h η η′ d))
R-ι q q′ (rcl s r h) = rcl s (R-ι q q′ r) (λ η η′ d → R-ι q q′ (h η η′ d))
R-ι q q′ (rwk r) = rwk (R-ι q q′ r)
R-ι q q′ (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-ι q q′ (f ξ ξ′ d z z′ l))
R-ι {c = c} {d = dd} q q′ (rΩ {r = r} {r′ = r′} {h = h} {h′ = h′} ek s sρ f) =
  rΩ {r = <◃ r q} {r′ = <◃ r′ q′} ek s sρ
     (λ ξ ξ′ ζ ζ′ e dc z z′ l → subst₂ (λ w w′ → Rᴾ c dd (ι q (h ξ ζ (intoV (<→◃ r) w))) (ι q′ (h′ ξ′ ζ′ (intoV (<→◃ r′) w′)))) (sym (out-intoV (<→◃ (<◃ r q)) z)) (sym (out-intoV (<→◃ (<◃ r′ q′)) z′))
                                (R-ι q q′ (f ξ ξ′ ζ ζ′ e dc _ _ (intoRᴾ (<→◃ r) (outRᴾ (<→◃ (<◃ r q)) l)))))

R-ι↓ : ∀ {k k′ α β φ ψ} → k ≅ᴵ k′ → {x : O k φ} {x′ : O k′ ψ} → Rᵒ k k′ x x′ → Rᴾ α β (ι↓ {α = α} x) (ι↓ {α = β} x′)
R-ι↓ ek rz = rz
R-ι↓ ek (rs sa r) = rs sa (flo-∼ ek) (R-ι↓ ek r)
R-ι↓ ek (rl h) = rl (λ n → R-ι↓ ek (h n))
R-ι↓ ek (ri e h) = ri e (λ x y d → R-ι↓ ek (h x y d))
R-ι↓ ek (rŝ e r h) = rŝ e (R-ι↓ ek r) (λ η ee η′ e′ d → R-ι↓ ek (h η ee η′ e′ d))
R-ι↓ ek (rĉ e dz dg r h) = rĉ e dz dg (R-ι↓ ek r) (λ η ee η′ e′ d → R-ι↓ ek (h η ee η′ e′ d))
R-ι↓ ek (rclo s r h) = rclo s (R-ι↓ ek r) (λ η η′ d → R-ι↓ ek (h η η′ d))
R-ι↓ ek (rwk r) = rwk (R-ι↓ ek r)
R-ι↓ ek (rΩ {r = r} {r′ = r′} ei s f) = rΩ↓ ei s (λ ξ ξ′ d z z′ l → R-ι↓ ek (f ξ ξ′ d z z′ (intoR (<→◃ r) l)))
R-ι↓ (s≅ e) (rob {r = zero} {r′ = zero} ea l r) = rwk (R-ι↓ ea l)
R-ι↓ (l≅ h) (rob {r = self n} {r′ = self n′} ea l r) = rwk (R-ι↓ ea l)
```

## §3 $\dot\Omega$

```agda
RΩ̇ᴾ : ∀ {a b} → a ≅ᴵ b → Rᴾ a b (Ω̇ᴾ a) (Ω̇ᴾ b)
RΩ̇ᴾ z≅ = rcl fz∼ (rwk (R-ι↓ (s≅ z≅) (RΩ̇ (s≅ z≅)))) (λ η η′ eη → rwk (R-ι↓ eη (RΩ̇ eη)))
RΩ̇ᴾ (s≅ e) = rΩ e (⊔∼ fz∼ (fk∼ z≅)) (⊔∼ fz∼ (fk∼ z≅)) (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (R-ι zero zero l))
RΩ̇ᴾ (l≅ h) = rl (λ n → R-ι (self n) (self n) (RΩ̇ᴾ (h n)))
```

## §4 搬运不改变关系

```agda
R-trˡ  : ∀ {a a′ b φ χ ψ ρ} (e : a ≅ᴵ a′) {x : P a φ χ} {y : P b ψ ρ} → Rᴾ a b x y → Rᴾ a′ b (trP e x) y
R-tr⁻ˡ : ∀ {a a′ b φ χ ψ ρ} (e : a′ ≅ᴵ a) {x : P a φ χ} {y : P b ψ ρ} → Rᴾ a b x y → Rᴾ a′ b (tr⁻P e x) y
R-resˡ : ∀ {j a a′ b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : a ≅ᴵ a′) {z : P (repP (resP q e)) ξ ζ} {y : P b ξ′ ζ′} → Rᴾ _ b z y → Rᴾ j b (backP (resP q e) z) y
R-res⁻ˡ : ∀ {j a a′ b ξ ζ ξ′ ζ′} (q : j <ᴵ a) (e : a′ ≅ᴵ a) {z : P (repP (res⁻P q e)) ξ ζ} {y : P b ξ′ ζ′} → Rᴾ _ b z y → Rᴾ j b (backP (res⁻P q e) z) y

R-trˡ e rz = rz
R-trˡ e (rs sa sb r) = rs sa sb (R-trˡ e r)
R-trˡ e (rl h) = rl (λ m → R-trˡ e (h m))
R-trˡ e (ri ej h) = ri ej (λ x y d → R-trˡ e (h x y d))
R-trˡ e (rŝ ec r h) = rŝ ec (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
R-trˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trˡ e r) (λ η ee η′ e′ d → R-trˡ e (h η ee η′ e′ d))
R-trˡ e (rclo s r h) = rclo s (R-trˡ e r) (λ η η′ d → R-trˡ e (h η η′ d))
R-trˡ e (rcl s r h) = rcl s (R-trˡ e r) (λ η η′ d → R-trˡ e (h η η′ d))
R-trˡ e (rwk r) = rwk (R-trˡ e r)
R-trˡ e (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-trˡ e (f ξ ξ′ d z z′ l))
R-trˡ {a′ = a′} {b} e (rΩ {r = q} {r′} {h} {h′} ek s sρ f) =
  rΩ {r = ltP (resP q e)} (≅ᴵ-trans (≅ᴵ-sym (eqP (resP q e))) ek) s sρ
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rᴾ a′ b (trP e (h ξ ζ (intoV (<→◃ q) (backP (resP q e) w)))) (h′ ξ′ ζ′ (intoV (<→◃ r′) z′))) (sym (out-intoV (<→◃ (ltP (resP q e))) z))
                              (R-trˡ e (f ξ ξ′ ζ ζ′ d dc _ z′ (intoRᴾ (<→◃ q) (R-resˡ q e (outRᴾ (<→◃ (ltP (resP q e))) l))))))

R-tr⁻ˡ e rz = rz
R-tr⁻ˡ e (rs sa sb r) = rs sa sb (R-tr⁻ˡ e r)
R-tr⁻ˡ e (rl h) = rl (λ m → R-tr⁻ˡ e (h m))
R-tr⁻ˡ e (ri ej h) = ri ej (λ x y d → R-tr⁻ˡ e (h x y d))
R-tr⁻ˡ e (rŝ ec r h) = rŝ ec (R-tr⁻ˡ e r) (λ η ee η′ e′ d → R-tr⁻ˡ e (h η ee η′ e′ d))
R-tr⁻ˡ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ˡ e r) (λ η ee η′ e′ d → R-tr⁻ˡ e (h η ee η′ e′ d))
R-tr⁻ˡ e (rclo s r h) = rclo s (R-tr⁻ˡ e r) (λ η η′ d → R-tr⁻ˡ e (h η η′ d))
R-tr⁻ˡ e (rcl s r h) = rcl s (R-tr⁻ˡ e r) (λ η η′ d → R-tr⁻ˡ e (h η η′ d))
R-tr⁻ˡ e (rwk r) = rwk (R-tr⁻ˡ e r)
R-tr⁻ˡ e (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-tr⁻ˡ e (f ξ ξ′ d z z′ l))
R-tr⁻ˡ {a′ = a′} {b} e (rΩ {r = q} {r′} {h} {h′} ek s sρ f) =
  rΩ {r = ltP (res⁻P q e)} (≅ᴵ-trans (≅ᴵ-sym (eqP (res⁻P q e))) ek) s sρ
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rᴾ a′ b (tr⁻P e (h ξ ζ (intoV (<→◃ q) (backP (res⁻P q e) w)))) (h′ ξ′ ζ′ (intoV (<→◃ r′) z′))) (sym (out-intoV (<→◃ (ltP (res⁻P q e))) z))
                              (R-tr⁻ˡ e (f ξ ξ′ ζ ζ′ d dc _ z′ (intoRᴾ (<→◃ q) (R-res⁻ˡ q e (outRᴾ (<→◃ (ltP (res⁻P q e))) l))))))

R-resˡ zero      (s≅ e) l = R-tr⁻ˡ e l
R-resˡ (suc q)   (s≅ e) l = R-resˡ q e l
R-resˡ (lim n q) (l≅ h) l = R-resˡ q (h n) l

R-res⁻ˡ zero      (s≅ e) l = R-trˡ e l
R-res⁻ˡ (suc q)   (s≅ e) l = R-res⁻ˡ q e l
R-res⁻ˡ (lim n q) (l≅ h) l = R-res⁻ˡ q (h n) l

R-trʳ  : ∀ {a b b′ φ χ ψ ρ} (e : b ≅ᴵ b′) {x : P a φ χ} {y : P b ψ ρ} → Rᴾ a b x y → Rᴾ a b′ x (trP e y)
R-tr⁻ʳ : ∀ {a b b′ φ χ ψ ρ} (e : b′ ≅ᴵ b) {x : P a φ χ} {y : P b ψ ρ} → Rᴾ a b x y → Rᴾ a b′ x (tr⁻P e y)
R-resʳ : ∀ {j a b b′ ξ ζ ξ′ ζ′} (q : j <ᴵ b) (e : b ≅ᴵ b′) {z : P a ξ ζ} {y : P (repP (resP q e)) ξ′ ζ′} → Rᴾ a _ z y → Rᴾ a j z (backP (resP q e) y)
R-res⁻ʳ : ∀ {j a b b′ ξ ζ ξ′ ζ′} (q : j <ᴵ b) (e : b′ ≅ᴵ b) {z : P a ξ ζ} {y : P (repP (res⁻P q e)) ξ′ ζ′} → Rᴾ a _ z y → Rᴾ a j z (backP (res⁻P q e) y)

R-trʳ e rz = rz
R-trʳ e (rs sa sb r) = rs sa sb (R-trʳ e r)
R-trʳ e (rl h) = rl (λ m → R-trʳ e (h m))
R-trʳ e (ri ej h) = ri ej (λ x y d → R-trʳ e (h x y d))
R-trʳ e (rŝ ec r h) = rŝ ec (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rclo s r h) = rclo s (R-trʳ e r) (λ η η′ d → R-trʳ e (h η η′ d))
R-trʳ e (rcl s r h) = rcl s (R-trʳ e r) (λ η η′ d → R-trʳ e (h η η′ d))
R-trʳ e (rwk r) = rwk (R-trʳ e r)
R-trʳ e (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-trʳ e (f ξ ξ′ d z z′ l))
R-trʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s sρ f) =
  rΩ {r = r} {r′ = ltP (resP q e)} (≅ᴵ-trans ek (eqP (resP q e))) s sρ
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rᴾ a b′ (h ξ ζ (intoV (<→◃ r) z)) (trP e (h′ ξ′ ζ′ (intoV (<→◃ q) (backP (resP q e) w))))) (sym (out-intoV (<→◃ (ltP (resP q e))) z′))
                              (R-trʳ e (f ξ ξ′ ζ ζ′ d dc z _ (intoRᴾ (<→◃ r) (R-resʳ q e (outRᴾ (<→◃ r) l))))))

R-tr⁻ʳ e rz = rz
R-tr⁻ʳ e (rs sa sb r) = rs sa sb (R-tr⁻ʳ e r)
R-tr⁻ʳ e (rl h) = rl (λ m → R-tr⁻ʳ e (h m))
R-tr⁻ʳ e (ri ej h) = ri ej (λ x y d → R-tr⁻ʳ e (h x y d))
R-tr⁻ʳ e (rŝ ec r h) = rŝ ec (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
R-tr⁻ʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
R-tr⁻ʳ e (rclo s r h) = rclo s (R-tr⁻ʳ e r) (λ η η′ d → R-tr⁻ʳ e (h η η′ d))
R-tr⁻ʳ e (rcl s r h) = rcl s (R-tr⁻ʳ e r) (λ η η′ d → R-tr⁻ʳ e (h η η′ d))
R-tr⁻ʳ e (rwk r) = rwk (R-tr⁻ʳ e r)
R-tr⁻ʳ e (rΩ↓ ek s f) = rΩ↓ ek s (λ ξ ξ′ d z z′ l → R-tr⁻ʳ e (f ξ ξ′ d z z′ l))
R-tr⁻ʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s sρ f) =
  rΩ {r = r} {r′ = ltP (res⁻P q e)} (≅ᴵ-trans ek (eqP (res⁻P q e))) s sρ
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → subst (λ w → Rᴾ a b′ (h ξ ζ (intoV (<→◃ r) z)) (tr⁻P e (h′ ξ′ ζ′ (intoV (<→◃ q) (backP (res⁻P q e) w))))) (sym (out-intoV (<→◃ (ltP (res⁻P q e))) z′))
                              (R-tr⁻ʳ e (f ξ ξ′ ζ ζ′ d dc z _ (intoRᴾ (<→◃ r) (R-res⁻ʳ q e (outRᴾ (<→◃ r) l))))))

R-resʳ zero      (s≅ e) l = R-tr⁻ʳ e l
R-resʳ (suc q)   (s≅ e) l = R-resʳ q e l
R-resʳ (lim n q) (l≅ h) l = R-resʳ q (h n) l

R-res⁻ʳ zero      (s≅ e) l = R-trʳ e l
R-res⁻ʳ (suc q)   (s≅ e) l = R-res⁻ʳ q e l
R-res⁻ʳ (lim n q) (l≅ h) l = R-res⁻ʳ q (h n) l
```

## §5 折叠

```agda
R-repᴾ : ∀ {a b φ χ ψ ρ} {X : P a φ χ} {X′ : P b ψ ρ} → φ ∼ᶠ ψ → χ ∼ᶠ ρ → Rᴾ a b X X′ → ∀ n → Rᴾ a b (repᵖ X n) (repᵖ X′ n)
R-repᴾ s c r zero = rz
R-repᴾ s c r (suc zero) = r
R-repᴾ s c r (suc (suc n)) = rwk (R-⊞ s c (R-repᴾ s c r (suc n)) r)

R-ψᵖ : ∀ {a b t t′ φ χ ψ ρ} (q : t <ᴵ a) (q′ : t′ <ᴵ b) → t ≅ᴵ t′ → {x : P a φ χ} {x′ : P b ψ ρ} → Rᴾ a b x x′ → Rᴾ t t′ (ψᵖ q x) (ψᵖ q′ x′)
chRG : ∀ {a b k k′ φ χ ψ ρ ξ ξ′ ζ ζ′} {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl} {fc : ∀ {L} → Ev L ζ → Ev L Fl} {fc′ : ∀ {L} → Ev L ζ′ → Ev L Fl}
       {c₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {c₂ : ∀ {L} → Ev L ζ → Ev L (Fl ⊔ (ζ ⊔ χ))} {c₁′ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))} {c₂′ : ∀ {L} → Ev L ζ′ → Ev L (Fl ⊔ (ζ′ ⊔ ρ))}
       {r : k <ᴵ a} {r′ : k′ <ᴵ b} {h : ∀ ξ ζ → Vs k (<→◃ r) ξ ζ → P a (ξ ⊔ φ) (ζ ⊔ χ)} {h′ : ∀ ξ ζ → Vs k′ (<→◃ r′) ξ ζ → P b (ξ ⊔ ψ) (ζ ⊔ ρ)} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ → ζ ∼ᶠ ζ′ →
       (∀ ξ ξ′ ζ ζ′ → ξ ∼ᶠ ξ′ → ζ ∼ᶠ ζ′ → (z : P k ξ ζ) (z′ : P k′ ξ′ ζ′) → LRᴾ a (<→◃ r) z z′ → Rᴾ a b (h ξ ζ (intoV (<→◃ r) z)) (h′ ξ′ ζ′ (intoV (<→◃ r′) z′))) →
       ∀ n → Rᴾ k k′ (chainᵖ fe fc (λ z → pwk c₁ c₂ (ψᵖ r (h ξ ζ (intoV (<→◃ r) z)))) n) (chainᵖ fe′ fc′ (λ z → pwk c₁′ c₂′ (ψᵖ r′ (h′ ξ′ ζ′ (intoV (<→◃ r′) z)))) n)

R-ψᵖ q q′ et rz = rwk (RΩ̇ᴾ et)
R-ψᵖ q q′ et (rs sa sb r) = rl (R-repᴾ (⊔∼ (∼ᶠ-refl Fl) sa) (⊔∼ (∼ᶠ-refl Fl) sb) (R-ψᵖ q q′ et r))
R-ψᵖ q q′ et (rl h) = rl (λ n → R-ψᵖ q q′ et (h n))
R-ψᵖ q q′ et (ri e h) = ri e (λ x y d → R-ψᵖ q q′ et (h x y d))
R-ψᵖ q q′ et (rŝ e r h) = rŝ e (R-ψᵖ q q′ et r) (λ η ee η′ e′ d → R-ψᵖ q q′ et (h η ee η′ e′ d))
R-ψᵖ q q′ et (rĉ e dz dg r h) = rĉ e dz dg (R-ψᵖ q q′ et r) (λ η ee η′ e′ d → R-ψᵖ q q′ et (h η ee η′ e′ d))
R-ψᵖ q q′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψᵖ q q′ et r)) (λ η η′ d → rwk (R-ψᵖ q q′ et (h η η′ d))))
R-ψᵖ q q′ et (rcl s r h) = rwk (rcl (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψᵖ q q′ et r)) (λ η η′ d → rwk (R-ψᵖ q q′ et (h η η′ d))))
R-ψᵖ q q′ et (rwk r) = rwk (R-ψᵖ q q′ et r)
R-ψᵖ q q′ et (rΩ↓ ek s f) = rΩ↓ ek (⊔∼ (∼ᶠ-refl Fl) s) (λ ξ ξ′ d z z′ l → rwk (R-ψᵖ q q′ et (f ξ ξ′ d z z′ l)))
R-ψᵖ {t = t} {t′} q q′ et (rΩ {φ = φ} {χ} {ψ} {ρ} {k} {k′} {r = r} {r′} {h} {h′} ek s sρ f) with <ᴵ-dec r q | <ᴵ-dec r′ q′
... | injᵃ (via e p) | injᵃ (via e′ p′) =
  rΩ {r = p} {r′ = p′} (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans ek e′)) (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ)
     (λ ξ ξ′ ζ ζ′ d dc z z′ l → rwk (subst₂ (λ w w′ → Rᴾ t t′ (ψᵖ q (h ξ ζ (intoV (<→◃ r) (tr⁻P e w)))) (ψᵖ q′ (h′ ξ′ ζ′ (intoV (<→◃ r′) (tr⁻P e′ w′))))) (sym (out-intoV (<→◃ p) z)) (sym (out-intoV (<→◃ p′) z′))
                                    (R-ψᵖ q q′ et (f ξ ξ′ ζ ζ′ d dc _ _ (intoRᴾ (<→◃ r) (R-tr⁻ˡ e (R-tr⁻ʳ e′ (outRᴾ (<→◃ p) l))))))))
... | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
... | injᵃ a | injᶜ c = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ek)))))
... | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
... | injᶜ c | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c) ek))))
... | injᵇ _ | injᵇ _ = rl (λ n → rwk (R-ψᵖ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Fl ⊔ χ) (Fl ⊔ ρ) (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ) _ _ (intoRᴾ (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {fc = proj₁} {fc′ = proj₁} {c₁ = dupr2} {c₂ = dupr2} {c₁′ = dupr2} {c₂′ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ) f n)))))
... | injᵇ _ | injᶜ _ = rl (λ n → rwk (R-ψᵖ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Fl ⊔ χ) (Fl ⊔ ρ) (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ) _ _ (intoRᴾ (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {fc = proj₁} {fc′ = proj₁} {c₁ = dupr2} {c₂ = dupr2} {c₁′ = dupr2} {c₂′ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ) f n)))))
... | injᶜ _ | injᵇ _ = rl (λ n → rwk (R-ψᵖ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Fl ⊔ χ) (Fl ⊔ ρ) (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ) _ _ (intoRᴾ (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {fc = proj₁} {fc′ = proj₁} {c₁ = dupr2} {c₂ = dupr2} {c₁′ = dupr2} {c₂′ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ) f n)))))
... | injᶜ _ | injᶜ _ = rl (λ n → rwk (R-ψᵖ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (Fl ⊔ χ) (Fl ⊔ ρ) (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ) _ _ (intoRᴾ (<→◃ r) (chRG {fe = proj₁} {fe′ = proj₁} {fc = proj₁} {fc′ = proj₁} {c₁ = dupr2} {c₂ = dupr2} {c₁′ = dupr2} {c₂′ = dupr2} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) (⊔∼ (∼ᶠ-refl Fl) sρ) f n)))))

chRG ek sξ sζ f zero = rwk (RΩ̇ᴾ ek)
chRG {ξ = ξ} {ξ′} {ζ} {ζ′} {fe = fe} {fe′} {fc} {fc′} {c₁} {c₂} {c₁′} {c₂′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek sξ sζ f (suc n) =
  rwk (R-ψᵖ r r′ ek (f ξ ξ′ ζ ζ′ sξ sζ _ _ (intoRᴾ (<→◃ r) (chRG {fe = fe} {fe′ = fe′} {fc = fc} {fc′ = fc′} {c₁ = c₁} {c₂ = c₂} {c₁′ = c₁′} {c₂′ = c₂′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek sξ sζ f n))))
```

## §6 目标在高度 1

```agda
R-Ψ : ∀ {a b t t′ φ χ ψ ρ ℓ ℓ′} (e : Ev ℓ χ) (p : t <ᴵ ℓ) (e′ : Ev ℓ′ ρ) (p′ : t′ <ᴵ ℓ′) → t ≅ᴵ t′ → {x : P a φ χ} {x′ : P b ψ ρ} → Rᴾ a b x x′ → Rᵒ t t′ (Ψ e p x) (Ψ e′ p′ x′)
chRΨ : ∀ {a b k k′ φ χ ψ ρ ξ ξ′ ℓ ℓ′} (e : Ev ℓ χ) (e′ : Ev ℓ′ ρ) → {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fe′ : ∀ {L} → Ev L ξ′ → Ev L Fl}
       {c₁ : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {c₁′ : ∀ {L} → Ev L ξ′ → Ev L (Fl ⊔ (ξ′ ⊔ ψ))} {ac : ∀ {L} → Ev L χ → k <ᴵ L} {ac′ : ∀ {L} → Ev L ρ → k′ <ᴵ L}
       {h : ∀ ξ → O k ξ → P a (ξ ⊔ φ) χ} {h′ : ∀ ξ → O k′ ξ → P b (ξ ⊔ ψ) ρ} → k ≅ᴵ k′ → ξ ∼ᶠ ξ′ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → Rᵒ k k′ z z′ → Rᴾ a b (h ξ z) (h′ ξ′ z′)) →
       ∀ n → Rᵒ k k′ (chainᵒ fe (λ z → owk c₁ (Ψ e (ac e) (h ξ z))) n) (chainᵒ fe′ (λ z → owk c₁′ (Ψ e′ (ac′ e′) (h′ ξ′ z))) n)

R-Ψ e p e′ p′ et rz = rwk (RΩ̇ et)
R-Ψ e p e′ p′ et (rs sa sb r) = rl (R-rep (⊔∼ (∼ᶠ-refl Fl) sa) (R-Ψ e p e′ p′ et r))
R-Ψ e p e′ p′ et (rl h) = rl (λ n → R-Ψ e p e′ p′ et (h n))
R-Ψ e p e′ p′ et (ri d h) = ri d (λ x y dd → R-Ψ e p e′ p′ et (h x y dd))
R-Ψ e p e′ p′ et (rŝ d r h) = rŝ d (R-Ψ e p e′ p′ et r) (λ η ee η′ e₁ dd → R-Ψ e p e′ p′ et (h η ee η′ e₁ dd))
R-Ψ e p e′ p′ et (rĉ d dz dg r h) = rĉ d dz dg (R-Ψ e p e′ p′ et r) (λ η ee η′ e₁ dd → R-Ψ e p e′ p′ et (h η ee η′ e₁ dd))
R-Ψ e p e′ p′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-Ψ e p e′ p′ et r)) (λ η η′ d → rwk (R-Ψ e p e′ p′ et (h η η′ d))))
R-Ψ e p e′ p′ et (rcl {χ = χ} {ρ = ρ} s r h) =
  rŝ (bound-≅ (⊔∼ s (fk∼ z≅)) e p e′ p′ et) (R-Ψ e p e′ p′ et r)
     (λ η d η′ d′ eη → R-Ψ (evη χ (bound (χ ⊔ fk zero) e p) η d) (lim 0 (iF (bound (χ ⊔ fk zero) e p))) (evη ρ (bound (ρ ⊔ fk zero) e′ p′) η′ d′) (lim 0 (iF (bound (ρ ⊔ fk zero) e′ p′))) et (h η η′ eη))
R-Ψ e p e′ p′ et (rwk {lc = lc} {lc′ = lc′} r) = rwk (R-Ψ (lc e) p (lc′ e′) p′ et r)
R-Ψ {t = t} {t′} e p e′ p′ et (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {k} {k′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f) with <ᴵ-dec (ac e) p | <ᴵ-dec (ac′ e′) p′
... | injᵃ (via d q) | injᵃ (via d′ q′) =
  rΩ {r = q} {r′ = q′} (≅ᴵ-trans (≅ᴵ-sym d) (≅ᴵ-trans ek d′)) (⊔∼ (∼ᶠ-refl Fl) s)
     (λ ξ ξ′ dd z z′ l → rwk (subst₂ (λ w w′ → Rᵒ t t′ (Ψ e p (h ξ (tr⁻O d w))) (Ψ e′ p′ (h′ ξ′ (tr⁻O d′ w′)))) (sym (out-intoU (<→◃ q) z)) (sym (out-intoU (<→◃ q′) z′))
                                    (R-Ψ e p e′ p′ et (f ξ ξ′ dd _ _ (OR.R-tr⁻ˡ d (OR′.R-tr⁻ʳ d′ (outR (<→◃ q) l)))))))
... | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
... | injᵃ a | injᶜ c = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ek)))))
... | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
... | injᶜ c | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c) ek))))
... | injᵇ _ | injᵇ _ = rl (λ n → rwk (R-Ψ e p e′ p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (chRΨ e e′ {fe = proj₁} {fe′ = proj₁} {c₁ = dupr2} {c₁′ = dupr2} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) f n))))
... | injᵇ _ | injᶜ _ = rl (λ n → rwk (R-Ψ e p e′ p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (chRΨ e e′ {fe = proj₁} {fe′ = proj₁} {c₁ = dupr2} {c₁′ = dupr2} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) f n))))
... | injᶜ _ | injᵇ _ = rl (λ n → rwk (R-Ψ e p e′ p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (chRΨ e e′ {fe = proj₁} {fe′ = proj₁} {c₁ = dupr2} {c₁′ = dupr2} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) f n))))
... | injᶜ _ | injᶜ _ = rl (λ n → rwk (R-Ψ e p e′ p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (chRΨ e e′ {fe = proj₁} {fe′ = proj₁} {c₁ = dupr2} {c₁′ = dupr2} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) f n))))
R-Ψ {t = t} {t′} e p e′ p′ et (rΩ {φ = φ} {χ} {ψ} {ρ} {k} {k′} {fc = fc} {fc′ = fc′} {r = r} {r′} {h} {h′} ek s sρ f) =
  rl (λ n → rwk (R-Ψ (e , e) p (e′ , e′) p′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) χ ρ (⊔∼ (∼ᶠ-refl Fl) s) sρ _ _ (intoRᴾ (<→◃ r)
     (chRG {fe = proj₁} {fe′ = proj₁} {fc = fc} {fc′ = fc′} {c₁ = dupr2} {c₂ = λ u → fc u , (u , u)} {c₁′ = dupr2} {c₂′ = λ u → fc′ u , (u , u)} {r = r} {r′ = r′} {h = h} {h′ = h′} ek (⊔∼ (∼ᶠ-refl Fl) s) sρ f n)))))

chRΨ e e′ ek sξ f zero = rwk (RΩ̇ ek)
chRΨ {ξ = ξ} {ξ′ = ξ′} e e′ {fe = fe} {fe′ = fe′} {c₁ = c₁} {c₁′ = c₁′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek sξ f (suc n) =
  rwk (R-Ψ e (ac e) e′ (ac′ e′) ek (f ξ ξ′ sξ _ _ (chRΨ e e′ {fe = fe} {fe′ = fe′} {c₁ = c₁} {c₁′ = c₁′} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek sξ f n)))
```
