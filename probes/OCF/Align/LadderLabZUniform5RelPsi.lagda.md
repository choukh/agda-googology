> **机械克隆, 验收用.** 由 `ScafLadderZUniform5RelPsi` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆.** 由 `Uniform5RelPsi` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (五): 互模拟对 $\psi_{\Omega+\tau}$ 封闭, 求值

> 接 [Uniform5Rel](Uniform5Rel.lagda.md). `R-trʳ` 族 (右侧的搬运), `R-ψ` (比较结果在 $\cong$ 下一致: 非对角由 `clash` 排除, 穿透分支两侧的 `tr⁻O` 由 `R-tr⁻ˡ`/`R-tr⁻ʳ` 吸收), `R→Rd` (求值).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderLabZUniform5RelPsi where

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
open import OCF.Align.LadderLabZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.LadderLabZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.LadderLabZDecoupleBase using (ΩΩ)
open import OCF.Align.LadderLabZStage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.LadderLabZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.LadderLabZStandardOmega using ()
open import OCF.Align.LadderLabZGoodLBase
open import OCF.Align.LadderLabZUniformS
open import OCF.Align.LadderLabZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.LadderLabZUniform3Rel
open import OCF.Align.LadderLabZUniform3SqABase
open import OCF.Align.LadderLabZUniform3Hon
open import OCF.Align.LadderLabZUniform3Depth2Class
open import OCF.Align.LadderLabZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)

open import OCF.Align.LadderLabZUniform3Full using (∅ᴿ-goodʰ)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Bachmann using (clash)
open import OCF.Align.LadderLabZUniform5Head
open import OCF.Align.LadderLabZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.LadderLabZUniform4Two
open RestrO
open import OCF.Align.LadderLabZUniform5Tail using (out-intoU)
open import OCF.Align.LadderLabZUniform5Rel
```

## §1 右侧的搬运

```agda
R-trʳ  : ∀ {a b b′ φ ψ} (e : b ≅ᴵ b′) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a b′ x (trO e y)
R-tr⁻ʳ : ∀ {a b b′ φ ψ} (e : b′ ≅ᴵ b) {x : O a φ} {y : O b ψ} → Rᵒ a b x y → Rᵒ a b′ x (tr⁻O e y)
R-resʳ : ∀ {j a b b′ ξ ξ′} (q : j <ᴵ b) (e : b ≅ᴵ b′) {z : O a ξ} {y : O (repO (resO q e)) ξ′} → Rᵒ a _ z y → Rᵒ a j z (backO (resO q e) y)
R-res⁻ʳ : ∀ {j a b b′ ξ ξ′} (q : j <ᴵ b) (e : b′ ≅ᴵ b) {z : O a ξ} {y : O (repO (res⁻O q e)) ξ′} → Rᵒ a _ z y → Rᵒ a j z (backO (res⁻O q e) y)

R-trʳ e rz = rz
R-trʳ e (rs sa r) = rs sa (R-trʳ e r)
R-trʳ e (rl h) = rl (λ m → R-trʳ e (h m))
R-trʳ e (ri ej h) = ri ej (λ x y d → R-trʳ e (h x y d))
R-trʳ e (rŝ ec r h) = rŝ ec (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-trʳ e r) (λ η ee η′ e′ d → R-trʳ e (h η ee η′ e′ d))
R-trʳ e (rclo s r h) = rclo s (R-trʳ e r) (λ η η′ d → R-trʳ e (h η η′ d))
R-trʳ e (rwk r) = rwk (R-trʳ e r)
R-trʳ (s≅ e) (rob {r = zero} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek e) (R-trʳ e l) (R-trʳ (s≅ e) r)
R-trʳ (l≅ h) (rob {r = zero} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (h n)) (R-trʳ (h n) l) (R-trʳ (l≅ h) r)
R-trʳ (s≅ e) (rob {r = self m} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek e) (R-trʳ e l) (R-trʳ (s≅ e) r)
R-trʳ (l≅ h) (rob {r = self m} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (h n)) (R-trʳ (h n) l) (R-trʳ (l≅ h) r)
R-trʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s f) =
  rΩ {r = r} {r′ = ltO (resO q e)} (≅ᴵ-trans ek (eqO (resO q e))) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a b′ (h ξ (intoU (<→◃ r) z)) (trO e (h′ ξ′ (intoU (<→◃ q) (backO (resO q e) w))))) (sym (out-intoU (<→◃ (ltO (resO q e))) z′))
                              (R-trʳ e (f ξ ξ′ d z _ (intoR (<→◃ r) (R-resʳ q e (outR (<→◃ r) l))))))

R-tr⁻ʳ e rz = rz
R-tr⁻ʳ e (rs sa r) = rs sa (R-tr⁻ʳ e r)
R-tr⁻ʳ e (rl h) = rl (λ m → R-tr⁻ʳ e (h m))
R-tr⁻ʳ e (ri ej h) = ri ej (λ x y d → R-tr⁻ʳ e (h x y d))
R-tr⁻ʳ e (rŝ ec r h) = rŝ ec (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
R-tr⁻ʳ e (rĉ ec dz dg r h) = rĉ ec dz dg (R-tr⁻ʳ e r) (λ η ee η′ e′ d → R-tr⁻ʳ e (h η ee η′ e′ d))
R-tr⁻ʳ e (rclo s r h) = rclo s (R-tr⁻ʳ e r) (λ η η′ d → R-tr⁻ʳ e (h η η′ d))
R-tr⁻ʳ e (rwk r) = rwk (R-tr⁻ʳ e r)
R-tr⁻ʳ (s≅ e) (rob {r = zero} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym e)) (R-tr⁻ʳ e l) (R-tr⁻ʳ (s≅ e) r)
R-tr⁻ʳ (l≅ h) (rob {r = zero} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym (h n))) (R-tr⁻ʳ (h n) l) (R-tr⁻ʳ (l≅ h) r)
R-tr⁻ʳ (s≅ e) (rob {r = self m} {r′ = zero} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym e)) (R-tr⁻ʳ e l) (R-tr⁻ʳ (s≅ e) r)
R-tr⁻ʳ (l≅ h) (rob {r = self m} {r′ = self n} ek l r) = rob (≅ᴵ-trans ek (≅ᴵ-sym (h n))) (R-tr⁻ʳ (h n) l) (R-tr⁻ʳ (l≅ h) r)
R-tr⁻ʳ {a} {b′ = b′} e (rΩ {r = r} {r′ = q} {h} {h′} ek s f) =
  rΩ {r = r} {r′ = ltO (res⁻O q e)} (≅ᴵ-trans ek (eqO (res⁻O q e))) s
     (λ ξ ξ′ d z z′ l → subst (λ w → Rᵒ a b′ (h ξ (intoU (<→◃ r) z)) (tr⁻O e (h′ ξ′ (intoU (<→◃ q) (backO (res⁻O q e) w))))) (sym (out-intoU (<→◃ (ltO (res⁻O q e))) z′))
                              (R-tr⁻ʳ e (f ξ ξ′ d z _ (intoR (<→◃ r) (R-res⁻ʳ q e (outR (<→◃ r) l))))))

R-resʳ zero      (s≅ e) l = R-tr⁻ʳ e l
R-resʳ (suc q)   (s≅ e) l = R-resʳ q e l
R-resʳ (lim n q) (l≅ h) l = R-resʳ q (h n) l

R-res⁻ʳ zero      (s≅ e) l = R-trʳ e l
R-res⁻ʳ (suc q)   (s≅ e) l = R-res⁻ʳ q e l
R-res⁻ʳ (lim n q) (l≅ h) l = R-res⁻ʳ q (h n) l
```

## §2 对 $\psi_{\Omega+\tau}$ 封闭

```agda
R-rep : ∀ {a b φ ψ} {X : O a φ} {X′ : O b ψ} → φ ∼ᶠ ψ → Rᵒ a b X X′ → ∀ n → Rᵒ a b (repᵒ X n) (repᵒ X′ n)
R-rep s r zero = rz
R-rep s r (suc zero) = r
R-rep s r (suc (suc n)) = rwk (R-⊕ s (R-rep s r (suc n)) r)

R-ψ : ∀ {a b t t′ φ ψ} (q : t <ᴵ a) (q′ : t′ <ᴵ b) → t ≅ᴵ t′ → {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rᵒ t t′ (ψᵒ q x) (ψᵒ q′ x′)
chRR : ∀ {a b k k′ φ ψ} {r : k <ᴵ a} {r′ : k′ <ᴵ b} {h : ∀ ξ → Us k (<→◃ r) ξ → O a (ξ ⊔ φ)} {h′ : ∀ ξ → Us k′ (<→◃ r′) ξ → O b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LRᵒ a (<→◃ r) z z′ → Rᵒ a b (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) →
       ∀ n → Rᵒ k k′ (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r′ (h′ (Fl ⊔ ψ) (intoU (<→◃ r′) z)))) n)

R-ψ q q′ et rz = rwk (RΩ̇ et)
R-ψ q q′ et (rs sa r) = rl (R-rep (⊔∼ (∼ᶠ-refl Fl) sa) (R-ψ q q′ et r))
R-ψ q q′ et (rl h) = rl (λ n → R-ψ q q′ et (h n))
R-ψ q q′ et (ri e h) = ri e (λ x y d → R-ψ q q′ et (h x y d))
R-ψ q q′ et (rŝ e r h) = rŝ e (R-ψ q q′ et r) (λ η ee η′ e′ d → R-ψ q q′ et (h η ee η′ e′ d))
R-ψ q q′ et (rĉ e dz dg r h) = rĉ e dz dg (R-ψ q q′ et r) (λ η ee η′ e′ d → R-ψ q q′ et (h η ee η′ e′ d))
R-ψ q q′ et (rclo s r h) = rwk (rclo (⊔∼ (∼ᶠ-refl Fl) s) (rwk (R-ψ q q′ et r)) (λ η η′ d → rwk (R-ψ q q′ et (h η η′ d))))
R-ψ q q′ et (rwk r) = rwk (R-ψ q q′ et r)
R-ψ q q′ et (rob _ l r) = R-ψ q q′ et r
R-ψ {t = t} {t′} q q′ et (rΩ {φ = φ} {ψ} {k} {k′} {r = r} {r′} {h} {h′} ek s f) with <ᴵ-dec r q | <ᴵ-dec r′ q′
... | injᵃ (via e p) | injᵃ (via e′ p′) =
  rΩ {r = p} {r′ = p′} (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans ek e′)) (⊔∼ (∼ᶠ-refl Fl) s)
     (λ ξ ξ′ d z z′ l → rwk (subst₂ (λ w w′ → Rᵒ t t′ (ψᵒ q (h ξ (intoU (<→◃ r) (tr⁻O e w)))) (ψᵒ q′ (h′ ξ′ (intoU (<→◃ r′) (tr⁻O e′ w′))))) (sym (out-intoU (<→◃ p) z)) (sym (out-intoU (<→◃ p′) z′))
                                    (R-ψ q q′ et (f ξ ξ′ d _ _ (intoR (<→◃ r) (R-tr⁻ˡ e (R-tr⁻ʳ e′ (outR (<→◃ p) l))))))))
... | injᵃ a | injᵇ b = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ et b) (≅ᴵ-sym ek))))
... | injᵃ a | injᶜ c = ⊥-elim (clash a (inj₂ (≅ᴵ-trans et (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym ek)))))
... | injᵇ b | injᵃ a = ⊥-elim (clash a (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym et) b) ek)))
... | injᶜ c | injᵃ a = ⊥-elim (clash a (inj₂ (≅ᴵ-trans (≅ᴵ-sym et) (≅ᴵ-trans (≅ᴵ-sym c) ek))))
... | injᵇ _ | injᵇ _ = rl (λ n → rwk (R-ψ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᵇ _ | injᶜ _ = rl (λ n → rwk (R-ψ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᶜ _ | injᵇ _ = rl (λ n → rwk (R-ψ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
... | injᶜ _ | injᶜ _ = rl (λ n → rwk (R-ψ q q′ et (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))

chRR ek s f zero = rwk (RΩ̇ ek)
chRR {φ = φ} {ψ = ψ} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f (suc n) =
  rwk (R-ψ r r′ ek (f (Fl ⊔ φ) (Fl ⊔ ψ) (⊔∼ (∼ᶠ-refl Fl) s) _ _ (intoR (<→◃ r) (chRR {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n))))
```

## §3 求值

```agda
chRE : ∀ {a b k k′ φ ψ} {fe : ∀ {L} → Ev L φ → Ev L Fl} {fe′ : ∀ {L} → Ev L ψ → Ev L Fl} {r : k <ᴵ a} {r′ : k′ <ᴵ b}
       {h : ∀ ξ → Us k (<→◃ r) ξ → O a (ξ ⊔ φ)} {h′ : ∀ ξ → Us k′ (<→◃ r′) ξ → O b (ξ ⊔ ψ)} → k ≅ᴵ k′ → φ ∼ᶠ ψ →
       (∀ ξ ξ′ → ξ ∼ᶠ ξ′ → (z : O k ξ) (z′ : O k′ ξ′) → LRᵒ a (<→◃ r) z z′ → Rᵒ a b (h ξ (intoU (<→◃ r) z)) (h′ ξ′ (intoU (<→◃ r′) z′))) →
       ∀ n → Rᵒ k k′ (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n) (chainᵒ fe′ (λ z → owk (λ v → fe′ v , (v , v)) (ψᵒ r′ (h′ ψ (intoU (<→◃ r′) z)))) n)
chRE ek s f zero = rwk (RΩ̇ ek)
chRE {φ = φ} {ψ = ψ} {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f (suc n) =
  rwk (R-ψ r r′ ek (f φ ψ s _ _ (intoR (<→◃ r) (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n))))

R→Rd : ∀ {a b φ ψ} {x : O a φ} {x′ : O b ψ} → Rᵒ a b x x′ → Rd 0 (ψ̄ x) (ψ̄ x′)
R→Rd rz = wkRd 0 _ _ (H→R 0 (proj₂ ∅ᴿ-goodʰ))
R→Rd (rs s r) = sucRᴬ (R→Rd r)
R→Rd (rl h) = limRd 0 (λ n → R→Rd (h n))
R→Rd (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} e h) = limᵢRd 0 {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ (f x)} {H′ = λ x → ψ̄ (f′ x)} e (λ x y d → R→Rd (h x y d))
R→Rd (rŝ e r h) = ŝRd 0 e (R→Rd r) (λ η ee η′ e′ d → R→Rd (h η ee η′ e′ d))
R→Rd (rĉ e dz dg r h) = ĉRd 0 e dz dg (R→Rd r) (λ η ee η′ e′ d → R→Rd (h η ee η′ e′ d))
R→Rd (rclo {t = t} {t′} {g} {g′} s r h) = cloRd 0 {t = ψ̄ t} {g = λ η → ψ̄ (g η)} {t′ = ψ̄ t′} {g′ = λ η → ψ̄ (g′ η)} s (R→Rd r) (λ η η′ d → R→Rd (h η η′ d))
R→Rd (rwk {le = le} {le′ = le′} r) = wkRd 0 le le′ (R→Rd r)
R→Rd (rob _ l r) = R→Rd r
R→Rd (rΩ {φ = φ} {ψ} {fe = fe} {fe′} {r} {r′} {h} {h′} ek s f) =
  limRd 0 (λ n → wkRd 0 _ _ (R→Rd (f φ ψ s _ _ (intoR (<→◃ r) (chRE {fe = fe} {fe′ = fe′} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s f n)))))
```
