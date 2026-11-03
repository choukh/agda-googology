# 阶梯 (六): 求值与标签

> 结论写在 [ScafLadder](ScafLadder.lagda.md). 由 [Uniform5Eval](Uniform5Eval.lagda.md) 改写. `Rd`, `Wd`, `Od` 的行不变, 新的只有 `lcl` (目标可数时界只读 $\chi$, 经 `pickF` 用已有的 `ŝWd`, `ŝOd`), `lΩ↓`, `lΩ` (`LimRow` 对 $\nu$ 与 $\Omega+\nu$ 同一份). **这里没有新的证书规则: 证书全由已有的 `Od` 的行造出.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderEval where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

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
open import OCF.Align.ScafLadderPsi
open import OCF.Align.ScafLadderRel
open import OCF.Align.ScafLadderZUniform5Eval using (OkW; Cv-of; Fw→[]; module LimRow; inp₀)
```

## §1 互模拟求值

```agda
R→Rdᴾ : ∀ {a b φ χ ψ ρ ℓ ℓ′} {x : P a φ χ} {x′ : P b ψ ρ} → Rᴾ a b x x′ → (e : Ev ℓ χ) (z : zero <ᴵ ℓ) (e′ : Ev ℓ′ ρ) (z′ : zero <ᴵ ℓ′) → Rd 0 (ψ̄ᴾ e z x) (ψ̄ᴾ e′ z′ x′)
R→Rdᴾ rz e z e′ z′ = wkRd 0 _ _ (H→R 0 (proj₂ ∅ᴿ-goodʰ))
R→Rdᴾ (rs s c r) e z e′ z′ = sucRᴬ (R→Rdᴾ r e z e′ z′)
R→Rdᴾ (rl h) e z e′ z′ = limRd 0 (λ n → R→Rdᴾ (h n) e z e′ z′)
R→Rdᴾ (ri {ac = ac} {ac′ = ac′} {f = f} {f′ = f′} d h) e z e′ z′ = limᵢRd 0 {ac = ac} {ac′ = ac′} {H = λ x → ψ̄ᴾ e z (f x)} {H′ = λ x → ψ̄ᴾ e′ z′ (f′ x)} d (λ x y dd → R→Rdᴾ (h x y dd) e z e′ z′)
R→Rdᴾ (rŝ d r h) e z e′ z′ = ŝRd 0 d (R→Rdᴾ r e z e′ z′) (λ η ee η′ e₁ dd → R→Rdᴾ (h η ee η′ e₁ dd) e z e′ z′)
R→Rdᴾ (rĉ d dz dg r h) e z e′ z′ = ĉRd 0 d dz dg (R→Rdᴾ r e z e′ z′) (λ η ee η′ e₁ dd → R→Rdᴾ (h η ee η′ e₁ dd) e z e′ z′)
R→Rdᴾ (rclo {t = t} {t′} {g} {g′} s r h) e z e′ z′ = cloRd 0 {t = ψ̄ᴾ e z t} {g = λ η → ψ̄ᴾ e z (g η)} {t′ = ψ̄ᴾ e′ z′ t′} {g′ = λ η → ψ̄ᴾ e′ z′ (g′ η)} s (R→Rdᴾ r e z e′ z′) (λ η η′ d → R→Rdᴾ (h η η′ d) e z e′ z′)
R→Rdᴾ (rcl {χ = χ} {ρ = ρ} s r h) e z e′ z′ =
  ŝRd 0 (bound-≅ (⊔∼ s (fk∼ z≅)) e z e′ z′ z≅) (R→Rdᴾ r e z e′ z′)
      (λ η d η′ d′ eη → R→Rdᴾ (h η η′ eη) (evη χ (bound (χ ⊔ fk zero) e z) η d) (lim 0 (iF (bound (χ ⊔ fk zero) e z))) (evη ρ (bound (ρ ⊔ fk zero) e′ z′) η′ d′) (lim 0 (iF (bound (ρ ⊔ fk zero) e′ z′))))
R→Rdᴾ (rwk {le = le} {lc = lc} {le′ = le′} {lc′ = lc′} r) e z e′ z′ = wkRd 0 le le′ (R→Rdᴾ r (lc e) z (lc′ e′) z′)
R→Rdᴾ (rΩ↓ {φ = φ} {χ} {ψ} {ρ} {fe = fe} {fe′} {ac} {ac′} {h} {h′} ek s f) e z e′ z′ =
  limRd 0 (λ n → wkRd 0 _ _ (R→Rdᴾ (f φ ψ s _ _ (chRΨ e e′ {fe = fe} {fe′ = fe′} {c₁ = λ v → fe v , (v , v)} {c₁′ = λ v → fe′ v , (v , v)} {ac = ac} {ac′ = ac′} {h = h} {h′ = h′} ek s f n)) e z e′ z′))
R→Rdᴾ (rΩ {φ = φ} {χ} {ψ} {ρ} {fe = fe} {fe′} {fc} {fc′} {r} {r′} {h} {h′} ek s sρ f) e z e′ z′ =
  limRd 0 (λ n → wkRd 0 _ _ (R→Rdᴾ (f φ ψ χ ρ s sρ _ _ (intoRᴾ (<→◃ r) (chRG {fe = fe} {fe′ = fe′} {fc = fc} {fc′ = fc′} {c₁ = λ v → fe v , (v , v)} {c₂ = λ v → fc v , (v , v)} {c₁′ = λ v → fe′ v , (v , v)} {c₂′ = λ v → fc′ v , (v , v)} {r = r} {r′ = r′} {h = h} {h′ = h′} ek s sρ f n))) (e , e) z (e′ , e′) z′))
```

## §2 高度 1 的闭包: 目标可数时的界

```agda
pickF : ∀ {χ ps y ys w₀ ℓ} → FW₀ (χ ⊔ fk zero) ps y ys → (I₀ : Idx w₀) → zero ≼ lvI I₀ → Ob w₀ ps y ys → (B : Top zero ℓ (χ ⊔ fk zero)) →
        Σ T λ w′ → Σ (Idx w′) λ Iw′ → (Bd B ⊑ᴵ suc (lvI Iw′)) × Ob w′ ps y ys
pickF {χ} {ps} {y} {ys} fw I₀ z₀ o B = Pick.pw Pk , Pick.pI Pk ,
    ubd B (≼→≺s (Pick.pc Pk)) (λ k → dem k (pd (Pick.pF Pk k))) , Pick.pP Pk
  where
  Pk : Pick (λ w′ → Ob w′ ps y ys) (χ ⊔ fk zero) Tr0 zero
  Pk = pickMax (χ ⊔ fk zero) Tr0 fw I₀ o z₀
  pd : ∀ {K} → (K ≅ᴵ zero) ⊎ (K ≼ lvI (Pick.pI Pk)) → (K ≺ᴵ suc (lvI (Pick.pI Pk))) ⊎ (K ≅ᴵ zero)
  pd (inj₁ k0) = inj₂ k0
  pd (inj₂ kw) = inj₁ (≼→≺s kw)
```

## §3 $W$ 部分

```agda
Lp→W : ∀ {c′ c m φ χ ℓ₂} {x : P c′ φ χ} {u} → OkW m c → (e : Ev ℓ₂ χ) (z : zero <ᴵ ℓ₂) → Lp c′ m x u → Wd c 0 (ψ̄ᴾ e z x) u
Lp→W ok e z lz = wkW 0 _ (G→W 0 ∅ᴿ-goodʰ)
Lp→W ok e z (ls {ps = ps} {y} {ys} {a = a} cc F Fχ l) = sucWʰ {ps = ps} {y = y} {ys = ys} {R = ψ̄ᴾ e z a} cc (Lp→W ok e z l)
Lp→W ok e z (ll {ps = ps} {y} {ys} {F} cc h) = limWd 0 {ps = ps} {y = y} {ys = ys} {F = λ n → ψ̄ᴾ e z (F n)} cc (λ n → Lp→W ok e z (h n))
Lp→W {c = c} {m = m} ok e z (li {ps = ps} {y} {ys} {ν} {j} {ac} {f} cc I d hP hI) =
  limᵢWd 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ᴾ e z (f x)} cc I d (InpW j) (inp₀ I d)
         (λ kj o → frL₊ kj (proj₁ o) , λ _ → proj₂ o , FHν I d)
         (λ η x l {i} s ui → Lp→W {m = wkm i} (≼-refl i) e z (hP η x l s (Cv-of ok ui)))
         (λ {η} {x} ix → Lp→W ok e z (hI η x ix))
Lp→W ok e z (lĉ {ps = ps} {y} {ys} {o₀ = o₀} {o} cc K h₀ hk) =
  ĉWd 0 {ps = ps} {y = y} {ys = ys} {O₀ = ψ̄ᴾ e z o₀} {O = λ η d → ψ̄ᴾ e z (o η d)} cc K (Lp→W ok e z h₀) (λ k → Lp→W ok e z (hk k))
Lp→W ok e z (lŝ {ps = ps} {y} {ys} {t = t} {g} cc I b o h₀ hg) =
  ŝWd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ᴾ e z t} {G = λ η d → ψ̄ᴾ e z (g η d)} cc I b o (Lp→W ok e z h₀) (λ θ Y hY lY nθ lt d → Lp→W ok e z (hg θ Y hY lY nθ lt d))
Lp→W ok e z (lclo {ps = ps} {y} {ys} {t} {g} F cc h₀ hg) =
  cloWd 0 {ps = ps} {y = y} {ys = ys} {t = ψ̄ᴾ e z t} {g = λ η → ψ̄ᴾ e z (g η)} (Fw→[] ok F) cc (Lp→W ok e z h₀) (λ θ Y hY lY nθ lt → Lp→W ok e z (hg θ Y hY lY nθ lt))
Lp→W ok e z (lcl {χ = χ} {ps = ps} {y} {ys} {t = t} {g} G cc I₀ z₀ o h₀ hg) =
  ŝWd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ᴾ e z t} {G = λ η d → ψ̄ᴾ (evη χ B η d) (lim 0 (iF B)) (g η)} cc (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk))) (proj₂ (proj₂ (proj₂ Pk)))
      (Lp→W ok e z h₀) (λ θ Y hY lY nθ lt d → Lp→W ok (evη χ B (toLevel Y hY) d) (lim 0 (iF B)) (hg θ Y hY lY nθ lt))
  where
  B = bound (χ ⊔ fk zero) e z
  Pk = pickF G I₀ z₀ o B
Lp→W ok e z (lwk {le = le} {le′ = le′} l) = wkW 0 le (Lp→W ok (le′ e) z l)
Lp→W {m = m} ok e z (lΩ↓ {φ = φ} {χ} {ps} {y} {ys} {ν = ν} {fe} {ac} {h} cc Iν ek f) =
  LimRow.limμW {ν = ν} {ps} {y} {ys} cc {F = λ n → wk 0 (λ v → v , v) (ψ̄ᴾ e z (h φ (chainᵒ fe (λ y₁ → owk (λ v → fe v , (v , v)) (Ψ e (ac e) (h φ y₁))) n)))}
    (λ n → wkW 0 (λ v → v , v) (Lp→W ok e z (f (Cv-refl m) φ _ _ (chainΨ e {fe = fe} {a = λ v → fe v , (v , v)} ac {h = h} Iν ek f n))))
Lp→W {m = m} ok e z (lΩ {φ = φ} {χ} {ps} {y} {ys} {ν = ν} {fe} {fc} {r} {h} cc Iν ek f) =
  LimRow.limμW {ν = μ ν} {ps} {y} {ys} cc {F = λ n → wk 0 (λ v → v , v) (ψ̄ᴾ (e , e) z (h φ χ (intoV (<→◃ r) (chainᵖ fe fc (λ y₁ → pwk (λ v → fe v , (v , v)) (λ v → fc v , (v , v)) (ψᵖ r (h φ χ (intoV (<→◃ r) y₁)))) n))))}
    (λ n → wkW 0 (λ v → v , v) (Lp→W ok (e , e) z (f (Cv-refl m) φ χ _ _ (intoQ (<→◃ r) (chainG {fe = fe} {fc = fc} {a = λ v → fe v , (v , v)} {b = λ v → fc v , (v , v)} {r = r} {h = h} Iν ek f n)))))
```

## §4 $L_0$ 部分与主定理

```agda
Lp→O : ∀ {c φ χ ℓ₂} {x : P c φ χ} {u} → Lp c hon x u → Rᴾ c c x x → (e : Ev ℓ₂ χ) (z : zero <ᴵ ℓ₂) → Od 0 (ψ̄ᴾ e z x) u
Lp→O lz rz e z = wkO 0 {X = ∅ᴿ} (λ _ → tt) (H→O 0 (proj₂ ∅ᴿ-goodʰ))
Lp→O (ls {ps = ps} {y} {ys} {a = a} cc F Fχ l) (rs s c r) e z = suc0 {ps = ps} {y = y} {ys = ys} {R = ψ̄ᴾ e z a} cc (Lp→O l r e z)
Lp→O (ll {ps = ps} {y} {ys} {F} cc h) (rl h′) e z = limOd 0 {ps = ps} {y = y} {ys = ys} {F = λ n → ψ̄ᴾ e z (F n)} cc (λ n → Lp→O (h n) (h′ n) e z)
Lp→O (li {ps = ps} {y} {ys} {ν} {j = zero} {ac} {f} cc I d hP hI) (ri e′ h′) e z =
  limᵢOᴬ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ᴾ e z (f x)} cc I d
         (λ η x l → Lp→W tt e z (hI η x (l , λ ())))
         (λ η x l xx → Lp→O (hI η x (l , λ ())) (h′ x x xx) e z , R→Rdᴾ (h′ x x xx) e z e z)
Lp→O (li {ps = ps} {y} {ys} {ν} {j = suc j} {ac} {f} cc I d hP hI) (ri e′ h′) e z =
  limᵢOᴾ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ᴾ e z (f x)} refl cc I d (InpO (suc j))
         (proj₁ (inp₀ I d) , Ωˢ-≅ᴬ (≅ᴵ-refl (suc j)) , proj₂ (inp₀ I d))
         (λ o xx → frL₊ refl (proj₁ o) , xx , λ _ → proj₂ o , FHν I d)
         (λ {η} {x} i → Lp→W tt e z (hI η x (proj₁ i , proj₂ (proj₂ i))))
         (λ {η} {x} i → R→Rdᴾ (h′ x x (proj₁ (proj₂ i))) e z e z)
         (λ {η} {x} i → Lp→O (hI η x (proj₁ i , proj₂ (proj₂ i))) (h′ x x (proj₁ (proj₂ i))) e z)
Lp→O (li {ps = ps} {y} {ys} {ν} {j = lim g s} {ac} {f} cc I d hP hI) (ri e′ h′) e z =
  limᵢOᴾ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ᴾ e z (f x)} refl cc I d (InpO (lim g s))
         (proj₁ (inp₀ I d) , Ωˢ-≅ᴬ (≅ᴵ-refl (lim g s)) , proj₂ (inp₀ I d))
         (λ o xx → frL₊ refl (proj₁ o) , xx , λ _ → proj₂ o , FHν I d)
         (λ {η} {x} i → Lp→W tt e z (hI η x (proj₁ i , proj₂ (proj₂ i))))
         (λ {η} {x} i → R→Rdᴾ (h′ x x (proj₁ (proj₂ i))) e z e z)
         (λ {η} {x} i → Lp→O (hI η x (proj₁ i , proj₂ (proj₂ i))) (h′ x x (proj₁ (proj₂ i))) e z)
Lp→O (lĉ {ps = ps} {y} {ys} {o₀ = o₀} {o} cc K h₀ hk) (rĉ d dz dg r h′) e z =
  ĉOd 0 {ps = ps} {y = y} {ys = ys} {O₀ = ψ̄ᴾ e z o₀} {O = λ η d → ψ̄ᴾ e z (o η d)} cc K (Lp→O h₀ r e z)
      (λ k → Lp→O (hk k) (h′ _ _ _ _ (≅ᴵ-refl _)) e z)
Lp→O (lŝ {ps = ps} {y} {ys} {t = t} {g} cc I b o h₀ hg) (rŝ d r h′) e z =
  ŝOd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ᴾ e z t} {G = λ η d → ψ̄ᴾ e z (g η d)} cc I b o (Lp→O h₀ r e z)
      (λ θ Y hY lY nθ lt ee → Lp→O (hg θ Y hY lY nθ lt ee) (h′ _ _ _ _ (≅ᴵ-refl _)) e z)
Lp→O (lclo {ps = ps} {y} {ys} {t} {g} F cc h₀ hg) (rclo s r h′) e z =
  cloOd 0 {ps = ps} {y = y} {ys = ys} {t = ψ̄ᴾ e z t} {g = λ η → ψ̄ᴾ e z (g η)} F cc (Lp→O h₀ r e z)
      (λ θ Y hY lY nθ lt → Lp→O (hg θ Y hY lY nθ lt) (h′ _ _ (≅ᴵ-refl _)) e z)
Lp→O (lcl {χ = χ} {ps = ps} {y} {ys} {t = t} {g} G cc I₀ z₀ o h₀ hg) (rcl s r h′) e z =
  ŝOd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ᴾ e z t} {G = λ η d → ψ̄ᴾ (evη χ B η d) (lim 0 (iF B)) (g η)} cc (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk))) (proj₂ (proj₂ (proj₂ Pk)))
      (Lp→O h₀ r e z)
      (λ θ Y hY lY nθ lt d → Lp→O (hg θ Y hY lY nθ lt) (h′ _ _ (≅ᴵ-refl _)) (evη χ B (toLevel Y hY) d) (lim 0 (iF B)))
  where
  B = bound (χ ⊔ fk zero) e z
  Pk = pickF G I₀ z₀ o B
Lp→O (lwk {le = le} {le′ = le′} {x = x} l) (rwk r) e z = wkO 0 {X = ψ̄ᴾ (le′ e) z x} le (Lp→O l r (le′ e) z)
Lp→O (lΩ↓ {φ = φ} {χ} {ps} {y} {ys} {ν = ν} {fe} {ac} {h} cc Iν ek f) (rΩ↓ e′ s f′) e z =
  LimRow.limμO {ν = ν} {ps} {y} {ys} cc {F = λ n → wk 0 (λ v → v , v) (ψ̄ᴾ e z (h φ (chainᵒ fe (λ y₁ → owk (λ v → fe v , (v , v)) (Ψ e (ac e) (h φ y₁))) n)))}
    (λ n → wkO 0 {X = ψ̄ᴾ e z (h φ (chainᵒ fe (λ y₁ → owk (λ v → fe v , (v , v)) (Ψ e (ac e) (h φ y₁))) n))} (λ v → v , v)
       (Lp→O (f cv-h φ _ _ (chainΨ e {fe = fe} {a = λ v → fe v , (v , v)} ac {h = h} Iν ek f n))
             (f′ φ φ s _ _ (chRΨ e e {fe = fe} {fe′ = fe} {c₁ = λ v → fe v , (v , v)} {c₁′ = λ v → fe v , (v , v)} {ac = ac} {ac′ = ac} {h = h} {h′ = h} e′ s f′ n)) e z))
Lp→O (lΩ {φ = φ} {χ} {ps} {y} {ys} {ν = ν} {fe} {fc} {r} {h} cc Iν ek f) (rΩ e′ s sρ f′) e z =
  LimRow.limμO {ν = μ ν} {ps} {y} {ys} cc {F = λ n → wk 0 (λ v → v , v) (ψ̄ᴾ (e , e) z (h φ χ (intoV (<→◃ r) (chainᵖ fe fc (λ y₁ → pwk (λ v → fe v , (v , v)) (λ v → fc v , (v , v)) (ψᵖ r (h φ χ (intoV (<→◃ r) y₁)))) n))))}
    (λ n → wkO 0 {X = ψ̄ᴾ (e , e) z (h φ χ (intoV (<→◃ r) (chainᵖ fe fc (λ y₁ → pwk (λ v → fe v , (v , v)) (λ v → fc v , (v , v)) (ψᵖ r (h φ χ (intoV (<→◃ r) y₁)))) n)))} (λ v → v , v)
       (Lp→O (f cv-h φ χ _ _ (intoQ (<→◃ r) (chainG {fe = fe} {fc = fc} {a = λ v → fe v , (v , v)} {b = λ v → fc v , (v , v)} {r = r} {h = h} Iν ek f n)))
             (f′ φ φ χ χ s sρ _ _ (intoRᴾ (<→◃ r) (chRG {fe = fe} {fe′ = fe} {fc = fc} {fc′ = fc} {c₁ = λ v → fe v , (v , v)} {c₂ = λ v → fc v , (v , v)} {c₁′ = λ v → fe v , (v , v)} {c₂′ = λ v → fc v , (v , v)} {r = r} {r′ = r} {h = h} {h′ = h} e′ s sρ f′ n))) (e , e) z))

labelᴾ : ∀ {c φ χ ℓ₂} {x : P c φ χ} {u} → Lp c hon x u → Rᴾ c c x x → (e : Ev ℓ₂ χ) (z : zero <ᴵ ℓ₂) → NF₁ (ψ₀ᵗ u) → ∀ {ℓ} (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) → Lab₀ (ψ̄ᴾ e z x ev p) (ψ₀ᵗ u)
labelᴾ l r e z nf ev p = Lp→O l r e z ev p nf
```
