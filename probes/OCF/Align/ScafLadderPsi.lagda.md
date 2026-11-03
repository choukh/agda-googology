# 阶梯 (四): 折叠保持标签

> 结论写在 [ScafLadder](ScafLadder.lagda.md). `Lp-ψᵖ`: 目标在高度 2 (与 `Ld-ψ` 同形). `Ld-Ψ`: 目标在高度 1, **输出是已有的 `Ld`**, 闭包落成 `lŝ`, 界由 `pickΨ` 给: 目标 $\tau$ 经 `oτ` 出现 (这是 `Occ` 的新构造子), 其余地板项来自 `lcl` 的字段.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderPsi where

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
open import OCF.Align.ScafLadderZUniform5Rel
open import OCF.Align.ScafLadderZUniform5RelPsi
open import OCF.Align.ScafLadderZUniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.ScafLadderTree
open import OCF.Align.ScafLadderClass
open import OCF.Align.ScafLadderZSystemOmega using (th; ts)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.ScafLadderZUniform4Head using (module HeadRules)
open import OCF.Align.ScafLadderZUniform5Tr using (Ld-tr⁻)
open RestrP
```

## §1 搬运

```agda
Lp-tr  : ∀ {a b m φ χ} (e : a ≅ᴵ b) {x : P a φ χ} {u} → Lp a m x u → Lp b m (trP e x) u
Lp-tr⁻ : ∀ {a b m φ χ} (e : a ≅ᴵ b) {x : P b φ χ} {u} → Lp b m x u → Lp a m (tr⁻P e x) u
Lp-res : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {m ξ ζ} {z : P (repP (resP q e)) ξ ζ} {θ} → Lp _ m z θ → Lp j m (backP (resP q e) z) θ
Lp-res⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {m ξ ζ} {z : P (repP (res⁻P q e)) ξ ζ} {θ} → Lp _ m z θ → Lp j m (backP (res⁻P q e) z) θ

Lp-tr e lz = lz
Lp-tr e (ls cc F Fχ l) = ls cc F Fχ (Lp-tr e l)
Lp-tr e (ll cc h) = ll cc (λ n → Lp-tr e (h n))
Lp-tr e (li cc I ej hP hI) = li cc I ej (λ η x l s v → Lp-tr e (hP η x l s v)) (λ η x i → Lp-tr e (hI η x i))
Lp-tr e (lĉ cc K h₀ hk) = lĉ cc K (Lp-tr e h₀) (λ k → Lp-tr e (hk k))
Lp-tr e (lŝ cc I b o h₀ hg) = lŝ cc I b o (Lp-tr e h₀) (λ θ Y hY lY nθ lt d → Lp-tr e (hg θ Y hY lY nθ lt d))
Lp-tr e (lclo F cc h₀ hg) = lclo F cc (Lp-tr e h₀) (λ θ Y hY lY nθ lt → Lp-tr e (hg θ Y hY lY nθ lt))
Lp-tr e (lcl F cc I₀ z₀ o h₀ hg) = lcl F cc I₀ z₀ o (Lp-tr e h₀) (λ θ Y hY lY nθ lt → Lp-tr e (hg θ Y hY lY nθ lt))
Lp-tr e (lwk l) = lwk (Lp-tr e l)
Lp-tr e (lΩ↓ cc I ek f) = lΩ↓ cc I ek (λ v ξ z θ l → Lp-tr e (f v ξ z θ l))
Lp-tr {b = b} e (lΩ {ps = ps} {y} {ys} {r = q} {h = h} cc I ek f) =
  lΩ {r = ltP (resP q e)} cc I (≅ᴵ-trans (≅ᴵ-sym (eqP (resP q e))) ek)
     (λ {m′} v ξ ζ z θ l → subst (λ w → Lp b m′ (trP e (h ξ ζ (intoV (<→◃ q) (backP (resP q e) w)))) (ps ++ fsT (y ∷ ys) θ))
                               (sym (out-intoV (<→◃ (ltP (resP q e))) z))
                               (Lp-tr e (f v ξ ζ _ θ (intoQ (<→◃ q) (Lp-res q e (outQ (<→◃ (ltP (resP q e))) l))))))

Lp-tr⁻ e lz = lz
Lp-tr⁻ e (ls cc F Fχ l) = ls cc F Fχ (Lp-tr⁻ e l)
Lp-tr⁻ e (ll cc h) = ll cc (λ n → Lp-tr⁻ e (h n))
Lp-tr⁻ e (li cc I ej hP hI) = li cc I ej (λ η x l s v → Lp-tr⁻ e (hP η x l s v)) (λ η x i → Lp-tr⁻ e (hI η x i))
Lp-tr⁻ e (lĉ cc K h₀ hk) = lĉ cc K (Lp-tr⁻ e h₀) (λ k → Lp-tr⁻ e (hk k))
Lp-tr⁻ e (lŝ cc I b o h₀ hg) = lŝ cc I b o (Lp-tr⁻ e h₀) (λ θ Y hY lY nθ lt d → Lp-tr⁻ e (hg θ Y hY lY nθ lt d))
Lp-tr⁻ e (lclo F cc h₀ hg) = lclo F cc (Lp-tr⁻ e h₀) (λ θ Y hY lY nθ lt → Lp-tr⁻ e (hg θ Y hY lY nθ lt))
Lp-tr⁻ e (lcl F cc I₀ z₀ o h₀ hg) = lcl F cc I₀ z₀ o (Lp-tr⁻ e h₀) (λ θ Y hY lY nθ lt → Lp-tr⁻ e (hg θ Y hY lY nθ lt))
Lp-tr⁻ e (lwk l) = lwk (Lp-tr⁻ e l)
Lp-tr⁻ e (lΩ↓ cc I ek f) = lΩ↓ cc I ek (λ v ξ z θ l → Lp-tr⁻ e (f v ξ z θ l))
Lp-tr⁻ {a = a} e (lΩ {ps = ps} {y} {ys} {r = q} {h = h} cc I ek f) =
  lΩ {r = ltP (res⁻P q e)} cc I (≅ᴵ-trans (≅ᴵ-sym (eqP (res⁻P q e))) ek)
     (λ {m′} v ξ ζ z θ l → subst (λ w → Lp a m′ (tr⁻P e (h ξ ζ (intoV (<→◃ q) (backP (res⁻P q e) w)))) (ps ++ fsT (y ∷ ys) θ))
                               (sym (out-intoV (<→◃ (ltP (res⁻P q e))) z))
                               (Lp-tr⁻ e (f v ξ ζ _ θ (intoQ (<→◃ q) (Lp-res⁻ q e (outQ (<→◃ (ltP (res⁻P q e))) l))))))

Lp-res zero      (s≅ e) l = Lp-tr⁻ e l
Lp-res (suc q)   (s≅ e) l = Lp-res q e l
Lp-res (lim n q) (l≅ h) l = Lp-res q (h n) l

Lp-res⁻ zero      (s≅ e) l = Lp-tr e l
Lp-res⁻ (suc q)   (s≅ e) l = Lp-res⁻ q e l
Lp-res⁻ (lim n q) (l≅ h) l = Lp-res⁻ q (h n) l
```

## §2 目标在高度 2

```agda
Flχ→ν : ∀ {χ b} (τ : T) → FlrLab χ b → FlrLab (Fl ⊔ χ) (ψᵗ τ b ∷ [])
Flχ→ν t F (inl (inr ink)) = inj₁ z≅
Flχ→ν t F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , od o)

Flχ-rep : ∀ {χ x} n → FlrLab χ (x ∷ []) → FlrLab χ (replicate (suc n) x)
Flχ-rep n F = FlrLab-mono (occ-rep n) F

Lp-rep : ∀ {c m φ χ} {X̂ : P c φ χ} {X} → Lp c m X̂ (X ∷ []) → FlM m φ (X ∷ []) → FlrLab χ (X ∷ []) → ∀ n → Lp c m (repᵖ X̂ n) (replicate n X)
Lp-rep l F Fχ zero = lz
Lp-rep l F Fχ (suc zero) = l
Lp-rep {X = X} l F Fχ (suc (suc n)) = lwk (rp (rep-snoc′ n X) (Lp-⊞ (Lp-rep l F Fχ (suc n)) (FlM-rep n F) (Flχ-rep n Fχ) l))

Lp-ψᵖ : ∀ {c t τ m φ χ} (q : t <ᴵ c) (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → {x : P c φ χ} {u : T} → Lp c m x u → Lp t m (ψᵖ q x) (ψᵗ (μ (μ τ)) u ∷ [])
chainG : ∀ {c k ν m φ χ ξ ζ ps y ys} {fe : ∀ {L} → Ev L ξ → Ev L Fl} {fc : ∀ {L} → Ev L ζ → Ev L Fl} {a : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {b : ∀ {L} → Ev L ζ → Ev L (Fl ⊔ (ζ ⊔ χ))} {r : k <ᴵ c} {h : ∀ ξ ζ → Vs k (<→◃ r) ξ ζ → P c (ξ ⊔ φ) (ζ ⊔ χ)} (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {m′} → Cv m m′ → ∀ ξ ζ (z : P k ξ ζ) θ → Lq c (<→◃ r) m′ z θ → Lp c m′ (h ξ ζ (intoV (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) →
         ∀ n → Lp k m (chainᵖ fe fc (λ z → pwk a b (ψᵖ r (h ξ ζ (intoV (<→◃ r) z)))) n) (γW ps (y ∷ ys) (μ (μ ν)) n)

Lp-ψᵖ {τ = τ} {m} q Iτ et lz = lwk (LpΩ̇ᴵ Iτ et m)
Lp-ψᵖ {τ = τ} q Iτ et (ls {ps = ps} {y} {ys} cc F Fχ l) =
  ll {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.c1h (μ (μ τ)) {ps} {y} {ys} cc)
     (λ n → rp (sym (repW (μ (μ τ)) ps y ys cc n)) (Lp-rep (Lp-ψᵖ q Iτ et l) (FlU→μ (μ τ) F) (Flχ→ν (μ (μ τ)) Fχ) n))
Lp-ψᵖ {τ = τ} q Iτ et (ll {ps = ps} {y} {ys} cc h) =
  ll {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (μ (μ τ)) {ps} {y} {ys} cc)
     (λ n → rp (sym (ωW (μ (μ τ)) ps y ys cc n)) (Lp-ψᵖ q Iτ et (h n)))
Lp-ψᵖ {τ = τ} q Iτ et (li {ps = ps} {y} {ys} cc I e hP hI) =
  li {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I))) I e
     (λ η x l s v → rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I)) η)) (Lp-ψᵖ q Iτ et (hP η x l s v)))
     (λ η x i → rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I)) η)) (Lp-ψᵖ q Iτ et (hI η x i)))
Lp-ψᵖ {τ = τ} q Iτ et (lĉ {ps = ps} {y} {ys} cc K h₀ hk) =
  lĉ {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (μ (μ τ)) {ps} {y} {ys} cc) K
     (rp (sym (ωW (μ (μ τ)) ps y ys cc 0)) (Lp-ψᵖ q Iτ et h₀))
     (λ k → rp (sym (ωW (μ (μ τ)) ps y ys cc (suc k))) (Lp-ψᵖ q Iτ et (hk k)))
Lp-ψᵖ {τ = τ} q Iτ et (lŝ {ps = ps} {y} {ys} cc I b o h₀ hg) =
  lŝ {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0))) I b
     (λ θ → subst (Occ _) (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)) θ)) (od (o θ)))
     (rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)) (natT 1))) (Lp-ψᵖ q Iτ et h₀))
     (λ θ Y hY lY nθ lt e → rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)) θ)) (Lp-ψᵖ q Iτ et (hg θ Y hY lY nθ lt e)))
Lp-ψᵖ {τ = τ} q Iτ et (lclo {ps = ps} {y} {ys} G cc h₀ hg) =
  lwk (lclo {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (Fw-ψ (μ τ) cc G) (HeadRules.cΩh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)))
     (lwk (rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)) (natT 1))) (Lp-ψᵖ q Iτ et h₀)))
     (λ θ Y hY lY nθ lt → lwk (rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)) θ)) (Lp-ψᵖ q Iτ et (hg θ Y hY lY nθ lt)))))
Lp-ψᵖ {τ = τ} q Iτ et (lcl {ps = ps} {y} {ys} G cc I₀ z₀ o h₀ hg) =
  lwk (lcl {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (Fw-ψ {m = hon} (μ τ) cc G) (HeadRules.cΩh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0))) I₀ z₀
     (λ θ → subst (Occ _) (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)) θ)) (od (o θ)))
     (lwk (rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)) (natT 1))) (Lp-ψᵖ q Iτ et h₀)))
     (λ θ Y hY lY nθ lt → lwk (rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ (μ τ) I0)) θ)) (Lp-ψᵖ q Iτ et (hg θ Y hY lY nθ lt)))))
Lp-ψᵖ q Iτ et (lwk l) = lwk (Lp-ψᵖ q Iτ et l)
Lp-ψᵖ {τ = τ} q Iτ et (lΩ↓ {ps = ps} {y} {ys} cc Iν ek f) =
  lΩ↓ {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ τ Iν))) Iν ek
     (λ v ξ z θ l → lwk (rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc (inj₁ (ltμ τ Iν)) θ)) (Lp-ψᵖ q Iτ et (f v ξ z θ l))))
Lp-ψᵖ {t = t} {τ} q Iτ et (lΩ {φ = φ} {χ} {ps} {y} {ys} {k} {ν} {r = r} {h} cc Iν ek f) with <ᴵ-dec r q
... | injᵃ (via e s) =
  let pn = pen-of Iν ek Iτ et (via e s) in
  lΩ {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} {r = s} (HeadRules.cΩh (μ (μ τ)) {ps} {y} {ys} cc pn) Iν (≅ᴵ-trans (≅ᴵ-sym e) ek)
     (λ {m′} v ξ ζ z θ l → lwk (rp (sym (HeadRules.penh (μ (μ τ)) {ps} {y} {ys} cc pn θ))
        (subst (λ w → Lp t m′ (ψᵖ q (h ξ ζ (intoV (<→◃ r) (tr⁻P e w)))) (ψᵗ (μ (μ τ)) (ps ++ fsT (y ∷ ys) θ) ∷ [])) (sym (out-intoV (<→◃ s) z))
               (Lp-ψᵖ q Iτ et (f v ξ ζ _ θ (intoQ (<→◃ r) (Lp-tr⁻ e (outQ (<→◃ s) l))))))))
... | injᵇ b =
  let g = gt-ofᵇ Iν ek Iτ et b in
  ll {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (μ (μ τ)) {ps} {y} {ys} cc g)
     (λ n → rp (sym (gtW (μ (μ τ)) ps y ys (μ (μ ν)) cc g n))
               (lwk (Lp-ψᵖ q Iτ et (f (Cv-refl _) (Fl ⊔ φ) (Fl ⊔ χ) _ _ (intoQ (<→◃ r) (chainG {fe = proj₁} {fc = proj₁} {a = dupr2} {b = dupr2} {r = r} {h = h} Iν ek f n))))))
... | injᶜ c =
  let g = gt-ofᶜ Iν ek Iτ et c in
  ll {ps = []} {y = ψᵗ (μ (μ τ)) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (μ (μ τ)) {ps} {y} {ys} cc g)
     (λ n → rp (sym (gtW (μ (μ τ)) ps y ys (μ (μ ν)) cc g n))
               (lwk (Lp-ψᵖ q Iτ et (f (Cv-refl _) (Fl ⊔ φ) (Fl ⊔ χ) _ _ (intoQ (<→◃ r) (chainG {fe = proj₁} {fc = proj₁} {a = dupr2} {b = dupr2} {r = r} {h = h} Iν ek f n))))))

chainG Iν ek f zero = lwk (LpΩ̇ᴵ Iν ek _)
chainG {m = m} {ξ = ξ} {ζ = ζ} {fe = fe} {fc = fc} {a = a} {b = b} {r = r} {h = h} Iν ek f (suc n) =
  lwk (Lp-ψᵖ r Iν ek (f (Cv-refl m) ξ ζ _ _ (intoQ (<→◃ r) (chainG {fe = fe} {fc = fc} {a = a} {b = b} {r = r} {h = h} Iν ek f n))))
```

## §3 目标在高度 1: 输出是已有的 `Ld`

```agda
pickΨ : ∀ {χ ps y ys t ℓ τ} → FW₀ (χ ⊔ fk zero) ps y ys → (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → (B : Top t ℓ (χ ⊔ fk zero)) →
        Σ T λ w′ → Σ (Idx w′) λ Iw′ → (Bd B ⊑ᴵ suc (lvI Iw′)) × (∀ θ → Occ w′ (ψᵗ (μ τ) (ps ++ fsT (y ∷ ys) θ) ∷ []))
pickΨ {χ} {ps} {y} {ys} {t} {ℓ} {τ} fw Iτ et B = Pick.pw Pk , Pick.pI Pk ,
    ubd B (≼→≺s (≼-trans (inj₂ et) (Pick.pc Pk))) (λ k → dem k (pd (Pick.pF Pk k))) , Pick.pP Pk
  where
  pw′ : ∀ {K} → (K ≅ᴵ zero) ⊎ (Σ T λ w₁ → Σ (Idx w₁) λ I₁ → (K ≼ lvI I₁) × Ob w₁ ps y ys) →
        (K ≅ᴵ zero) ⊎ (Σ T λ w₁ → Σ (Idx w₁) λ I₁ → (K ≼ lvI I₁) × (∀ θ → Occ w₁ (ψᵗ (μ τ) (ps ++ fsT (y ∷ ys) θ) ∷ [])))
  pw′ (inj₁ k0) = inj₁ k0
  pw′ (inj₂ (w₁ , I₁′ , kw , ob′)) = inj₂ (w₁ , I₁′ , kw , (λ θ → od (ob′ θ)))
  Pk : Pick (λ w′ → ∀ θ → Occ w′ (ψᵗ (μ τ) (ps ++ fsT (y ∷ ys) θ) ∷ [])) (χ ⊔ fk zero) Tr0 (lvI Iτ)
  Pk = pickMax (χ ⊔ fk zero) Tr0 (λ k → pw′ (fw k)) Iτ (λ θ → oτ th) (inj₂ (≅ᴵ-refl _))
  pd : ∀ {K} → (K ≅ᴵ zero) ⊎ (K ≼ lvI (Pick.pI Pk)) → (K ≺ᴵ suc (lvI (Pick.pI Pk))) ⊎ (K ≅ᴵ zero)
  pd (inj₁ k0) = inj₂ k0
  pd (inj₂ kw) = inj₁ (≼→≺s kw)

Ld-Ψ : ∀ {c t τ m φ χ ℓ} (e : Ev ℓ χ) (p : t <ᴵ ℓ) (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → {x : P c φ χ} {u : T} → Lp c m x u → Ld t true m (Ψ e p x) (ψᵗ (μ τ) u ∷ [])
chainΨ : ∀ {c k ν m φ χ ξ ℓ ps y ys} (e : Ev ℓ χ) {fe : ∀ {L} → Ev L ξ → Ev L Fl} {a : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} (ac : ∀ {L} → Ev L χ → k <ᴵ L) {h : ∀ ξ → O k ξ → P c (ξ ⊔ φ) χ} (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → Ld k true m′ z θ → Lp c m′ (h ξ z) (ps ++ fsT (y ∷ ys) θ)) →
         ∀ n → Ld k true m (chainᵒ fe (λ z → owk a (Ψ e (ac e) (h ξ z))) n) (γW ps (y ∷ ys) (μ ν) n)

Ld-Ψ {τ = τ} {m} e p Iτ et lz = lwk (LdΩ̇ᴵ Iτ et m)
Ld-Ψ {τ = τ} e p Iτ et (ls {ps = ps} {y} {ys} cc F Fχ l) =
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.c1h (μ τ) {ps} {y} {ys} cc)
     (λ n → re (sym (repW (μ τ) ps y ys cc n)) (Ld-rep (Ld-Ψ e p Iτ et l) (FlU→μ τ F) (FC-τ Iτ et) n))
Ld-Ψ {τ = τ} e p Iτ et (ll {ps = ps} {y} {ys} cc h) =
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (μ τ) {ps} {y} {ys} cc)
     (λ n → re (sym (ωW (μ τ) ps y ys cc n)) (Ld-Ψ e p Iτ et (h n)))
Ld-Ψ {τ = τ} e p Iτ et (li {ps = ps} {y} {ys} cc I d hP hI) =
  li {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I))) I d
     (λ η x l s v → re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I)) η)) (Ld-Ψ e p Iτ et (hP η x l s v)))
     (λ η x i → re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I)) η)) (Ld-Ψ e p Iτ et (hI η x i)))
Ld-Ψ {τ = τ} e p Iτ et (lĉ {ps = ps} {y} {ys} cc K h₀ hk) =
  lĉ {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (μ τ) {ps} {y} {ys} cc) K
     (re (sym (ωW (μ τ) ps y ys cc 0)) (Ld-Ψ e p Iτ et h₀))
     (λ k → re (sym (ωW (μ τ) ps y ys cc (suc k))) (Ld-Ψ e p Iτ et (hk k)))
Ld-Ψ {τ = τ} e p Iτ et (lŝ {ps = ps} {y} {ys} cc I b o h₀ hg) =
  lŝ {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0))) I b
     (λ θ → subst (Occ _) (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (od (o θ)))
     (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) (natT 1))) (Ld-Ψ e p Iτ et h₀))
     (λ θ Y hY lY nθ lt d → re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (Ld-Ψ e p Iτ et (hg θ Y hY lY nθ lt d)))
Ld-Ψ {τ = τ} e p Iτ et (lclo {ps = ps} {y} {ys} G cc h₀ hg) =
  lwk (lclo {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (Fw-ψ τ cc G) (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)))
     (lwk (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) (natT 1))) (Ld-Ψ e p Iτ et h₀)))
     (λ θ Y hY lY nθ lt → lwk (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (Ld-Ψ e p Iτ et (hg θ Y hY lY nθ lt)))))
Ld-Ψ {τ = τ} e p Iτ et (lcl {χ = χ} {ps = ps} {y} {ys} G cc I₀ z₀ o h₀ hg) =
  lŝ {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)))
     (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk)))
     (λ θ → subst (Occ _) (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (proj₂ (proj₂ (proj₂ Pk)) θ))
     (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) (natT 1))) (Ld-Ψ e p Iτ et h₀))
     (λ θ Y hY lY nθ lt d → re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ))
        (Ld-Ψ (evη χ B (toLevel Y hY) d) (lim 0 (iF B)) Iτ et (hg θ Y hY lY nθ lt)))
  where
  B = bound (χ ⊔ fk zero) e p
  Pk = pickΨ G Iτ et B
Ld-Ψ e p Iτ et (lwk {le′ = le′} l) = lwk (Ld-Ψ (le′ e) p Iτ et l)
Ld-Ψ {t = t} {τ} e p Iτ et (lΩ↓ {φ = φ} {χ} {ps} {y} {ys} {k} {ν} {ac = ac} {h} cc Iν ek f) with <ᴵ-dec (ac e) p
... | injᵃ (via d s) =
  let pn = pen-of Iν ek Iτ et (via d s) in
  lΩ {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} {r = s} (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (Pen-μ pn)) Iν (≅ᴵ-trans (≅ᴵ-sym d) ek)
     (λ {m′} v ξ z θ l → lwk (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (Pen-μ pn) θ))
        (subst (λ w → Ld t true m′ (Ψ e p (h ξ (tr⁻O d w))) (ψᵗ (μ τ) (ps ++ fsT (y ∷ ys) θ) ∷ [])) (sym (out-intoU (<→◃ s) z))
               (Ld-Ψ e p Iτ et (f v ξ _ θ (Ld-tr⁻ d (outL (<→◃ s) l)))))))
... | injᵇ b =
  let g = gt-ofᵇ Iν ek Iτ et b in
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (μ τ) {ps} {y} {ys} cc g)
     (λ n → re (sym (gtW (μ τ) ps y ys (μ ν) cc g n))
               (lwk (Ld-Ψ e p Iτ et (f (Cv-refl _) (Fl ⊔ φ) _ _ (chainΨ e {fe = proj₁} {a = dupr2} ac {h = h} Iν ek f n)))))
... | injᶜ c =
  let g = gt-ofᶜ Iν ek Iτ et c in
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (μ τ) {ps} {y} {ys} cc g)
     (λ n → re (sym (gtW (μ τ) ps y ys (μ ν) cc g n))
               (lwk (Ld-Ψ e p Iτ et (f (Cv-refl _) (Fl ⊔ φ) _ _ (chainΨ e {fe = proj₁} {a = dupr2} ac {h = h} Iν ek f n)))))
Ld-Ψ {τ = τ} e p Iτ et (lΩ {φ = φ} {χ} {ps} {y} {ys} {k} {ν} {fc = fc} {r = r} {h} cc Iν ek f) =
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (μ τ) {ps} {y} {ys} cc (gtμ ν Iτ))
     (λ n → re (sym (gtW (μ τ) ps y ys (μ (μ ν)) cc (gtμ ν Iτ) n))
               (lwk (Ld-Ψ (e , e) p Iτ et (f (Cv-refl _) (Fl ⊔ φ) χ _ _ (intoQ (<→◃ r) (chainG {fe = proj₁} {fc = fc} {a = dupr2} {b = λ u → fc u , (u , u)} {r = r} {h = h} Iν ek f n))))))

chainΨ e ac Iν ek f zero = lwk (LdΩ̇ᴵ Iν ek _)
chainΨ {m = m} {ξ = ξ} e {fe = fe} {a = a} ac {h = h} Iν ek f (suc n) =
  lwk (Ld-Ψ e (ac e) Iν ek (f (Cv-refl m) ξ _ _ (chainΨ e {fe = fe} {a = a} ac {h = h} Iν ek f n)))
```
