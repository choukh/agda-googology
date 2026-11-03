> **机械克隆.** 由 `Uniform5Psi` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (五): $\psi_{\Omega+\tau}$ 的标签定理

> 接 [Uniform5Tr](Uniform5Tr.lagda.md), [Uniform5Head](Uniform5Head.lagda.md), [Uniform4Psi](Uniform4Psi.lagda.md). **`Ld-ψ q Iτ et : Ld c m x u → Ld t m (ψᵒ q x) (ψ_{Ω+τ}(u))`, 对一切 $t<^\mathsf I c$, `Iτ : Idx τ`, $t\cong$ `lvI Iτ`.** 与 Uniform4Psi 的差别只在 `lΩ` 一行: `cmp<` 的两种结果换成 `<ᴵ-dec` 的三种结果, 由 `pen-of`/`gt-ofᵇ`/`gt-ofᶜ` 对上 `cmpᵀ`; 穿透分支多一步 `Ld-tr⁻`. 链点的目标是节点自带的 `(Iν, ek)`. 不需要 `pickMax`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform5Psi where

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
open import OCF.Align.ScafLadderZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.ScafLadderZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.ScafLadderZDecoupleBase using (ΩΩ)
open import OCF.Align.ScafLadderZStage2Label using (one⁰)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW)
open import OCF.Align.Closure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.ScafLadderZStandardOmega using ()
open import OCF.Align.ScafLadderZGoodLBase
open import OCF.Align.ScafLadderZUniformS
open import OCF.Align.ScafLadderZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.ScafLadderZUniform3Rel
open import OCF.Align.ScafLadderZUniform3SqABase
open import OCF.Align.ScafLadderZUniform3Hon
open import OCF.Align.ScafLadderZUniform3Depth2Class
open import OCF.Align.ScafLadderZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.ScafLadderZUniform3Depth2Fold using (Zc₀; Zc₀-of)
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.ScafLadderZUniform5Head
open import OCF.Align.ScafLadderZUniform4Head using (module HeadRules)
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.ScafLadderZUniform4Two
open import OCF.Align.ScafLadderZUniform5Class
open import OCF.Align.ScafLadderZUniform5Close
open import OCF.Align.ScafLadderZUniform5Tail
open import OCF.Align.ScafLadderZUniform5Tr
```

## §1 重复

```agda
I₁ : Idx (natT 1)
I₁ = one⁰ , hs hz , lab1 , nf1

FlU→μ : ∀ {m φ b} (τ : T) → FlU m φ b → FlM m (Fl ⊔ φ) (ψᵗ (μ τ) b ∷ [])
FlU→μ {m = hon} t F (inl (inr ink)) = inj₁ z≅
FlU→μ {m = hon} t F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , os oh)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)
FlU→μ {m = wkm c} t F (inl (inr ink)) = inj₁ (inj₁ (inj₁ z≅))
FlU→μ {m = wkm c} t F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , os oh)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)

occ-rep : ∀ {w x} n → Occ w (x ∷ []) → Occ w (replicate (suc n) x)
occ-rep n oh = oh
occ-rep n (od o) = od o
occ-rep n (os o) = os o
occ-rep n (oτ t) = oτ t
occ-rep n (ot ())

FlM-rep : ∀ {m φ x} n → FlM m φ (x ∷ []) → FlM m φ (replicate (suc n) x)
FlM-rep {m = hon} n F = FlrLab-mono (occ-rep n) F
FlM-rep {m = wkm c} n F = FlrLab[]-mono (occ-rep n) F

rep-snoc′ : ∀ n (x : PT) → replicate (suc n) x ++ (x ∷ []) ≡ replicate (suc (suc n)) x
rep-snoc′ zero x = refl
rep-snoc′ (suc n) x = cong (x ∷_) (rep-snoc′ n x)

Pen-μ : ∀ {ν τ : T} → CPen (cmpᵀ (sucT ν) τ) → CPen (cmpᵀ (sucT (μ ν)) (μ τ))
Pen-μ p = p

FC-rep : ∀ {b c x} n → FC b c (x ∷ []) → FC b c (replicate (suc n) x)
FC-rep {b = false} n F = tt
FC-rep {b = true}  n F = FlrLab-mono (occ-rep n) F

FC-τ : ∀ {t τ u} (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → FC true t (ψᵗ (μ τ) u ∷ [])
FC-τ {suc t} Iτ e ink = inj₂ (_ , Iτ , inj₁ (≺ᴵ-respʳ (via (≅ᴵ-refl t) zero) e) , oτ th)
FC-τ {lim f s} Iτ e inb = inj₂ (_ , Iτ , inj₂ e , oτ th)

Ld-rep : ∀ {c b m φ} {X̂ : O c φ} {X} → Ld c b m X̂ (X ∷ []) → FlM m φ (X ∷ []) → FC b c (X ∷ []) → ∀ n → Ld c b m (repᵒ X̂ n) (replicate n X)
Ld-rep l F Fc zero = lz
Ld-rep l F Fc (suc zero) = l
Ld-rep {X = X} l F Fc (suc (suc n)) = lwk (re (rep-snoc′ n X) (Ld-⊕ (Ld-rep l F Fc (suc n)) (FlM-rep n F) (FC-rep n Fc) l))
```

## §2 主定理

```agda
Fw-ψ : ∀ {m φ ps y ys} (τ : T) → cof (y ∷ ys) ≡ cΩ [] → Fw m (φ ⊔ fk zero) ps y ys →
       Fw m ((Fl ⊔ φ) ⊔ fk zero) [] (ψᵗ (μ τ) (ps ++ (y ∷ ys))) []
Fw-ψ {m = hon} τ cc G (inr ink) = inj₁ z≅
Fw-ψ {m = hon} τ cc G (inl (inl (inr ink))) = inj₁ z≅
Fw-ψ {m = hon} {ps = ps} {y} {ys} τ cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (od (o θ)))
Fw-ψ {m = wkm c} τ cc G (inr ink) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψ {m = wkm c} τ cc G (inl (inl (inr ink))) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψ {m = wkm c} {ps = ps} {y} {ys} τ cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (od (o θ)))


Ld-ψ : ∀ {c t τ b m φ} (q : t <ᴵ c) (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → {x : O c φ} {u : T} → Ld c b m x u → Ld t true m (ψᵒ q x) (ψᵗ (μ τ) u ∷ [])
chainL : ∀ {c k ν b m φ ps y ys} {r : k <ᴵ c} {h : ∀ ξ → Us k (<→◃ r) ξ → O c (ξ ⊔ φ)} (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → LL c (<→◃ r) m′ z θ → Ld c b m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) →
         ∀ n → Ld k true m (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n) (γW ps (y ∷ ys) (μ ν) n)

Ld-ψ {t = t} {τ} {m = m} q Iτ et lz = lwk (LdΩ̇ᴵ Iτ et m)
Ld-ψ {τ = τ} q Iτ et (ls {ps = ps} {y} {ys} cc F _ l) =
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.c1h (μ τ) {ps} {y} {ys} cc)
     (λ n → re (sym (repW (μ τ) ps y ys cc n)) (Ld-rep (Ld-ψ q Iτ et l) (FlU→μ τ F) (FC-τ Iτ et) n))
Ld-ψ {τ = τ} q Iτ et (ll {ps = ps} {y} {ys} cc h) =
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (μ τ) {ps} {y} {ys} cc)
     (λ n → re (sym (ωW (μ τ) ps y ys cc n)) (Ld-ψ q Iτ et (h n)))
Ld-ψ {τ = τ} q Iτ et (li {ps = ps} {y} {ys} cc I e hP hI) =
  li {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I))) I e
     (λ η x l s v → re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I)) η)) (Ld-ψ q Iτ et (hP η x l s v)))
     (λ η x i → re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I)) η)) (Ld-ψ q Iτ et (hI η x i)))
Ld-ψ {τ = τ} q Iτ et (lĉ {ps = ps} {y} {ys} cc K h₀ hk) =
  lĉ {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (μ τ) {ps} {y} {ys} cc) K
     (re (sym (ωW (μ τ) ps y ys cc 0)) (Ld-ψ q Iτ et h₀))
     (λ k → re (sym (ωW (μ τ) ps y ys cc (suc k))) (Ld-ψ q Iτ et (hk k)))
Ld-ψ {τ = τ} q Iτ et (lŝ {ps = ps} {y} {ys} cc I b ob h₀ hg) =
  lŝ {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0))) I b
     (λ θ → subst (Occ _) (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (od (ob θ)))
     (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) (natT 1))) (Ld-ψ q Iτ et h₀))
     (λ θ Y hY lY nθ lt e → re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (Ld-ψ q Iτ et (hg θ Y hY lY nθ lt e)))
Ld-ψ {τ = τ} q Iτ et (lclo {ps = ps} {y} {ys} G cc h₀ hg) =
  lwk (lclo {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (Fw-ψ τ cc G) (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)))
     (lwk (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) (natT 1))) (Ld-ψ q Iτ et h₀)))
     (λ θ Y hY lY nθ lt → lwk (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (inj₁ (ltμ τ I0)) θ)) (Ld-ψ q Iτ et (hg θ Y hY lY nθ lt)))))
Ld-ψ q Iτ et (lwk l) = lwk (Ld-ψ q Iτ et l)
Ld-ψ q Iτ et (lob l x) = Ld-ψ q Iτ et x
Ld-ψ {t = t} {τ} q Iτ et (lΩ {φ = φ} {ps} {y} {ys} {k} {ν} {r = r} {h} cc Iν ek f) with <ᴵ-dec r q
... | injᵃ (via e s) =
  let pn = pen-of Iν ek Iτ et (via e s) in
  lΩ {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} {r = s} (HeadRules.cΩh (μ τ) {ps} {y} {ys} cc (Pen-μ pn)) Iν (≅ᴵ-trans (≅ᴵ-sym e) ek)
     (λ {m′} v ξ z θ l → lwk (re (sym (HeadRules.penh (μ τ) {ps} {y} {ys} cc (Pen-μ pn) θ))
        (subst (λ w → Ld t true m′ (ψᵒ q (h ξ (intoU (<→◃ r) (tr⁻O e w)))) (ψᵗ (μ τ) (ps ++ fsT (y ∷ ys) θ) ∷ [])) (sym (out-intoU (<→◃ s) z))
               (Ld-ψ q Iτ et (f v ξ _ θ (intoL (<→◃ r) (Ld-tr⁻ e (outL (<→◃ s) l))))))))
... | injᵇ b =
  let g = gt-ofᵇ Iν ek Iτ et b in
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (μ τ) {ps} {y} {ys} cc g)
     (λ n → re (sym (gtW (μ τ) ps y ys (μ ν) cc g n))
               (lwk (Ld-ψ q Iτ et (f (Cv-refl _) (Fl ⊔ φ) _ _ (intoL (<→◃ r) (chainL {r = r} {h = h} Iν ek f n))))))
... | injᶜ c =
  let g = gt-ofᶜ Iν ek Iτ et c in
  ll {ps = []} {y = ψᵗ (μ τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (μ τ) {ps} {y} {ys} cc g)
     (λ n → re (sym (gtW (μ τ) ps y ys (μ ν) cc g n))
               (lwk (Ld-ψ q Iτ et (f (Cv-refl _) (Fl ⊔ φ) _ _ (intoL (<→◃ r) (chainL {r = r} {h = h} Iν ek f n))))))

chainL Iν ek f zero = lwk (LdΩ̇ᴵ Iν ek _)
chainL {m = m} {φ = φ} {r = r} {h = h} Iν ek f (suc n) =
  lwk (Ld-ψ r Iν ek (f (Cv-refl m) (Fl ⊔ φ) _ _ (intoL (<→◃ r) (chainL {r = r} {h = h} Iν ek f n))))
```
