> **机械克隆.** 由 `Uniform5Eval` 经脚本复制, 只为把 `NF₁`, `Occ` 换成 [ScafLadderZStandardOmega](ScafLadderZStandardOmega.lagda.md), [ScafLadderZSystemOmega](ScafLadderZSystemOmega.lagda.md) 的版本; 见 [ScafLadder](ScafLadder.lagda.md). 下面的文字是原文.

# 统一形 (五): 从标签类到树的标签

> 接 [Uniform5Psi](Uniform5Psi.lagda.md), [Uniform5RelPsi](Uniform5RelPsi.lagda.md), [Uniform4Eval](Uniform4Eval.lagda.md). `Ld→W`, `Ld→O`, `label` 与 Uniform4Eval 逐行相同; 行引理全是 Uniform3Depth2Class 的深度 0 实例. `LimRow` 对 $\Omega+\nu$ 一致 (`gtμ` 换成 `Idx` 版). `lΩ`/`rΩ` 的反演不再需要 `≡-irrelevant`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderZUniform5Eval where

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
open import OCF.Align.ScafLadderZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
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
open import OCF.Align.ScafLadderZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.ScafLadderZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.ScafLadderZUniform5Head
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.ScafLadderZUniform4Two
open import OCF.Align.ScafLadderZUniform5Class
open import OCF.Align.ScafLadderZUniform5Close
open import OCF.Align.ScafLadderZUniform5Tail
open import OCF.Align.ScafLadderZUniform5Tr
open import OCF.Align.ScafLadderZUniform5Psi
open import OCF.Align.ScafLadderZUniform5Rel
open import OCF.Align.ScafLadderZUniform5RelPsi
open import OCF.Align.ScafLadderZUniform3SqA using (LW0→LW)
open GRᴬ
```

## §1 $\Omega+k$ 层的极限行

```agda
module LimRow {ν : T} {ps : T} {y : PT} {ys : T} (cc : cof (y ∷ ys) ≡ cΩ (μ ν)) where
  limμW : ∀ {c′ φ} {F : ℕ → Run φ} → (∀ n → LWʰ[ c′ ] (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (μ ν) n))) → LWʰ[ c′ ] (limA 0 F) (ps ++ (y ∷ ys))
  limμW {F = F} h {w = w} ev p Iw ei ki u =
    gl (trans (cofW w ps y ys) (trans (cong (E.cofA w) cc) (cong (E.cofψ₊ w (μ ν)) (gtμ ν Iw))))
       (λ n → subst (LabL₊ _ Ll _) (sym (gtW w ps y ys (μ ν) cc (gtμ ν Iw) n)) (proj₁ (h n ev p Iw ei ki u))) ,
    hl (NB-sum ps) (λ n → subst (Hn _) (sym (gtW w ps y ys (μ ν) cc (gtμ ν Iw) n)) (proj₂ (h n ev p Iw ei ki u)))

  limμO : ∀ {φ} {F : ℕ → Run φ} → (∀ n → L0 (F n) (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (μ ν) n))) → L0 (limA 0 F) (ps ++ (y ∷ ys))
  limμO {F = F} h ev p nu =
    let cω′ = trans (cofW [] ps y ys) (cong (E.cofA []) cc) in
    let Rn = λ n → h n ev p (subst NF₁ (gtW [] ps y ys (μ ν) cc refl n) (NF₁-fsn nu cω′ n)) in
    limᴸ nu cω′ (λ n → proj₁ (Rn n)) (λ n → subst (Lab _) (sym (gtW [] ps y ys (μ ν) cc refl n)) (proj₂ (Rn n)))

chainR : ∀ {c k ν b m φ ps y ys} {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : k <ᴵ c} {h : ∀ ξ → Us k (<→◃ r) ξ → O c (ξ ⊔ φ)} (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {m′} → Cv m m′ → ∀ ξ (z : O k ξ) θ → LL c (<→◃ r) m′ z θ → Ld c b m′ (h ξ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) →
         ∀ n → Ld k true m (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n) (γW ps (y ∷ ys) (μ ν) n)
chainR Iν ek f zero = lwk (LdΩ̇ᴵ Iν ek _)
chainR {m = m} {φ = φ} {fe = fe} {r = r} {h = h} Iν ek f (suc n) =
  lwk (Ld-ψ r Iν ek (f (Cv-refl m) φ _ _ (intoL (<→◃ r) (chainR {fe = fe} {r = r} {h = h} Iν ek f n))))
```

## §2 求值的 $W$ 部分

```agda
OkW : Mode → Ordᴵ → Set
OkW hon     c = ⊤
OkW (wkm i) c = Up i c

Cv-of : ∀ {m c i} → OkW m c → Up c i → Cv m (wkm i)
Cv-of {m = hon} ok u = cv-h
Cv-of {m = wkm i} ok u = cv-w (≼-trans ok u)

Fw→[] : ∀ {m c φ ps y ys} → OkW m c → Fw m φ ps y ys → FW[ c ] φ ps y ys
Fw→[] {m = hon} ok F = FW→FW[] F
Fw→[] {m = wkm i} ok F = Fw-cv (cv-w ok) F

inp₀ : ∀ {ν j} (I : Idx ν) → j ≅ᴵ lvI I → InpW j (Ωt ν) (Ωˢ j)
inp₀ I e = LabL-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) e , λ _ → hΩ refl I e , FHν I e

Ld→W : ∀ {c′ c b m φ} {x : O c′ φ} {u} → OkW m c → Ld c′ b m x u → Wd c 0 (ψ̄ x) u
Ld→W ok lz = wkW 0 _ (G→W 0 ∅ᴿ-goodʰ)
Ld→W ok (lob l x) = Ld→W ok x
Ld→W ok (ls {ps = ps} {y} {ys} {a = a} cc F _ l) = sucWʰ {ps = ps} {y = y} {ys = ys} {R = ψ̄ a} cc (Ld→W ok l)
Ld→W ok (ll {ps = ps} {y} {ys} {F} cc h) = limWd 0 {ps = ps} {y = y} {ys = ys} {F = λ n → ψ̄ (F n)} cc (λ n → Ld→W ok (h n))
Ld→W {c = c} {m = m} ok (li {ps = ps} {y} {ys} {ν} {j} {ac} {f} cc I e hP hI) =
  limᵢWd 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ (f x)} cc I e (InpW j) (inp₀ I e)
         (λ kj o → frL₊ kj (proj₁ o) , λ _ → proj₂ o , FHν I e)
         (λ η x l {i} s ui → Ld→W {m = wkm i} (≼-refl i) (hP η x l s (Cv-of ok ui)))
         (λ {η} {x} ix → Ld→W ok (hI η x ix))
Ld→W ok (lĉ {ps = ps} {y} {ys} {o₀ = o₀} {o} cc K h₀ hk) =
  ĉWd 0 {ps = ps} {y = y} {ys = ys} {O₀ = ψ̄ o₀} {O = λ η e → ψ̄ (o η e)} cc K (Ld→W ok h₀) (λ k → Ld→W ok (hk k))
Ld→W ok (lŝ {ps = ps} {y} {ys} {t = t} {g} cc I b ob h₀ hg) =
  ŝWd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ t} {G = λ η e → ψ̄ (g η e)} cc I b ob (Ld→W ok h₀) (λ θ Y hY lY nθ lt e → Ld→W ok (hg θ Y hY lY nθ lt e))
Ld→W ok (lclo {ps = ps} {y} {ys} {t} {g} F cc h₀ hg) =
  cloWd 0 {ps = ps} {y = y} {ys = ys} {t = ψ̄ t} {g = λ η → ψ̄ (g η)} (Fw→[] ok F) cc (Ld→W ok h₀) (λ θ Y hY lY nθ lt → Ld→W ok (hg θ Y hY lY nθ lt))
Ld→W ok (lwk {le = le} l) = wkW 0 le (Ld→W ok l)
Ld→W {m = m} ok (lΩ {φ = φ} {ps} {y} {ys} {ν = ν} {fe} {r} {h} cc Iν ek f) =
  LimRow.limμW {ν = ν} {ps} {y} {ys} cc {F = λ n → wk 0 (λ v → v , v) (ψ̄ (h φ (intoU (<→◃ r) (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n))))}
    (λ n → wkW 0 (λ v → v , v) (Ld→W ok (f (Cv-refl m) φ _ _ (intoL (<→◃ r) (chainR {fe = fe} {r = r} {h = h} Iν ek f n)))))
```

## §3 求值的 $L_0$ 部分与主定理

```agda
Ld→O : ∀ {c b φ} {x : O c φ} {u} → Ld c b hon x u → Rᵒ c c x x → Od 0 (ψ̄ x) u
Ld→O lz rz = wkO 0 {X = ∅ᴿ} (λ e → tt) (H→O 0 (proj₂ ∅ᴿ-goodʰ))
Ld→O (lob l x) (rob _ _ r) = Ld→O x r
Ld→O (ls {ps = ps} {y} {ys} {a = a} cc F _ l) (rs s r) = suc0 {ps = ps} {y = y} {ys = ys} {R = ψ̄ a} cc (Ld→O l r)
Ld→O (ll {ps = ps} {y} {ys} {F} cc h) (rl h′) = limOd 0 {ps = ps} {y = y} {ys = ys} {F = λ n → ψ̄ (F n)} cc (λ n → Ld→O (h n) (h′ n))
Ld→O (li {ps = ps} {y} {ys} {ν} {j = zero} {ac} {f} cc I e hP hI) (ri e′ h′) =
  limᵢOᴬ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ (f x)} cc I e
         (λ η x l → Ld→W tt (hI η x (l , λ ())))
         (λ η x l xx → Ld→O (hI η x (l , λ ())) (h′ x x xx) , R→Rd (h′ x x xx))
Ld→O (li {ps = ps} {y} {ys} {ν} {j = suc j} {ac} {f} cc I e hP hI) (ri e′ h′) =
  limᵢOᴾ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ (f x)} refl cc I e (InpO (suc j))
         (proj₁ (inp₀ I e) , Ωˢ-≅ᴬ (≅ᴵ-refl (suc j)) , proj₂ (inp₀ I e))
         (λ o xx → frL₊ refl (proj₁ o) , xx , λ _ → proj₂ o , FHν I e)
         (λ {η} {x} i → Ld→W tt (hI η x (proj₁ i , proj₂ (proj₂ i))))
         (λ {η} {x} i → R→Rd (h′ x x (proj₁ (proj₂ i))))
         (λ {η} {x} i → Ld→O (hI η x (proj₁ i , proj₂ (proj₂ i))) (h′ x x (proj₁ (proj₂ i))))
Ld→O (li {ps = ps} {y} {ys} {ν} {j = lim g s} {ac} {f} cc I e hP hI) (ri e′ h′) =
  limᵢOᴾ 0 {ps = ps} {y = y} {ys = ys} {ac = ac} {H = λ x → ψ̄ (f x)} refl cc I e (InpO (lim g s))
         (proj₁ (inp₀ I e) , Ωˢ-≅ᴬ (≅ᴵ-refl (lim g s)) , proj₂ (inp₀ I e))
         (λ o xx → frL₊ refl (proj₁ o) , xx , λ _ → proj₂ o , FHν I e)
         (λ {η} {x} i → Ld→W tt (hI η x (proj₁ i , proj₂ (proj₂ i))))
         (λ {η} {x} i → R→Rd (h′ x x (proj₁ (proj₂ i))))
         (λ {η} {x} i → Ld→O (hI η x (proj₁ i , proj₂ (proj₂ i))) (h′ x x (proj₁ (proj₂ i))))
Ld→O (lĉ {ps = ps} {y} {ys} {o₀ = o₀} {o} cc K h₀ hk) (rĉ e dz dg r h′) =
  ĉOd 0 {ps = ps} {y = y} {ys = ys} {O₀ = ψ̄ o₀} {O = λ η e → ψ̄ (o η e)} cc K (Ld→O h₀ r)
      (λ k → Ld→O (hk k) (h′ _ _ _ _ (≅ᴵ-refl _)))
Ld→O (lŝ {ps = ps} {y} {ys} {t = t} {g} cc I b ob h₀ hg) (rŝ e r h′) =
  ŝOd 0 {ps = ps} {y = y} {ys = ys} {T₀ = ψ̄ t} {G = λ η e → ψ̄ (g η e)} cc I b ob (Ld→O h₀ r)
      (λ θ Y hY lY nθ lt ee → Ld→O (hg θ Y hY lY nθ lt ee) (h′ _ _ _ _ (≅ᴵ-refl _)))
Ld→O (lclo {ps = ps} {y} {ys} {t} {g} F cc h₀ hg) (rclo s r h′) =
  cloOd 0 {ps = ps} {y = y} {ys = ys} {t = ψ̄ t} {g = λ η → ψ̄ (g η)} F cc (Ld→O h₀ r)
      (λ θ Y hY lY nθ lt → Ld→O (hg θ Y hY lY nθ lt) (h′ _ _ (≅ᴵ-refl _)))
Ld→O (lwk {le = le} {x = x} l) (rwk r) = wkO 0 {X = ψ̄ x} le (Ld→O l r)
Ld→O (lΩ {φ = φ} {ps} {y} {ys} {ν = ν} {fe} {r} {h} cc Iν ek f) (rΩ e′ s f′) =
  LimRow.limμO {ν = ν} {ps} {y} {ys} cc {F = λ n → wk 0 (λ v → v , v) (ψ̄ (h φ (intoU (<→◃ r) (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n))))}
    (λ n → wkO 0 {X = ψ̄ (h φ (intoU (<→◃ r) (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n)))} (λ v → v , v)
       (Ld→O (f cv-h φ _ _ (intoL (<→◃ r) (chainR {fe = fe} {r = r} {h = h} Iν ek f n)))
             (f′ φ φ s _ _ (intoR (<→◃ r) (chRE {fe = fe} {fe′ = fe} {r = r} {r′ = r} {h = h} {h′ = h} e′ s f′ n)))))

Ld→H : ∀ {c b φ} {x : O c φ} {u} → Ld c b hon x u → Rᵒ c c x x → Hd 0 (ψ̄ x) u
Ld→H l r = grᴬ (LW0→LW (LWʰ→ w)) (Ld→O l r) (R→Rd r) , w
  where
  w = Ld→W {c = zero} tt l

label : ∀ {c b φ} {x : O c φ} {u} → Ld c b hon x u → Rᵒ c c x x → NF₁ (ψ₀ᵗ u) → ∀ {ℓ} (ev : Ev ℓ φ) (z : zero <ᴵ ℓ) → Lab₀ (ψ̄ x ev z) (ψ₀ᵗ u)
label l r nf ev z = Ld→O l r ev z nf
```
