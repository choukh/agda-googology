> **机械改写, 验收用.** 由 [OrdLabPsi](OrdLabPsi.lagda.md) 经 `Survey/scripts/ordlab/mk_b.py` 生成: 只把 `HtS`, `PxS`, `LadderInf*` 换成 `HtB`, `PxB`, `LadderOrd*`. 见 [OrdLab](OrdLab.lagda.md).

# OrdLabBPsi

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
open import OCF.Align.OrdLabBBase
module OCF.Align.OrdLabBPsi (𝕊 : HtB) (𝕏 : PxB 𝕊) where

open PxB 𝕏
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.OrdLabZDecoupleBase using (ΩΩ)
open import OCF.Align.OrdLabZStage2Label using (one⁰)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.OrdLabZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.OrdLabZClosure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.LadderLabZStandardOmega using ()
open import OCF.Align.OrdLabZGoodLBase
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZUniform3Base hiding (_⊕_; Ψ; evη) renaming (FW to FW₀)
open import OCF.Align.OrdLabZUniform3Rel
open import OCF.Align.OrdLabZUniform3SqABase
open import OCF.Align.OrdLabZUniform3Hon
open import OCF.Align.OrdLabZUniform3Depth2Class
open import OCF.Align.OrdLabZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.OrdLabZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.OrdLabZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.OrdLabZUniform5Head
open import OCF.Align.OrdLabZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.OrdLabZUniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.OrdLabZUniform5Class using (Mode; hon; wkm; Fw; FlU; Cv; cv-h; cv-w; Cv-tr; Cv-refl; Fw-cv; FlU-cv; FlM; FlM-cv; FC)
open import OCF.Align.OrdLabZUniform5Close using (FlM→U; FlU-mono; FlU-⊔; FlM-⊔; Fw-⊕; FC-pre)
open import OCF.Align.OrdLabZUniform5Tr using (FC-≅)
open import OCF.Align.OrdLabZUniform5Psi using (FlU→μ; FlM-rep; rep-snoc′; Fw-ψ; FC-rep; Pen-μ; occ-rep)
open import OCF.Align.OrdLabZUniform4Head using (module HeadRules)
open import OCF.Free.Tree using (<◃)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZClosure using (Pen)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.OrdLabBClass 𝕊 𝕏
open RestrQ
open import OCF.Align.OrdLabZUniform5Psi using (I₁)
```

## §1 比较的记号一侧

```agda
FC-Ω : ∀ {t τ u} H (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → FC true t (ψᵗ (P H τ) u ∷ [])
FC-Ω {suc t} H Iτ e ink = inj₂ (_ , Iτ , inj₁ (≺ᴵ-respʳ (via (≅ᴵ-refl t) zero) e) , oτ (P-tail H _))
FC-Ω {lim f s} H Iτ e inb = inj₂ (_ , Iτ , inj₂ e , oτ (P-tail H _))

FlU→P : ∀ {m φ b W} → Occ (natT 1) (ψᵗ W b ∷ []) → FlU m φ b → FlM m (Fl ⊔ φ) (ψᵗ W b ∷ [])
FlU→P {m = hon} oc F (inl (inr ink)) = inj₁ z≅
FlU→P {m = hon} oc F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , oc)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)
FlU→P {m = wkm c} oc F (inl (inr ink)) = inj₁ (inj₁ (inj₁ z≅))
FlU→P {m = wkm c} oc F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (natT 1 , I₁ , inj₂ e , oc)
... | inj₂ (inj₂ (w , Iw , kw , o)) = inj₂ (w , Iw , kw , od o)

Fw-ψP : ∀ {m φ ps y ys W} → cmpᵀ (sucT []) W ≡ lt → cof (y ∷ ys) ≡ cΩ [] → Fw m (φ ⊔ fk zero) ps y ys →
        Fw m ((Fl ⊔ φ) ⊔ fk zero) [] (ψᵗ W (ps ++ (y ∷ ys))) []
Fw-ψP {m = hon} ℓ cc G (inr ink) = inj₁ z≅
Fw-ψP {m = hon} ℓ cc G (inl (inl (inr ink))) = inj₁ z≅
Fw-ψP {m = hon} {ps = ps} {y} {ys} {W} ℓ cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh W {ps} {y} {ys} cc (inj₁ ℓ) θ)) (od (o θ)))
Fw-ψP {m = wkm c} ℓ cc G (inr ink) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψP {m = wkm c} ℓ cc G (inl (inl (inr ink))) = inj₁ (inj₁ (inj₁ z≅))
Fw-ψP {m = wkm c} {ps = ps} {y} {ys} {W} ℓ cc G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (HeadRules.penh W {ps} {y} {ys} cc (inj₁ ℓ) θ)) (od (o θ)))
```

## §2 搬运

```agda
Lq-tr  : ∀ {m t a b mo φ χ} (e : a ≅ᴵ b) {x : Q m a φ χ} {u} → Lq m a t mo x u → Lq m b t mo (trQ e x) u
Lq-tr⁻ : ∀ {m t a b mo φ χ} (e : a ≅ᴵ b) {x : Q m b φ χ} {u} → Lq m b t mo x u → Lq m a t mo (tr⁻Q e x) u
Lq-res : ∀ {m j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {mo ξ ζ} {z : Q m (repQ (resQ q e)) ξ ζ} {θ} → Lq m _ true mo z θ → Lq m j true mo (backQ (resQ q e) z) θ
Lq-res⁻ : ∀ {m j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {mo ξ ζ} {z : Q m (repQ (res⁻Q q e)) ξ ζ} {θ} → Lq m _ true mo z θ → Lq m j true mo (backQ (res⁻Q q e) z) θ

Lq-tr e lz = lz
Lq-tr e (ls cc Fa Fχ Fc l) = ls cc Fa Fχ (FC-≅ e Fc) (Lq-tr e l)
Lq-tr e (ll cc h) = ll cc (λ n → Lq-tr e (h n))
Lq-tr e (li cc I ej hP hI) = li cc I ej (λ η x l s v → Lq-tr e (hP η x l s v)) (λ η x i → Lq-tr e (hI η x i))
Lq-tr e (lĉ cc K h₀′ hk) = lĉ cc K (Lq-tr e h₀′) (λ k → Lq-tr e (hk k))
Lq-tr e (lŝ cc I b o h₀′ hg) = lŝ cc I b o (Lq-tr e h₀′) (λ θ Y hY lY nθ lt d → Lq-tr e (hg θ Y hY lY nθ lt d))
Lq-tr e (lclo Fa cc h₀′ hg) = lclo Fa cc (Lq-tr e h₀′) (λ θ Y hY lY nθ lt → Lq-tr e (hg θ Y hY lY nθ lt))
Lq-tr e (lcl Fa cc I₀ z₀ o h₀′ hg) = lcl Fa cc I₀ z₀ o (Lq-tr e h₀′) (λ θ Y hY lY nθ lt → Lq-tr e (hg θ Y hY lY nθ lt))
Lq-tr e (lwk l) = lwk (Lq-tr e l)
Lq-tr e (lΩ↓ cc I ek f) = lΩ↓ cc I ek (λ v ξ ζ z θ l → Lq-tr e (f v ξ ζ z θ l))
Lq-tr (s≅ e) (lob {r = zero} l x) = lob (Lq-tr e l) (Lq-tr (s≅ e) x)
Lq-tr (l≅ h) (lob {r = self n} l x) = lob (Lq-tr (h n) l) (Lq-tr (l≅ h) x)
Lq-tr {m} {b = b} e (lΩ {ps = ps} {y} {ys} {r = q} {h = h} cc I ek f) =
  lΩ {r = ltQ (resQ q e)} cc I (≅ᴵ-trans (≅ᴵ-sym (eqQ (resQ q e))) ek)
     (λ {mo′} v ξ ζ z θ l → subst (λ w → Lq m b _ mo′ (trQ e (h ξ ζ (intoU (<→◃ q) (backQ (resQ q e) w)))) (ps ++ fsT (y ∷ ys) θ))
                               (sym (out-intoU (<→◃ (ltQ (resQ q e))) z))
                               (Lq-tr e (f v ξ ζ _ θ (intoL (<→◃ q) (Lq-res q e (outL (<→◃ (ltQ (resQ q e))) l))))))

Lq-tr⁻ e lz = lz
Lq-tr⁻ e (ls cc Fa Fχ Fc l) = ls cc Fa Fχ (FC-≅ (≅ᴵ-sym e) Fc) (Lq-tr⁻ e l)
Lq-tr⁻ e (ll cc h) = ll cc (λ n → Lq-tr⁻ e (h n))
Lq-tr⁻ e (li cc I ej hP hI) = li cc I ej (λ η x l s v → Lq-tr⁻ e (hP η x l s v)) (λ η x i → Lq-tr⁻ e (hI η x i))
Lq-tr⁻ e (lĉ cc K h₀′ hk) = lĉ cc K (Lq-tr⁻ e h₀′) (λ k → Lq-tr⁻ e (hk k))
Lq-tr⁻ e (lŝ cc I b o h₀′ hg) = lŝ cc I b o (Lq-tr⁻ e h₀′) (λ θ Y hY lY nθ lt d → Lq-tr⁻ e (hg θ Y hY lY nθ lt d))
Lq-tr⁻ e (lclo Fa cc h₀′ hg) = lclo Fa cc (Lq-tr⁻ e h₀′) (λ θ Y hY lY nθ lt → Lq-tr⁻ e (hg θ Y hY lY nθ lt))
Lq-tr⁻ e (lcl Fa cc I₀ z₀ o h₀′ hg) = lcl Fa cc I₀ z₀ o (Lq-tr⁻ e h₀′) (λ θ Y hY lY nθ lt → Lq-tr⁻ e (hg θ Y hY lY nθ lt))
Lq-tr⁻ e (lwk l) = lwk (Lq-tr⁻ e l)
Lq-tr⁻ e (lΩ↓ cc I ek f) = lΩ↓ cc I ek (λ v ξ ζ z θ l → Lq-tr⁻ e (f v ξ ζ z θ l))
Lq-tr⁻ (s≅ e) (lob {r = zero} l x) = lob (Lq-tr⁻ e l) (Lq-tr⁻ (s≅ e) x)
Lq-tr⁻ (l≅ h) (lob {r = self n} l x) = lob (Lq-tr⁻ (h n) l) (Lq-tr⁻ (l≅ h) x)
Lq-tr⁻ {m} {a = a} e (lΩ {ps = ps} {y} {ys} {r = q} {h = h} cc I ek f) =
  lΩ {r = ltQ (res⁻Q q e)} cc I (≅ᴵ-trans (≅ᴵ-sym (eqQ (res⁻Q q e))) ek)
     (λ {mo′} v ξ ζ z θ l → subst (λ w → Lq m a _ mo′ (tr⁻Q e (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q e) w)))) (ps ++ fsT (y ∷ ys) θ))
                               (sym (out-intoU (<→◃ (ltQ (res⁻Q q e))) z))
                               (Lq-tr⁻ e (f v ξ ζ _ θ (intoL (<→◃ q) (Lq-res⁻ q e (outL (<→◃ (ltQ (res⁻Q q e))) l))))))

Lq-res zero      (s≅ e) l = Lq-tr⁻ e l
Lq-res (suc q)   (s≅ e) l = Lq-res q e l
Lq-res (lim n q) (l≅ h) l = Lq-res q (h n) l

Lq-res⁻ zero      (s≅ e) l = Lq-tr e l
Lq-res⁻ (suc q)   (s≅ e) l = Lq-res⁻ q e l
Lq-res⁻ (lim n q) (l≅ h) l = Lq-res⁻ q (h n) l
```

## §3 字面目标

```agda
Flχ→ν : ∀ {χ b} (τ : T) → FlrLab χ b → FlrLab (Fl ⊔ χ) (ψᵗ τ b ∷ [])
Flχ→ν t F (inl (inr ink)) = inj₁ z≅
Flχ→ν t F (inr k) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , od o)

Flχ-rep : ∀ {χ x} n → FlrLab χ (x ∷ []) → FlrLab χ (replicate (suc n) x)
Flχ-rep n F = FlrLab-mono (occ-rep n) F

Lq-rep : ∀ {m c b mo φ χ} {X̂ : Q m c φ χ} {X} → Lq m c b mo X̂ (X ∷ []) → FlM mo φ (X ∷ []) → (∀ i → i <ᴸ m → FlrLab (χ i) (X ∷ [])) → FC b c (X ∷ []) → ∀ n → Lq m c b mo (repᵠ X̂ n) (replicate n X)
Lq-rep l F Fχ Fc zero = lz
Lq-rep l F Fχ Fc (suc zero) = l
Lq-rep {X = X} l F Fχ Fc (suc (suc n)) = lwk (rq (rep-snoc′ n X) (Lq-⊞ (Lq-rep l F Fχ Fc (suc n)) (FlM-rep n F) (λ i q → Flχ-rep n (Fχ i q)) (FC-rep n Fc) l))

Lq-ψ : ∀ {m c t τ b mo φ χ} (q : t <ᴵ c) (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → {x : Q m c φ χ} {u : T} → Lq m c b mo x u → Lq m t true mo (ψᵠ q x) (ψᵗ (P m τ) u ∷ [])
chainG : ∀ {m c k ν b mo φ χ ξ ps y ys} {fe : ∀ {L} → Ev L ξ → Ev L Fl} {a : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)} (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {mo′} → Cv mo mo′ → ∀ ξ ζ (z : Q m k ξ ζ) θ → LL m c (<→◃ r) mo′ z θ → Lq m c b mo′ (h ξ ζ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) →
         ∀ n → Lq m k true mo (chainᵠ fe fc* (λ z → qwk a (⇑ (cv* m)) (ψᵠ r (h ξ (Z* χ) (intoU (<→◃ r) z)))) n) (γW ps (y ∷ ys) (P m ν) n)

Lq-ψ {m} {τ = τ} {mo = mo} q Iτ et lz = lwk (LqΩ̇ᴵ m Iτ et mo)
Lq-ψ {m} {τ = τ} q Iτ et (ls {ps = ps} {y} {ys} cc F Fχ _ l) =
  ll {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.c1h (P m τ) {ps} {y} {ys} cc)
     (λ n → rq (sym (repW (P m τ) ps y ys cc n)) (Lq-rep (Lq-ψ q Iτ et l) (FlU→P (os (P-occ m τ)) F) (λ i r → Flχ→ν (P m τ) (Fχ i r)) (FC-Ω m Iτ et) n))
Lq-ψ {m} {τ = τ} q Iτ et (ll {ps = ps} {y} {ys} cc hh) =
  ll {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (P m τ) {ps} {y} {ys} cc)
     (λ n → rq (sym (ωW (P m τ) ps y ys cc n)) (Lq-ψ q Iτ et (hh n)))
Lq-ψ {m} {τ = τ} q Iτ et (li {ps = ps} {y} {ys} cc I d hP hI) =
  li {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I))) I d
     (λ η x l s v → rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I)) η)) (Lq-ψ q Iτ et (hP η x l s v)))
     (λ η x i → rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I)) η)) (Lq-ψ q Iτ et (hI η x i)))
Lq-ψ {m} {τ = τ} q Iτ et (lĉ {ps = ps} {y} {ys} cc K h₀′ hk) =
  lĉ {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (P m τ) {ps} {y} {ys} cc) K
     (rq (sym (ωW (P m τ) ps y ys cc 0)) (Lq-ψ q Iτ et h₀′))
     (λ k → rq (sym (ωW (P m τ) ps y ys cc (suc k))) (Lq-ψ q Iτ et (hk k)))
Lq-ψ {m} {τ = τ} q Iτ et (lŝ {ps = ps} {y} {ys} cc I b o h₀′ hg) =
  lŝ {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0))) I b
     (λ θ → subst (Occ _) (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)) θ)) (od (o θ)))
     (rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)) (natT 1))) (Lq-ψ q Iτ et h₀′))
     (λ θ Y hY lY nθ lt d → rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)) θ)) (Lq-ψ q Iτ et (hg θ Y hY lY nθ lt d)))
Lq-ψ {m} {τ = τ} q Iτ et (lclo {ps = ps} {y} {ys} G cc h₀′ hg) =
  lwk (lclo {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (Fw-ψP (P-lt m τ I0) cc G) (HeadRules.cΩh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)))
     (lwk (rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)) (natT 1))) (Lq-ψ q Iτ et h₀′)))
     (λ θ Y hY lY nθ lt → lwk (rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)) θ)) (Lq-ψ q Iτ et (hg θ Y hY lY nθ lt)))))
Lq-ψ {m} {τ = τ} q Iτ et (lcl {ps = ps} {y} {ys} G cc I₀ z₀ o h₀′ hg) =
  lcl {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (Fw-ψP {m = hon} (P-lt m τ I0) cc G) (HeadRules.cΩh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0))) I₀ z₀
     (λ θ → subst (Occ _) (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)) θ)) (od (o θ)))
     (rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)) (natT 1))) (Lq-ψ q Iτ et h₀′))
     (λ θ Y hY lY nθ lt → lwk (rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-lt m τ I0)) θ)) (Lq-ψ q Iτ et (hg θ Y hY lY nθ lt))))
Lq-ψ q Iτ et (lwk l) = lwk (Lq-ψ q Iτ et l)
Lq-ψ q Iτ et (lob l x) = Lq-ψ q Iτ et x
Lq-ψ {m} {τ = τ} q Iτ et (lΩ↓ {ps = ps} {y} {ys} {n} {q = r} cc Iν ek f) =
  lΩ↓ {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} {q = r} (HeadRules.cΩh (P m τ) {ps} {y} {ys} cc (inj₁ (P-cmp-lt τ r Iν))) Iν ek
     (λ v ξ ζ z θ l → lwk (rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc (inj₁ (P-cmp-lt τ r Iν)) θ)) (Lq-ψ q Iτ et (f v ξ ζ z θ l))))
Lq-ψ {m} {t = t} {τ} q Iτ et (lΩ {φ = φ} {χ} {ps} {y} {ys} {k} {ν} {r = r} {h} cc Iν ek f) with <ᴵ-dec r q
... | injᵃ (via e s) =
  let pn = subst Pen (sym (P-cmp≡ m ν τ)) (pen-of Iν ek Iτ et (via e s)) in
  lΩ {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} {r = s} (HeadRules.cΩh (P m τ) {ps} {y} {ys} cc pn) Iν (≅ᴵ-trans (≅ᴵ-sym e) ek)
     (λ {mo′} v ξ ζ z θ l → lwk (rq (sym (HeadRules.penh (P m τ) {ps} {y} {ys} cc pn θ))
        (subst (λ w → Lq m t true mo′ (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e w)))) (ψᵗ (P m τ) (ps ++ fsT (y ∷ ys) θ) ∷ [])) (sym (out-intoU (<→◃ s) z))
               (Lq-ψ q Iτ et (f v ξ ζ _ θ (intoL (<→◃ r) (Lq-tr⁻ e (outL (<→◃ s) l))))))))
... | injᵇ b =
  let g = trans (P-cmp≡ m ν τ) (gt-ofᵇ Iν ek Iτ et b) in
  ll {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (P m τ) {ps} {y} {ys} cc g)
     (λ n → rq (sym (gtW (P m τ) ps y ys (P m ν) cc g n))
               (lwk (Lq-ψ q Iτ et (f (Cv-refl _) (Fl ⊔ φ) (Z* χ) _ _ (intoL (<→◃ r) (chainG {fe = proj₁} {a = dupr2} {r = r} {h = h} Iν ek f n))))))
... | injᶜ c =
  let g = trans (P-cmp≡ m ν τ) (gt-ofᶜ Iν ek Iτ et c) in
  ll {ps = []} {y = ψᵗ (P m τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (P m τ) {ps} {y} {ys} cc g)
     (λ n → rq (sym (gtW (P m τ) ps y ys (P m ν) cc g n))
               (lwk (Lq-ψ q Iτ et (f (Cv-refl _) (Fl ⊔ φ) (Z* χ) _ _ (intoL (<→◃ r) (chainG {fe = proj₁} {a = dupr2} {r = r} {h = h} Iν ek f n))))))

chainG {m} Iν ek f zero = lwk (LqΩ̇ᴵ m Iν ek _)
chainG {mo = mo} {χ = χ} {ξ = ξ} {fe = fe} {a = a} {r = r} {h = h} Iν ek f (suc n) =
  lwk (Lq-ψ r Iν ek (f (Cv-refl mo) ξ (Z* χ) _ _ (intoL (<→◃ r) (chainG {fe = fe} {a = a} {r = r} {h = h} Iν ek f n))))
```

## §4 目标在高度 $H$

```agda
pickG : ∀ {ψ ps y ys i ℓ w₀} {Θ : T → T} → FW₀ (ψ ⊔ fk zero) ps y ys → (∀ {w θ} → Occ w (ps ++ fsT (y ∷ ys) θ) → Occ w (Θ θ)) →
        (I₀ : Idx w₀) → i ≼ lvI I₀ → (∀ θ → Occ w₀ (Θ θ)) → (B : Top i ℓ (ψ ⊔ fk zero)) →
        Σ T λ w′ → Σ (Idx w′) λ Iw′ → (Bd B ⊑ᴵ suc (lvI Iw′)) × (∀ θ → Occ w′ (Θ θ))
pickG {ψ} {ps} {y} {ys} {i} {ℓ} {w₀} {Θ} fw wr I₀ c₀ o B = Pick.pw Pk , Pick.pI Pk ,
    ubd B (≼→≺s (Pick.pc Pk)) (λ k → dem k (pd (Pick.pF Pk k))) , Pick.pP Pk
  where
  pw′ : ∀ {K} → (K ≅ᴵ zero) ⊎ (Σ T λ w₁ → Σ (Idx w₁) λ I₁ → (K ≼ lvI I₁) × Ob w₁ ps y ys) →
        (K ≅ᴵ zero) ⊎ (Σ T λ w₁ → Σ (Idx w₁) λ I₁ → (K ≼ lvI I₁) × (∀ θ → Occ w₁ (Θ θ)))
  pw′ (inj₁ k0) = inj₁ k0
  pw′ (inj₂ (w₁ , I₁′ , kw , ob′)) = inj₂ (w₁ , I₁′ , kw , (λ θ → wr (ob′ θ)))
  Pk : Pick (λ w′ → ∀ θ → Occ w′ (Θ θ)) (ψ ⊔ fk zero) Tr0 i
  Pk = pickMax (ψ ⊔ fk zero) Tr0 (λ k → pw′ (fw k)) I₀ o c₀
  pd : ∀ {K} → (K ≅ᴵ zero) ⊎ (K ≼ lvI (Pick.pI Pk)) → (K ≺ᴵ suc (lvI (Pick.pI Pk))) ⊎ (K ≅ᴵ zero)
  pd (inj₁ k0) = inj₂ k0
  pd (inj₂ kw) = inj₁ (≼→≺s kw)

Lq-Ψ : ∀ {H m α φ χ t τ b mo w} (qH : H <ᴸ m) (ok : Ok w) (e : Eh H m w χ) (p : t <ᴵ w H) (Iτ : Idx τ) → t ≅ᴵ lvI Iτ → {x : Q m α φ χ} {u : T} → Lq m α b mo x u → Lq H t true mo (Ψ qH ok e p x) (ψᵗ (P H τ) u ∷ [])
chainΨ : ∀ {m α k n ν b mo φ χ ξ w ps y ys} {fe : ∀ {L} → Ev L ξ → Ev L Fl} {a : ∀ {L} → Ev L ξ → Ev L (Fl ⊔ (ξ ⊔ φ))} (q : n <ᴸ m) (ok : Ok w) (e* : Eh n m w (lo n (Z* χ) ∪ χ)) (pk : k <ᴵ w n) {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m α (ξ ⊔ φ) (lo n ζ ∪ χ)} (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {mo′} → Cv mo mo′ → ∀ ξ ζ (z : Q n k ξ ζ) θ → LV m q mo′ z θ → Lq m α b mo′ (h ξ ζ (intoV q z)) (ps ++ fsT (y ∷ ys) θ)) →
         ∀ i → Lq n k true mo (chainᵠ fe fc* (λ z → qwk a (⇑ (cv* n)) (Ψ q ok e* pk (h ξ (Z* χ) (intoV q z)))) i) (γW ps (y ∷ ys) (P n ν) i)

Lq-Ψ {H} {τ = τ} {mo = mo} qH ok e p Iτ et lz = lwk (LqΩ̇ᴵ H Iτ et mo)
Lq-Ψ {H} {τ = τ} qH ok e p Iτ et (ls {ps = ps} {y} {ys} cc F Fχ _ l) =
  ll {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.c1h (P H τ) {ps} {y} {ys} cc)
     (λ n → rq (sym (repW (P H τ) ps y ys cc n)) (Lq-rep (Lq-Ψ qH ok e p Iτ et l) (FlU→P (os (P-occ H τ)) F) (λ i r → Flχ→ν (P H τ) (Fχ i (tr< r qH))) (FC-Ω H Iτ et) n))
Lq-Ψ {H} {τ = τ} qH ok e p Iτ et (ll {ps = ps} {y} {ys} cc hh) =
  ll {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (P H τ) {ps} {y} {ys} cc)
     (λ n → rq (sym (ωW (P H τ) ps y ys cc n)) (Lq-Ψ qH ok e p Iτ et (hh n)))
Lq-Ψ {H} {τ = τ} qH ok e p Iτ et (li {ps = ps} {y} {ys} cc I d hP hI) =
  li {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I))) I d
     (λ η x l s v → rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I)) η)) (Lq-Ψ qH ok e p Iτ et (hP η x l s v)))
     (λ η x i → rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I)) η)) (Lq-Ψ qH ok e p Iτ et (hI η x i)))
Lq-Ψ {H} {τ = τ} qH ok e p Iτ et (lĉ {ps = ps} {y} {ys} cc K h₀′ hk) =
  lĉ {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cωh (P H τ) {ps} {y} {ys} cc) K
     (rq (sym (ωW (P H τ) ps y ys cc 0)) (Lq-Ψ qH ok e p Iτ et h₀′))
     (λ k → rq (sym (ωW (P H τ) ps y ys cc (suc k))) (Lq-Ψ qH ok e p Iτ et (hk k)))
Lq-Ψ {H} {τ = τ} qH ok e p Iτ et (lŝ {ps = ps} {y} {ys} cc I b o h₀′ hg) =
  lŝ {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0))) I b
     (λ θ → subst (Occ _) (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (od (o θ)))
     (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) (natT 1))) (Lq-Ψ qH ok e p Iτ et h₀′))
     (λ θ Y hY lY nθ lt d → rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (Lq-Ψ qH ok e p Iτ et (hg θ Y hY lY nθ lt d)))
Lq-Ψ {H} {τ = τ} qH ok e p Iτ et (lclo {ps = ps} {y} {ys} G cc h₀′ hg) =
  lwk (lclo {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (Fw-ψP (P-lt H τ I0) cc G) (HeadRules.cΩh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)))
     (lwk (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) (natT 1))) (Lq-Ψ qH ok e p Iτ et h₀′)))
     (λ θ Y hY lY nθ lt → lwk (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (Lq-Ψ qH ok e p Iτ et (hg θ Y hY lY nθ lt)))))
Lq-Ψ qH ok e p Iτ et (lwk {le′ = le′} l) = lwk (Lq-Ψ qH ok (λ i h r → le′ i r (e i h r)) p Iτ et l)
Lq-Ψ qH ok e p Iτ et (lob l x) = Lq-Ψ qH ok e p Iτ et x
Lq-Ψ {H} {τ = τ} qH ok e p Iτ et (lcl {χ = χ} {ps = ps} {y} {ys} {w₀} {n} {ψ} {q} {s} G cc I₀ z₀ o h₀′ hg) with tri n H
... | tlt l =
  lcl {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} {q = l} (Fw-ψP {m = hon} (P-lt H τ I0) cc G) (HeadRules.cΩh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0))) I₀ z₀
      (λ θ → subst (Occ _) (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (od (o θ)))
      (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) (natT 1))) (Lq-Ψ qH ok e p Iτ et h₀′))
      (λ θ Y hY lY nθ lt → lwk (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (Lq-Ψ qH ok _ p Iτ et (hg θ Y hY lY nθ lt))))
... | teq refl =
  lŝ {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)))
     (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk)))
     (λ θ → subst (Occ _) (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (proj₂ (proj₂ (proj₂ Pk)) θ))
     (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) (natT 1))) (Lq-Ψ qH ok e p Iτ et h₀′))
     (λ θ Y hY lY nθ lt d → lwk (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (Lq-Ψ qH _ _ _ Iτ et (hg θ Y hY lY nθ lt))))
  where
  B = bound (ψ ⊔ fk zero) (s (e n (inj₁ refl) q)) p
  Pk = pickG {Θ = λ θ → ψᵗ (P H τ) (ps ++ fsT (y ∷ ys) θ) ∷ []} G od Iτ (inj₂ et) (λ θ → oτ (P-tail H τ)) B
... | tgt l =
  lŝ {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cΩh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)))
     (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk)))
     (λ θ → subst (Occ _) (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (proj₂ (proj₂ (proj₂ Pk)) θ))
     (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) (natT 1))) (Lq-Ψ qH ok e p Iτ et h₀′))
     (λ θ Y hY lY nθ lt d → lwk (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-lt H τ I0)) θ)) (Lq-Ψ qH _ _ _ Iτ et (hg θ Y hY lY nθ lt))))
  where
  B = bound (ψ ⊔ fk zero) (s (e n (inj₂ l) q)) (zr ok n)
  Pk = pickG {Θ = λ θ → ψᵗ (P H τ) (ps ++ fsT (y ∷ ys) θ) ∷ []} G od I₀ z₀ (λ θ → od (o θ)) B
Lq-Ψ {H} {t = t} {τ = τ} {mo = mo} qH ok e p Iτ et (lΩ↓ {φ = φ} {χ} {ps} {y} {ys} {n} {k} {ν} {q} {fe} {ac} {h = h′} cc Iν ek f) with tri n H
... | tlt l =
  lΩ↓ {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} {q = l} (HeadRules.cΩh (P H τ) {ps} {y} {ys} cc (inj₁ (P-cmp-lt τ l Iν))) Iν ek
      (λ {mo′} v ξ ζ z θ lz → lwk (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc (inj₁ (P-cmp-lt τ l Iν)) θ))
         (subst (λ w → Lq H t true mo′ (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h′ ξ ζ (intoV q w))) (ψᵗ (P H τ) (ps ++ fsT (y ∷ ys) θ) ∷ [])) (sym (out-intoV l z))
                (Lq-Ψ qH ok (e-lo ζ (inj₂ l) e) p Iτ et (f v ξ ζ z θ (intoLV q (outLV l lz)))))))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p
...   | injᵃ (via d s) =
  let pn = subst Pen (sym (P-cmp≡ H ν τ)) (pen-of Iν ek Iτ et (via d s)) in
  lΩ {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} {r = s} (HeadRules.cΩh (P H τ) {ps} {y} {ys} cc pn) Iν (≅ᴵ-trans (≅ᴵ-sym d) ek)
     (λ {mo′} v ξ ζ z θ l → lwk (rq (sym (HeadRules.penh (P H τ) {ps} {y} {ys} cc pn θ))
        (subst (λ w → Lq H t true mo′ (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h′ ξ ζ (intoV q (tr⁻Q d w)))) (ψᵗ (P H τ) (ps ++ fsT (y ∷ ys) θ) ∷ [])) (sym (out-intoU (<→◃ s) z))
               (Lq-Ψ qH ok (e-lo ζ (inj₁ refl) e) p Iτ et (f v ξ ζ _ θ (intoLV q (Lq-tr⁻ d (outL (<→◃ s) l))))))))
...   | injᵇ b =
  let g = trans (P-cmp≡ H ν τ) (gt-ofᵇ Iν ek Iτ et b) in
  ll {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (P H τ) {ps} {y} {ys} cc g)
     (λ i → rq (sym (gtW (P H τ) ps y ys (P H ν) cc g i))
               (lwk (Lq-Ψ qH ok (e⁺ H ok e) p Iτ et (f (Cv-refl _) (Fl ⊔ φ) (Z* χ) _ _ (intoLV q (chainΨ {fe = proj₁} {a = dupr2} q ok (e⁺ H ok e) (ac (e n (inj₁ refl) q)) {h = h′} Iν ek f i))))))
...   | injᶜ c =
  let g = trans (P-cmp≡ H ν τ) (gt-ofᶜ Iν ek Iτ et c) in
  ll {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (P H τ) {ps} {y} {ys} cc g)
     (λ i → rq (sym (gtW (P H τ) ps y ys (P H ν) cc g i))
               (lwk (Lq-Ψ qH ok (e⁺ H ok e) p Iτ et (f (Cv-refl _) (Fl ⊔ φ) (Z* χ) _ _ (intoLV q (chainΨ {fe = proj₁} {a = dupr2} q ok (e⁺ H ok e) (ac (e n (inj₁ refl) q)) {h = h′} Iν ek f i))))))
Lq-Ψ {H} {τ = τ} qH ok e p Iτ et (lΩ↓ {φ = φ} {χ} {ps} {y} {ys} {n} {k} {ν} {q} {fe} {ac} {h = h′} cc Iν ek f) | tgt l =
  ll {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (P H τ) {ps} {y} {ys} cc (P-cmp-gt ν l Iτ))
     (λ i → rq (sym (gtW (P H τ) ps y ys (P n ν) cc (P-cmp-gt ν l Iτ) i))
               (lwk (Lq-Ψ qH ok (e⁺ n ok e) p Iτ et (f (Cv-refl _) (Fl ⊔ φ) (Z* χ) _ _ (intoLV q (chainΨ {fe = proj₁} {a = dupr2} q ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q)) {h = h′} Iν ek f i))))))
Lq-Ψ {H} {m} {τ = τ} qH ok e p Iτ et (lΩ {φ = φ} {χ} {ps} {y} {ys} {k} {ν} {r = r} {h = h′} cc Iν ek f) =
  ll {ps = []} {y = ψᵗ (P H τ) (ps ++ (y ∷ ys))} {ys = []} (HeadRules.cgth (P H τ) {ps} {y} {ys} cc (P-cmp-gt ν qH Iτ))
     (λ i → rq (sym (gtW (P H τ) ps y ys (P m ν) cc (P-cmp-gt ν qH Iτ) i))
               (lwk (Lq-Ψ qH ok (e⁺ m ok e) p Iτ et (f (Cv-refl _) (Fl ⊔ φ) (Z* χ) _ _ (intoL (<→◃ r) (chainG {fe = proj₁} {a = dupr2} {r = r} {h = h′} Iν ek f i))))))

chainΨ {n = n} q ok e* pk₀ Iν ek f zero = lwk (LqΩ̇ᴵ n Iν ek _)
chainΨ {mo = mo} {χ = χ} {ξ = ξ} {fe = fe} {a = a} q ok e* pk₀ {h = h} Iν ek f (suc i) =
  lwk (Lq-Ψ q ok e* pk₀ Iν ek (f (Cv-refl mo) ξ (Z* χ) _ _ (intoLV q (chainΨ {fe = fe} {a = a} q ok e* pk₀ {h = h} Iν ek f i))))
```
