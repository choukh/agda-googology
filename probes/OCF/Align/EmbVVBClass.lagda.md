> **机械改写, 验收用.** 由 `OrdLabBClass` 经 `Survey/scripts/embvv/mk_world.py`: 第 0 行多一种去头的链行. 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
import OCF.Align.EmbVVMode
open import OCF.Align.EmbVVBBase
module OCF.Align.EmbVVBClass (𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) (𝕏 : PxB 𝕊 dr) where

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
open import OCF.Align.EmbVVOZPrefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.EmbVVOZDecouple using (Idx; lvI; Lab0[])
open import OCF.Align.EmbVVOZDecoupleBase using (ΩΩ)
open import OCF.Align.EmbVVOZStage2Label using (one⁰)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.EmbVVOZOmegaExpBase using (OccΣ; cofΣ; predΣ; πw; repW; ωW; γW; gtW; cofW)
open import OCF.Align.OrdLabZClosure using (cmpᵀ-refl) renaming (Pen to CPen)
open import OCF.Align.EmbVVLZStandardOmega using ()
open import OCF.Align.EmbVVOZGoodLBase
open import OCF.Align.EmbVVOZUniformS
open import OCF.Align.EmbVVOZUniform3Base hiding (_⊕_; Ψ; evη) renaming (FW to FW₀)
open import OCF.Align.EmbVVOZUniform3Rel
open import OCF.Align.EmbVVOZUniform3SqABase
open import OCF.Align.EmbVVOZUniform3Hon
open import OCF.Align.EmbVVOZUniform3Depth2Class
open import OCF.Align.EmbVVOZUniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Align.EmbVVOZUniform3Depth2Fold using (Zc₀; Zc₀-of; InpO)
open import OCF.Align.EmbVVOZUniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr; ∅ᴿ-goodʰ)
open import OCF.Align.EmbVVOZUniform5Head
open import OCF.Align.EmbVVOZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Align.EmbVVOZUniform3SqA using (LW0→LW)
open GRᴬ
open import OCF.Align.EmbVVOZUniform5Class using (Mode; hon; wkm; Fw; FlU; Cv; cv-h; cv-w; Cv-tr; Cv-refl; Fw-cv; FlU-cv; FlM; FlM-cv; FC)
open import OCF.Align.EmbVVOZUniform5Close using (FlM→U; FlU-mono; FlU-⊔; FlM-⊔; Fw-⊕; FC-pre)
open import OCF.Align.EmbVVTree 𝕊 dr
open import OCF.Free.Tree using (<◃)
open import OCF.Align.OrdLabZCorrespond using (fsT-c1)
open import OCF.Align.EmbVVLZStandardOmega using (n[])
```

## §0 记号: 叶子 $\Omega_u$ 的共尾度与基本列

```agda
cofΩt-c1 : ∀ u → cof u ≡ c1 → cof (Ωt u) ≡ cΩ (pred u)
cofΩt-c1 (w ∷ ws) e = cong (E.cofψ0 (w ∷ ws)) e

cofΩt-ω : ∀ u → cof u ≡ cω → cof (Ωt u) ≡ cω
cofΩt-ω (w ∷ ws) e = cong (E.cofψ0 (w ∷ ws)) e

cofΩt-Ω : ∀ u → cof u ≡ cΩ [] → cof (Ωt u) ≡ cΩ []
cofΩt-Ω (w ∷ ws) e = cong (E.cofψ0 (w ∷ ws)) e

fsn-Ωt : ∀ u → cof u ≡ cω → ∀ n → fsn (Ωt u) n ≡ Ωt (fsn u n)
fsn-Ωt (w ∷ ws) e n = E.fsn0-eq w ws n e

fsT-Ωt1 : ∀ u → cof u ≡ c1 → ∀ θ → fsT (Ωt u) θ ≡ θ
fsT-Ωt1 (w ∷ ws) e θ = fsT-c1 (w ∷ ws) _ e θ

fsT0-cΩ : ∀ u c θ → c ≡ cΩ [] → E.fsT0 u c θ ≡ ψᵗ (fsT u θ) [] ∷ []
fsT0-cΩ u .(cΩ []) θ refl = refl

fsT-ΩtΩ : ∀ u → cof u ≡ cΩ [] → ∀ θ → fsT (Ωt u) θ ≡ Ωt (fsT u θ)
fsT-ΩtΩ (w ∷ ws) e θ = fsT0-cΩ (w ∷ ws) _ θ e
```

## §1 `Lq`

```agda
module _ (m : Ht) (c : Ordᴵ) (L : ∀ {k} → k ◃ c → Mode → ∀ {ξ ζ} → Q m k ξ ζ → T → Set)
         (Lv : ∀ {n} → n <ᴸ m → Mode → ∀ {k ξ ζ} → Q n k ξ ζ → T → Set) where
  data Lq₊ : Bool → Mode → ∀ {φ χ} → Q m c φ χ → T → Set where
    lz : ∀ {b mo φ χ} → Lq₊ b mo {φ} {χ} q0 []
    ls : ∀ {b mo φ χ ps y ys} {a : Q m c φ χ} → cof (y ∷ ys) ≡ c1 → FlU mo φ (ps ++ pred (y ∷ ys)) → (∀ i → i <ᴸ m → FlrLab (χ i) (ps ++ pred (y ∷ ys))) → FC b c (ps ++ pred (y ∷ ys)) → Lq₊ b mo a (ps ++ pred (y ∷ ys)) → Lq₊ b mo (qs a) (ps ++ (y ∷ ys))
    ll : ∀ {b mo φ χ ps y ys} {F : ℕ → Q m c φ χ} → cof (y ∷ ys) ≡ cω → (∀ n → Lq₊ b mo (F n) (ps ++ fsn (y ∷ ys) n)) → Lq₊ b mo (ql F) (ps ++ (y ∷ ys))
    li : ∀ {b mo φ χ ps y ys ν j} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {f : Ordˢ j → Q m c φ χ} → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → ∀ {i} → j ≺ᴵ i → Cv mo (wkm i) → Lq₊ b (wkm i) (f x) (ps ++ fsT (y ∷ ys) η)) →
         (∀ η x → InpW j η x → Lq₊ b mo (f x) (ps ++ fsT (y ∷ ys) η)) → Lq₊ b mo (qi ac f) (ps ++ (y ∷ ys))
    lĉ : ∀ {b mo φ χ ps y ys c₀ z} {zg : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {o₀ : Q m c φ χ} {o : (η : Ordᴵ) → c₀ ⊑ᴵ η → Q m c φ χ} → cof (y ∷ ys) ≡ cω →
         (K : CCᴸ c₀ z zg) → Lq₊ b mo o₀ (ps ++ fsn (y ∷ ys) 0) →
         (∀ k → Lq₊ b mo (o (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) → Lq₊ b mo (qĉ c₀ z zg o₀ o) (ps ++ (y ∷ ys))
    lŝ : ∀ {b mo φ χ ps y ys c₀ w′} {t : Q m c φ χ} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Q m c φ χ} → cof (y ∷ ys) ≡ cΩ [] → (Iw′ : Idx w′) → c₀ ⊑ᴵ suc (lvI Iw′) → Ob w′ ps y ys →
         Lq₊ b mo t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → Lq₊ b mo (g (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
         Lq₊ b mo (qŝ c₀ t g) (ps ++ (y ∷ ys))
    lclo : ∀ {b mo φ χ ps y ys} {t : Q m c (φ ⊔ fk zero) χ} {g : (η : Ordᴵ) → Q m c (φ ⊔ fk η) χ} → Fw mo (φ ⊔ fk zero) ps y ys → cof (y ∷ ys) ≡ cΩ [] →
         Lq₊ b mo t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → Lq₊ b mo (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         Lq₊ b mo (qclo t g) (ps ++ (y ∷ ys))
    lcl : ∀ {b mo φ χ ps y ys w₀ n ψ} {q : n <ᴸ m} {s : ∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (ψ ⊔ fk zero)} {t : Q m c φ χ} {g : (η : Ordᴵ) → Q m c φ (upd χ n (ψ ⊔ fk η))} →
         FW₀ (ψ ⊔ fk zero) ps y ys → cof (y ∷ ys) ≡ cΩ [] →
         (I₀ : Idx w₀) → zero ≼ lvI I₀ → Ob w₀ ps y ys →
         Lq₊ b mo t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵗ θ → Lq₊ b mo (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         Lq₊ b mo (qcl q ψ s t g) (ps ++ (y ∷ ys))
    lwk : ∀ {b mo φ φ′ χ χ′ u} {le : ∀ {L} → Ev L φ′ → Ev L φ} {le′ : Sub m χ′ χ} {x : Q m c φ χ} → Lq₊ b mo x u → Lq₊ b mo (qwk le le′ x) u
    lΩ↓ : ∀ {b mo φ χ ps y ys n k ν} {q : n <ᴸ m} {fe : ∀ {L} → Ev L φ → Ev L Fl} {ac : ∀ {L} → Ev L (χ n) → k <ᴵ L} {h : ∀ ξ ζ → Vs m q k ξ ζ → Q m c (ξ ⊔ φ) (lo n ζ ∪ χ)} → cof (y ∷ ys) ≡ cΩ (P n ν) →
         (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {mo′} → Cv mo mo′ → ∀ ξ ζ (z : Q n k ξ ζ) θ → Lv q mo′ z θ → Lq₊ b mo′ (h ξ ζ (intoV q z)) (ps ++ fsT (y ∷ ys) θ)) → Lq₊ b mo (qΩ↓ q fe ac h) (ps ++ (y ∷ ys))
    lΩ : ∀ {b mo φ χ ps y ys k ν} {fe : ∀ {L} → Ev L φ → Ev L Fl} {r : k <ᴵ c} {h : ∀ ξ ζ → Us m k (<→◃ r) ξ ζ → Q m c (ξ ⊔ φ) (lo m ζ ∪ χ)} → cof (y ∷ ys) ≡ cΩ (P m ν) →
         (Iν : Idx ν) → k ≅ᴵ lvI Iν →
         (∀ {mo′} → Cv mo mo′ → ∀ ξ ζ (z : Q m k ξ ζ) θ → L (<→◃ r) mo′ z θ → Lq₊ b mo′ (h ξ ζ (intoU (<→◃ r) z)) (ps ++ fsT (y ∷ ys) θ)) → Lq₊ b mo (qΩ fe r h) (ps ++ (y ∷ ys))
    lob : ∀ {b mo φ χ u k} {r : k ◃₁ c} {z : Us m k (◃₁→◃ r) φ χ} {x : Q m c φ χ} → L (◃₁→◃ r) mo (outU (◃₁→◃ r) z) u → Lq₊ false mo x u → Lq₊ b mo (omk r z x) u

XL : Ht → Set₁
XL n = Mode → ∀ {k ξ ζ} → Q n k ξ ζ → T → Set

LqV : ∀ m (v : ∀ {n} → n <ᴸ m → XL n) c → Bool → Mode → ∀ {φ χ} → Q m c φ χ → T → Set
LLV : ∀ m (v : ∀ {n} → n <ᴸ m → XL n) c {k} → k ◃ c → Mode → ∀ {ξ ζ} → Q m k ξ ζ → T → Set
LqV m v c b mo x u = Lq₊ m c (LLV m v c) v b mo x u
LLV m v (suc c)   zero      mo x u = LqV m v c true mo x u
LLV m v (suc c)   (suc r)   mo x u = LLV m v c r mo x u
LLV m v (lim f s) (self n)  mo x u = LqV m v (f n) true mo x u
LLV m v (lim f s) (lim n r) mo x u = LLV m v (f n) r mo x u

FLv : ∀ m → (∀ {n} → n <ᴸ m → XL n) → XL m
FLv m v mo {k} x u = LqV m v k true mo x u

LV : ∀ m {n} → n <ᴸ m → XL n
LV = Rec XL FLv

Lq : ∀ m c → Bool → Mode → ∀ {φ χ} → Q m c φ χ → T → Set
Lq m = LqV m (LV m)

LL : ∀ m c {k} → k ◃ c → Mode → ∀ {ξ ζ} → Q m k ξ ζ → T → Set
LL m = LLV m (LV m)

outL : ∀ {m c k} (r : k ◃ c) {mo ξ ζ} {z : Q m k ξ ζ} {θ} → LL m c r mo z θ → Lq m k true mo z θ
outL zero      l = l
outL (suc r)   l = outL r l
outL (self n)  l = l
outL (lim n r) l = outL r l

intoL : ∀ {m c k} (r : k ◃ c) {mo ξ ζ} {z : Q m k ξ ζ} {θ} → Lq m k true mo z θ → LL m c r mo z θ
intoL zero      l = l
intoL (suc r)   l = intoL r l
intoL (self n)  l = l
intoL (lim n r) l = intoL r l

outLV : ∀ {m n} (q : n <ᴸ m) {mo k ξ ζ} {z : Q n k ξ ζ} {θ} → LV m q mo z θ → Lq n k true mo z θ
outLV {m} q {mo} {z = z} {θ} l = subst (λ X → X mo z θ) (Rec-β XL FLv m q) l

intoLV : ∀ {m n} (q : n <ᴸ m) {mo k ξ ζ} {z : Q n k ξ ζ} {θ} → Lq n k true mo z θ → LV m q mo z θ
intoLV {m} q {mo} {z = z} {θ} l = subst (λ X → X mo z θ) (sym (Rec-β XL FLv m q)) l

Lq-cv : ∀ {m c b a a′ φ χ} {x : Q m c φ χ} {u} → Cv a a′ → Lq m c b a x u → Lq m c b a′ x u
Lq-cv v lz = lz
Lq-cv v (ls cc F Fχ Fc l) = ls cc (FlU-cv v F) Fχ Fc (Lq-cv v l)
Lq-cv v (ll cc h) = ll cc (λ n → Lq-cv v (h n))
Lq-cv v (li cc I e hP hI) = li cc I e (λ η x l s v′ → hP η x l s (Cv-tr v v′)) (λ η x i → Lq-cv v (hI η x i))
Lq-cv v (lĉ cc K h₀ hk) = lĉ cc K (Lq-cv v h₀) (λ k → Lq-cv v (hk k))
Lq-cv v (lŝ cc I b o h₀ hg) = lŝ cc I b o (Lq-cv v h₀) (λ θ Y hY lY nθ lt e → Lq-cv v (hg θ Y hY lY nθ lt e))
Lq-cv v (lclo F cc h₀ hg) = lclo (Fw-cv v F) cc (Lq-cv v h₀) (λ θ Y hY lY nθ lt → Lq-cv v (hg θ Y hY lY nθ lt))
Lq-cv v (lcl F cc I₀ z₀ o h₀ hg) = lcl F cc I₀ z₀ o (Lq-cv v h₀) (λ θ Y hY lY nθ lt → Lq-cv v (hg θ Y hY lY nθ lt))
Lq-cv v (lwk l) = lwk (Lq-cv v l)
Lq-cv v (lΩ↓ cc I e f) = lΩ↓ cc I e (λ v′ → f (Cv-tr v v′))
Lq-cv v (lΩ cc I e f) = lΩ cc I e (λ v′ → f (Cv-tr v v′))
Lq-cv v (lob {r = zero} l x) = lob (Lq-cv v l) (Lq-cv v x)
Lq-cv v (lob {r = self n} l x) = lob (Lq-cv v l) (Lq-cv v x)

rq : ∀ {m c b mo φ χ} {x : Q m c φ χ} {u v} → u ≡ v → Lq m c b mo x u → Lq m c b mo x v
rq refl l = l
```

## §2 加法

```agda
FWχ-⊞ : ∀ {χ ρ x ps y ys} → FlrLab χ x → FW₀ (ρ ⊔ fk zero) ps y ys → FW₀ ((χ ⊔ ρ) ⊔ fk zero) (x ++ ps) y ys
FWχ-⊞ F G (inr ink) = inj₁ z≅
FWχ-⊞ {ps = ps} F G (inl (inl k)) with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (++-assoc _ ps _)) (OccPre _ o))
FWχ-⊞ {x = x} {ps = ps} F G (inl (inr k)) with G (inl k)
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → subst (Occ w) (sym (++-assoc x ps _)) (OccΣ x (o θ)))

Lq-⊞ : ∀ {m c b b′ mo φ χ ψ ρ} {W : Q m c φ χ} {t : Q m c ψ ρ} {x y} → Lq m c b mo W x → FlM mo φ x → (∀ i → i <ᴸ m → FlrLab (χ i) x) → FC b c x → Lq m c b′ mo t y → Lq m c b mo (W ⊞ t) (x ++ y)
Lq-⊞ {x = x} lW F Fχ Fc lz = lwk (rq (sym (++-identityʳ x)) lW)
Lq-⊞ {x = x} lW F Fχ Fc (ls {ps = ps} {y} {ys} cc Fa Fb _ l) =
  rq (++-assoc x ps (y ∷ ys)) (ls {ps = x ++ ps} cc (subst (FlU _ _) (sym (++-assoc x ps _)) (FlU-⊔ F Fa))
     (λ i q → subst (FlrLab _) (sym (++-assoc x ps _)) (FlrLab-⊔ (Fχ i q) (Fb i q)))
     (subst (FC _ _) (sym (++-assoc x ps _)) (FC-pre _ Fc)) (rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc l)))
Lq-⊞ {x = x} lW F Fχ Fc (ll {ps = ps} {y} {ys} cc h) =
  rq (++-assoc x ps (y ∷ ys)) (ll {ps = x ++ ps} cc (λ n → rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc (h n))))
Lq-⊞ {x = x} lW F Fχ Fc (li {ps = ps} {y} {ys} cc I e hP hI) =
  rq (++-assoc x ps (y ∷ ys)) (li {ps = x ++ ps} cc I e
     (λ η z l s v → rq (sym (++-assoc x ps _)) (Lq-⊞ (Lq-cv v lW) (FlM-cv v F) Fχ Fc (hP η z l s v)))
     (λ η z i → rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc (hI η z i))))
Lq-⊞ {x = x} lW F Fχ Fc (lĉ {ps = ps} {y} {ys} cc K h₀ hk) =
  rq (++-assoc x ps (y ∷ ys)) (lĉ {ps = x ++ ps} cc K (rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc h₀)) (λ k → rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc (hk k))))
Lq-⊞ {x = x} lW F Fχ Fc (lŝ {ps = ps} {y} {ys} cc I b o h₀ hg) =
  rq (++-assoc x ps (y ∷ ys)) (lŝ {ps = x ++ ps} cc I b (λ θ → subst (Occ _) (sym (++-assoc x ps _)) (OccΣ x (o θ)))
     (rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc h₀))
     (λ θ Y hY lY nθ lt e → rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc (hg θ Y hY lY nθ lt e))))
Lq-⊞ {x = x} lW F Fχ Fc (lclo {ps = ps} {y} {ys} G cc h₀ hg) =
  rq (++-assoc x ps (y ∷ ys)) (lwk (lclo {ps = x ++ ps} (Fw-⊕ F G) cc
     (lwk (rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc h₀)))
     (λ θ Y hY lY nθ lt → lwk (rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc (hg θ Y hY lY nθ lt))))))
Lq-⊞ {x = x} lW F Fχ Fc (lcl {ps = ps} {y} {ys} {q = q} G cc I₀ z₀ o h₀ hg) =
  rq (++-assoc x ps (y ∷ ys)) (lcl {ps = x ++ ps} (FWχ-⊞ (Fχ _ q) G) cc I₀ z₀ (λ θ → subst (Occ _) (sym (++-assoc x ps _)) (OccΣ x (o θ)))
     (rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc h₀))
     (λ θ Y hY lY nθ lt → lwk (rq (sym (++-assoc x ps _)) (Lq-⊞ lW F Fχ Fc (hg θ Y hY lY nθ lt)))))
Lq-⊞ lW F Fχ Fc (lwk l) = lwk (Lq-⊞ lW F Fχ Fc l)
Lq-⊞ {x = x} lW F Fχ Fc (lΩ↓ {ps = ps} {y} {ys} cc I e f) =
  rq (++-assoc x ps (y ∷ ys)) (lΩ↓ {ps = x ++ ps} cc I e
     (λ v ξ ζ z θ l → lwk (rq (sym (++-assoc x ps _)) (Lq-⊞ (Lq-cv v lW) (FlM-cv v F) Fχ Fc (f v ξ ζ z θ l)))))
Lq-⊞ {x = x} lW F Fχ Fc (lΩ {ps = ps} {y} {ys} cc I e f) =
  rq (++-assoc x ps (y ∷ ys)) (lΩ {ps = x ++ ps} cc I e
     (λ v ξ ζ z θ l → lwk (rq (sym (++-assoc x ps _)) (Lq-⊞ (Lq-cv v lW) (FlM-cv v F) Fχ Fc (f v ξ ζ z θ l)))))
Lq-⊞ lW F Fχ Fc (lob l x₁) = Lq-⊞ lW F Fχ Fc x₁
```

## §3 嵌入

```agda
out-intoU : ∀ {m c k} (r : k ◃ c) {ξ ζ} (z : Q m k ξ ζ) → outU r (intoU r z) ≡ z
out-intoU zero      z = refl
out-intoU (suc r)   z = out-intoU r z
out-intoU (self n)  z = refl
out-intoU (lim n r) z = out-intoU r z

Lq-ι : ∀ {m c d b mo φ χ} (q : c ◃ d) {x : Q m c φ χ} {u} → Lq m c b mo x u → Lq m d false mo (ι q x) u
Lq-ι q lz = lz
Lq-ι q (ls cc F Fχ _ l) = ls cc F Fχ tt (Lq-ι q l)
Lq-ι q (ll cc h) = ll cc (λ n → Lq-ι q (h n))
Lq-ι q (li cc I e hP hI) = li cc I e (λ η x l s v → Lq-ι q (hP η x l s v)) (λ η x i → Lq-ι q (hI η x i))
Lq-ι q (lĉ cc K h₀ hk) = lĉ cc K (Lq-ι q h₀) (λ k → Lq-ι q (hk k))
Lq-ι q (lŝ cc I b o h₀ hg) = lŝ cc I b o (Lq-ι q h₀) (λ θ Y hY lY nθ lt e → Lq-ι q (hg θ Y hY lY nθ lt e))
Lq-ι q (lclo F cc h₀ hg) = lclo F cc (Lq-ι q h₀) (λ θ Y hY lY nθ lt → Lq-ι q (hg θ Y hY lY nθ lt))
Lq-ι q (lcl F cc I₀ z₀ o h₀ hg) = lcl F cc I₀ z₀ o (Lq-ι q h₀) (λ θ Y hY lY nθ lt → Lq-ι q (hg θ Y hY lY nθ lt))
Lq-ι q (lwk l) = lwk (Lq-ι q l)
Lq-ι q (lΩ↓ cc I e f) = lΩ↓ cc I e (λ v ξ ζ z θ l → Lq-ι q (f v ξ ζ z θ l))
Lq-ι {m} {d = d} q (lΩ {ps = ps} {y} {ys} {r = r} {h = h} cc I e f) =
  lΩ {r = <◃ r q} cc I e
     (λ {mo′} v ξ ζ z θ l → subst (λ w → Lq m d false mo′ (ι q (h ξ ζ (intoU (<→◃ r) w))) (ps ++ fsT (y ∷ ys) θ)) (sym (out-intoU (<→◃ (<◃ r q)) z))
                               (Lq-ι q (f v ξ ζ z θ (intoL (<→◃ r) (outL (<→◃ (<◃ r q)) l)))))
Lq-ι q (lob l x) = Lq-ι q x

FlC : ∀ {χ : Fv} {x u} n {m} → FlrLab x u → (∀ i → i <ᴸ n → FlrLab (χ i) u) → ∀ i → i <ᴸ m → FlrLab (cap χ n x i) u
FlC n F G i q with tri i n
... | tlt r = G i r
... | teq _ = F
... | tgt _ = λ ()

FC-lift : ∀ {k u b} → FC true k u → FC b zero u
FC-lift {b = false} F = tt
FC-lift {b = true} F = λ ()

Lq-ι↓ : ∀ {n m k b mo φ χ} (d : n <ᴸ m) {x : Q n k φ χ} {u} → Lq n k true mo x u → Lq m zero b mo (ι↓ {α = zero} d x) u
Lq-ι↓ d lz = lz
Lq-ι↓ {n = n} {χ = χ} d (ls cc F Fχ Fc l) = ls cc F (FlC {χ} n Fc Fχ) (FC-lift Fc) (Lq-ι↓ d l)
Lq-ι↓ d (ll cc h) = ll cc (λ n → Lq-ι↓ d (h n))
Lq-ι↓ d (li cc I e hP hI) = li cc I e (λ η x l s v → Lq-ι↓ d (hP η x l s v)) (λ η x i → Lq-ι↓ d (hI η x i))
Lq-ι↓ d (lĉ cc K h₀′ hk) = lĉ cc K (Lq-ι↓ d h₀′) (λ k → Lq-ι↓ d (hk k))
Lq-ι↓ d (lŝ cc I b o h₀′ hg) = lŝ cc I b o (Lq-ι↓ d h₀′) (λ θ Y hY lY nθ lt e → Lq-ι↓ d (hg θ Y hY lY nθ lt e))
Lq-ι↓ d (lclo F cc h₀′ hg) = lclo F cc (Lq-ι↓ d h₀′) (λ θ Y hY lY nθ lt → Lq-ι↓ d (hg θ Y hY lY nθ lt))
Lq-ι↓ d (lcl F cc I₀ z₀ o h₀′ hg) = lcl F cc I₀ z₀ o (Lq-ι↓ d h₀′) (λ θ Y hY lY nθ lt → lwk (Lq-ι↓ d (hg θ Y hY lY nθ lt)))
Lq-ι↓ d (lwk l) = lwk (Lq-ι↓ d l)
Lq-ι↓ {m = m} {b = b} d (lΩ↓ {ps = ps} {y} {ys} {q = q} {h = h} cc I e f) =
  lΩ↓ {q = tr< q d} cc I e (λ {mo′} v ξ ζ z θ l → lwk
    (subst (λ w → Lq m zero b mo′ (ι↓ d (h ξ ζ (intoV q w))) (ps ++ fsT (y ∷ ys) θ)) (sym (out-intoV (tr< q d) z))
       (Lq-ι↓ d (f v ξ ζ _ θ (intoLV q (outLV (tr< q d) l))))))
Lq-ι↓ {m = m} {b = b} d (lΩ {ps = ps} {y} {ys} {r = r} {h = h} cc I e f) =
  lΩ↓ {q = d} cc I e (λ {mo′} v ξ ζ z θ l → lwk
    (subst (λ w → Lq m zero b mo′ (ι↓ d (h ξ ζ (intoU (<→◃ r) w))) (ps ++ fsT (y ∷ ys) θ)) (sym (out-intoV d z))
       (Lq-ι↓ d (f v ξ ζ _ θ (intoL (<→◃ r) (outLV d l))))))
Lq-ι↓ {k = suc a} d (lob {r = zero} l x) = lwk (Lq-ι↓ d l)
Lq-ι↓ {k = lim f s} d (lob {r = self n} l x) = lwk (Lq-ι↓ d l)
```

## §2 尾巴

```agda
Zu : Mode → Ordᴵ → Flr → Set
Zu m zero      φ = ∀ u → FlU m φ u
Zu m (suc _)   φ = ⊤
Zu m (lim _ _) φ = ⊤

Zu-flo : ∀ m k → Zu m k (flo k)
Zu-flo hon zero u ()
Zu-flo (wkm c) zero u ()
Zu-flo m (suc k) = tt
Zu-flo m (lim f s) = tt

Zu-of : ∀ {m k φ} → Zc₀ k φ → Zu m k φ
Zu-of {m = hon} {k = zero} f u k with f k
... | inj₁ e = inj₁ e
... | inj₂ e = inj₂ (inj₁ e)
Zu-of {m = wkm c} {k = zero} f u k with f k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ e = inj₂ (inj₁ e)
Zu-of {k = suc _} f = tt
Zu-of {k = lim _ _} f = tt

FP→U : ∀ {c φ} → FP c φ → ∀ u → FlU (wkm c) φ u
FP→U f u k with f k
... | inj₁ g = inj₁ g
... | inj₂ e = inj₂ (inj₁ e)

FH→U : ∀ {m φ z u v vs} → z ≡ ψᵗ u v ∷ vs → FH φ z → FlU m φ z
FH→U {m = hon} refl f k with f k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ (I , kw)) = inj₂ (inj₂ (_ , I , kw , oh))
FH→U {m = wkm c} refl f k with f k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ (I , kw)) = inj₂ (inj₂ (_ , I , kw , oh))

module Tl {c : Ordᴵ} {χ : Fv} where
  tlA : ∀ {m φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → (∀ u → FlU m φ u) → Lab0ᴸ t y → Lq h₀ c false m (tl {χ = χ} φ cv t) y
  tlA {y = []} fp (lz cc) = lz
  tlA {y = y ∷ ys} fp (lz cc) = ⊥-elim (cof-ne y ys cc)
  tlA {y = []} fp (ls () l)
  tlA {y = y ∷ ys} fp (ls cc l) = ls {ps = []} cc (fp _) (λ i q₀ → ⊥-elim (no< q₀)) tt (tlA fp l)
  tlA {y = []} fp (ll () h)
  tlA {y = y ∷ ys} fp (ll cc h) = ll {ps = []} cc (λ n → tlA fp (h n))
  tlA {y = []} fp (lŝ₀ () K h₀ hk)
  tlA {y = y ∷ ys} fp (lŝ₀ cc K h₀′ hk) = lĉ {ps = []} cc K (tlA fp h₀′) (λ k → tlA fp (hk k))
  tlA {y = []} fp (lĉ () K h₀ hk)
  tlA {y = y ∷ ys} fp (lĉ cc K h₀ hk) = lĉ {ps = []} cc K (tlA fp h₀) (λ k → tlA fp (hk k))

  tlV : ∀ {i k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP i φ → LvOK i k → LabL t y → Lq h₀ c false (wkm i) (tl {χ = χ} φ cv t) y
  tl₊ : ∀ {i k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FP i φ → LvOK i k → LabL₊ k Ll t y → Lq h₀ c false (wkm i) (tl {χ = χ} φ cv t) y

  tlV {k = zero}    fp lv at = tlA (FP→U fp) (atomL at)
  tlV {k = suc _}   fp lv h  = tl₊ fp lv h
  tlV {k = lim _ _} fp lv h  = tl₊ fp lv h

  tl₊ {y = []} fp lv (gz cc) = lz
  tl₊ {y = y ∷ ys} fp lv (gz cc) = ⊥-elim (cof-ne y ys cc)
  tl₊ {y = []} fp lv (gs () l)
  tl₊ {y = y ∷ ys} fp lv (gs cc l) = ls {ps = []} cc (FP→U fp _) (λ i q₀ → ⊥-elim (no< q₀)) tt (tl₊ fp lv l)
  tl₊ {y = []} fp lv (gl () h)
  tl₊ {y = y ∷ ys} fp lv (gl cc h) = ll {ps = []} cc (λ n → tl₊ fp lv (h n))
  tl₊ {k = suc k′} fp lv (gu {r = zero} h) = lwk (tlV {φ = flo k′} {cv = cvFlo k′} (FP-flo lv) (LvOK-pred lv) h)
  tl₊ {k = lim f s} fp lv (gu {r = self n} h) = lwk (tlV {φ = flo (f n)} {cv = cvFlo (f n)} (FP-flo′ (LvOK-self lv n)) (LvOK-self lv n) h)
  tl₊ {y = []} fp lv (gi () I ej h)
  tl₊ {y = y ∷ ys} fp lv (gi {q = q} cc I ej h) =
    li {ps = []} cc I ej (λ η x l s v → Lq-cv v (tl₊ fp lv (h η x (→Ll (<→◃ q) l))))
       (λ η x i → tl₊ fp lv (h η x (→Ll (<→◃ q) (proj₁ i))))
  tl₊ {y = []} fp lv (gĉ () K h₀ hk)
  tl₊ {y = y ∷ ys} fp lv (gĉ cc K h₀ hk) = lĉ {ps = []} cc K (tl₊ fp lv h₀) (λ k → tl₊ fp lv (hk k))
  tl₊ {k = zero} fp lv (gŝ () cc Iw bw ob h₀ hg)
  tl₊ {k = suc _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  tl₊ {k = suc _} {y = y ∷ ys} fp lv (gŝ kk cc Iw bw ob h₀ hg) =
    lŝ {ps = []} cc Iw bw ob (tl₊ fp lv h₀) (λ θ Y hY lY nθ lt e → tl₊ fp lv (hg θ Y hY lY nθ lt e))
  tl₊ {k = lim _ _} {y = []} fp lv (gŝ kk () Iw bw ob h₀ hg)
  tl₊ {k = lim _ _} {y = y ∷ ys} fp lv (gŝ kk cc Iw bw ob h₀ hg) =
    lŝ {ps = []} cc Iw bw ob (tl₊ fp lv h₀) (λ θ Y hY lY nθ lt e → tl₊ fp lv (hg θ Y hY lY nθ lt e))

  tlH : ∀ {m k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FH φ y → Hn t y → LabL₊ k Ll t y → Lq h₀ c false m (tl {χ = χ} φ cv t) y
  tlΩ : ∀ {m θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {k} → k ≅ᴵ toLevel Y hY → ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} → Zu m k φ →
        Lq h₀ c false m (tl {χ = χ} φ cv (Ωˢ k)) (Ωt θ)
  tlT : ∀ {m j} {x : Ordˢ j} {η} → InpW j η x → Lq h₀ c false m (tl {χ = χ} (flo j) (cvFlo j) x) η

  tlT {m} {j = zero}    (l , ch) = tlA (Zu-flo m zero) (atomL l)
  tlT {j = suc _}   (l , ch) = tlH (proj₂ (ch refl)) (proj₁ (ch refl)) l
  tlT {j = lim _ _} (l , ch) = tlH (proj₂ (ch refl)) (proj₁ (ch refl)) l

  tlH fp (hΩ refl (Y , hY , lY , nY) e) l = tlΩ Y hY lY nY e (Zu-of (Zc₀-of (Y , hY , lY , nY) e fp))
  tlH {y = []} fp hz (gz cc) = lz
  tlH {y = y ∷ ys} fp hz (gz cc) = ⊥-elim (cof-ne y ys cc)
  tlH {y = []} fp (hs () n) l
  tlH {y = y@(ψᵗ _ _) ∷ ys} fp (hs nb n) (gs cc l) =
    ls {ps = []} cc (FH→U (proj₂ (proj₂ (pred-Pr nb cc))) (FH-pred nb cc fp)) (λ i q₀ → ⊥-elim (no< q₀)) tt (tlH (FH-pred nb cc fp) n l)
  tlH {y = []} fp (hl () n) l
  tlH {y = y ∷ ys} fp (hl nb n) (gl cc h) = ll {ps = []} cc (λ m → tlH (FH-fsn nb fp m) (n m) (h m))
  tlH {y = []} fp (hi () n) l
  tlH {y = y ∷ ys} fp (hi {q = q} nb n) (gi cc I ej h) =
    li {ps = []} cc I ej (λ η x l s v → tlH (FH-fsT nb fp η) (n η x l) (h η x (→Ll (<→◃ q) l)))
       (λ η x i → tlH (FH-fsT nb fp η) (n η x (proj₁ i)) (h η x (→Ll (<→◃ q) (proj₁ i))))
  tlH {y = []} fp (hĉ () cw K g₀ n₀ gk nk) l
  tlH {y = y ∷ ys} fp (hĉ nb cw K g₀ n₀ gk nk) l = lĉ {ps = []} cw K (tlH (FH-fsn nb fp 0) n₀ g₀) (λ k → tlH (FH-fsn nb fp (suc k)) (nk k) (gk k))
  tlH {k = zero} fp (hŝ nb n₀ nk) (gŝ () cc Iw bw ob h₀ hg)
  tlH {k = suc _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg)
  tlH {k = suc _} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ kk cc Iw bw ob h₀ hg) =
    lŝ {ps = []} cc Iw bw ob (tlH (FH-fsT nb fp (natT 1)) n₀ h₀) (λ θ Y hY lY nθ lt e → tlH (FH-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e))
  tlH {k = lim _ _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg)
  tlH {k = lim _ _} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ kk cc Iw bw ob h₀ hg) =
    lŝ {ps = []} cc Iw bw ob (tlH (FH-fsT nb fp (natT 1)) n₀ h₀) (λ θ Y hY lY nθ lt e → tlH (FH-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e))

  tlΩ {θ = []} Ord₊.zero hY l nθ z≅ zc = tlA zc (atomL (LabL-Ω Ord₊.zero hY l nθ z≅))
  tlΩ {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ zc with Lab0[] l
  ... | ()
  tlΩ (Ord₊.suc Y) hY (l0 cc ()) nθ (s≅ e) zc
  tlΩ (Ord₊.suc Y) hY (lω cc () h) nθ (s≅ e) zc
  tlΩ {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) zc
  tlΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc j} (s≅ e) {φ} {cv} zc =
    li {ps = []} {y = ψᵗ (w ∷ ws) []} {ys = []} (cong (E.cofψ0 (w ∷ ws)) c₁) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e
       (λ η x lx {i} s v → rq (sym (fsTΩ c₁ η)) (lwk (tlV {φ = flo j} {cv = cvFlo j} (FP-flo′ (inj₁ (⊑ᴵ-trans (≺→⊑ s) (⊑-suc i)))) (inj₁ (⊑ᴵ-trans (≺→⊑ s) (⊑-suc i))) lx)))
       (λ η x ix → rq (sym (fsTΩ c₁ η)) (lwk (tlT ix)))
  tlΩ (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) zc
  tlΩ (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) zc
  tlΩ {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) zc
  tlΩ {m = m} {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {k = lim f s} (l≅ ee) {φ} {cv} zc =
    ll {ps = []} {y = ψᵗ (w ∷ ws) []} {ys = []} (cong (E.cofψ0 (w ∷ ws)) c₁)
       (λ n → rq (sym (E.fsn0-eq w ws n c₁))
                 (lwk (tlΩ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) {flo (f n)} {cvFlo (f n)} (Zu-flo m (f n)))))
  tlΩ (Ord₊.limᵢ () f) hY l nθ e zc
  tlΩ (Ord₊.up () x) hY l nθ e zc
```


## §5 $\dot\Omega$

```agda
I₁ᵖ : Idx (natT 1)
I₁ᵖ = one⁰ , hs hz , lab1 , nf1

z≼1 : zero ≼ lvI I₁ᵖ
z≼1 = inj₁ (via z≅ zero)

Lq-up : ∀ {mo φ χ} {x : Q h₀ zero φ χ} {u} → Lq h₀ zero false mo x u → Lq h₀ zero true mo x u
Lq-up lz = lz
Lq-up (ls cc F Fχ _ l) = ls cc F Fχ (λ ()) (Lq-up l)
Lq-up (ll cc h) = ll cc (λ n → Lq-up (h n))
Lq-up (li cc I e hP hI) = li cc I e (λ η x l s v → Lq-up (hP η x l s v)) (λ η x i → Lq-up (hI η x i))
Lq-up (lĉ cc K h₀′ hk) = lĉ cc K (Lq-up h₀′) (λ k → Lq-up (hk k))
Lq-up (lŝ cc I b o h₀′ hg) = lŝ cc I b o (Lq-up h₀′) (λ θ Y hY lY nθ lt e → Lq-up (hg θ Y hY lY nθ lt e))
Lq-up (lclo F cc h₀′ hg) = lclo F cc (Lq-up h₀′) (λ θ Y hY lY nθ lt → Lq-up (hg θ Y hY lY nθ lt))
Lq-up (lcl {q = q} F cc I₀ z₀ o h₀′ hg) = ⊥-elim (no< q)
Lq-up (lwk l) = lwk (Lq-up l)
Lq-up (lΩ↓ {q = q} cc I e f) = ⊥-elim (no< q)

ZuK : ∀ m k → Zu m k (fz ⊔ fk k)
ZuK hon zero u (inr ink) = inj₁ z≅
ZuK (wkm c) zero u (inr ink) = inj₁ (inj₁ (inj₁ z≅))
ZuK m (suc k) = tt
ZuK m (lim f s) = tt

Fw-Ω̂ : ∀ m → Fw m (fz ⊔ fk zero) [] ΩΩ []
Fw-Ω̂ hon (inr ink) = inj₁ z≅
Fw-Ω̂ (wkm c) (inr ink) = inj₁ (inj₁ (inj₁ z≅))

Fw-cl : ∀ {y} → FW₀ (fz ⊔ fk zero) [] y []
Fw-cl (inr ink) = inj₁ z≅
```

```agda
XLq : Ht → Set
XLq m = ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {α} → α ≅ᴵ toLevel Y hY → ∀ mo → Lq m α true mo (Ω̇ m α) (Ωt (P m θ))

-- 第 0 行
rowLq : ∀ m (I : ∀ {n} → n <ᴸ m → XLq n) (v : View _<ᴸ_ h₀ m) → Row₀ 𝕊 dr P m v (dr m) → ∀ mo → Lq m zero true mo (rowV m (ΩI m) v) (Ωt (P m []))
rowLq _ I base (rb e) mo =
  rq (cong Ωt (sym e)) (Lq-up (lclo {ps = []} {y = ΩΩ} {ys = []} (Fw-Ω̂ mo) refl
       (Tl.tlΩ one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _) {fz ⊔ fk zero} {proj₂} tt)
       (λ θ Y hY lY nθ lt → Tl.tlΩ Y hY lY nθ (≅ᴵ-refl _) {fz ⊔ fk (toLevel Y hY)} {λ e q → proj₂ e (suc q)} (ZuK mo (toLevel Y hY)))))
rowLq m I (clos {n = n} q) (rc .q cc fs) mo =
  subst (λ X → Lq m zero true mo (rowC q X) (Ωt (P m []))) (sym (ΩI≡ q))
  (lcl {ps = []} {y = ψᵗ (P m []) []} {ys = []} {q = q} Fw-cl (cofΩt-Ω (P m []) cc) I₁ᵖ z≼1
      (λ θ → subst (Occ _) (sym (fsTe θ)) (os (P-occ n θ)))
      (lwk (rq (sym (fsTe (natT 1))) (Lq-ι↓ q (I q one⁰ (hs hz) lab1 nf1 (s≅ z≅) mo))))
      (λ θ Y hY lY nθ lt → lwk (rq (sym (fsTe θ)) (Lq-ι↓ q (I q Y hY lY nθ (≅ᴵ-refl _) mo)))))
  where
  fsTe : ∀ θ → fsT (Ωt (P m [])) θ ≡ Ωt (P n θ)
  fsTe θ = trans (fsT-ΩtΩ (P m []) cc θ) (cong Ωt (fs θ))
rowLq m I (chain F qs₁) r mo with dr m | r
rowLq m I (chain F qs₁) r mo | keep | rl .F .qs₁ cc f0 fs =
  ll {ps = []} {y = ψᵗ (P m []) []} {ys = []} (cofΩt-ω (P m []) cc)
     (λ { zero → rq (sym (trans (fsn-Ωt (P m []) cc 0) (cong Ωt f0))) (𝟏-lab mo)
        ; (suc i) → rq (sym (trans (fsn-Ωt (P m []) cc (suc i)) (cong Ωt (fs i))))
             (subst (λ X → Lq m zero true mo (stepL (qs₁ i) X) (Ωt (P (F i) []))) (sym (ΩI≡ (qs₁ i)))
                (lwk (Lq-ι↓ (qs₁ i) (I (qs₁ i) Ord₊.zero hz (l0 refl z≅) n[] z≅ mo)))) })
  where
  𝟏-lab : ∀ mo → Lq m zero true mo (𝟏L {m}) (Ωt [])
  𝟏-lab mo = lwk (ls {ps = []} {y = 𝟏} {ys = []} refl (fl mo) (λ i q ()) (λ ()) lz)
    where
    fl : ∀ mo → FlU mo fz []
    fl hon ()
    fl (wkm c) ()
rowLq m I (chain F qs₁) r mo | repl n q | rr .q .F .qs₁ cc f0 fs =
  ll {ps = []} {y = ψᵗ (P m []) []} {ys = []} (cofΩt-ω (P m []) cc)
     (λ { zero → rq (sym (trans (fsn-Ωt (P m []) cc 0) (cong Ωt f0)))
             (subst (λ X → Lq m zero true mo (stepL q X) (Ωt (P n []))) (sym (ΩI≡ q))
                (lwk (Lq-ι↓ q (I q Ord₊.zero hz (l0 refl z≅) n[] z≅ mo))))
        ; (suc i) → rq (sym (trans (fsn-Ωt (P m []) cc (suc i)) (cong Ωt (fs i))))
             (subst (λ X → Lq m zero true mo (stepL (qs₁ i) X) (Ωt (P (F i) []))) (sym (ΩI≡ (qs₁ i)))
                (lwk (Lq-ι↓ (qs₁ i) (I (qs₁ i) Ord₊.zero hz (l0 refl z≅) n[] z≅ mo)))) })
rowLq m I (chain F qs₁) r mo | drop | rh .F .qs₁ cc fs =
  ll {ps = []} {y = ψᵗ (P m []) []} {ys = []} (cofΩt-ω (P m []) cc)
     (λ i → rq (sym (trans (fsn-Ωt (P m []) cc i) (cong Ωt (fs i))))
             (subst (λ X → Lq m zero true mo (stepL (qs₁ i) X) (Ωt (P (F i) []))) (sym (ΩI≡ (qs₁ i)))
                (lwk (Lq-ι↓ (qs₁ i) (I (qs₁ i) Ord₊.zero hz (l0 refl z≅) n[] z≅ mo)))))

FLq : ∀ m → (∀ {n} → n <ᴸ m → XLq n) → XLq m
FLq m I {θ = []} Ord₊.zero hY l nθ z≅ mo = rowLq m I (view m) (P-row m) mo
FLq m I {θ = w ∷ ws} Ord₊.zero hY l nθ z≅ mo with Lab0[] l
... | ()
FLq m I (Ord₊.suc Y) hY (l0 cc ()) nθ (s≅ e) mo
FLq m I (Ord₊.suc Y) hY (lω cc () h) nθ (s≅ e) mo
FLq m I {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) mo
FLq m I {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {suc j} (s≅ e) mo =
  lΩ {ps = []} {y = ψᵗ (P m (w ∷ ws)) []} {ys = []}
     (trans (cofΩt-c1 (P m (w ∷ ws)) (trans (P-cof m w ws) c₁)) (cong cΩ (P-pred m w ws)))
     (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e
     (λ v ξ ζ z θ l′ → lwk (rq (sym (fsT-Ωt1 (P m (w ∷ ws)) (trans (P-cof m w ws) c₁) θ)) (lob l′ (Lq-ι zero l′))))
FLq m I (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) mo
FLq m I (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) mo
FLq m I {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) mo
FLq m I {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {lim f s} (l≅ ee) mo =
  ll {ps = []} {y = ψᵗ (P m (w ∷ ws)) []} {ys = []} (cofΩt-ω (P m (w ∷ ws)) (trans (P-cof m w ws) c₁))
     (λ n → rq (sym (trans (fsn-Ωt (P m (w ∷ ws)) (trans (P-cof m w ws) c₁) n) (cong Ωt (P-fsn m w ws n))))
               (lob (FLq m I (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) mo) (Lq-ι (self n) (FLq m I (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) mo))))

LqΩ̇ : ∀ m → XLq m
LqΩ̇ m = FLq m (Rec XLq FLq m)

LqΩ̇ᴵ : ∀ m {ν α} (I : Idx ν) → α ≅ᴵ lvI I → ∀ mo → Lq m α true mo (Ω̇ m α) (Ωt (P m ν))
LqΩ̇ᴵ m (Y , hY , lY , nY) e mo = LqΩ̇ m Y hY lY nY e mo
```
