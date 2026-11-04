> **机械克隆, 验收用.** 由 `OrdLabZUniform3Base` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZUniform3Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZSymbolic using (Mlev; Fs; Fst)
open import OCF.Align.EmbVVOZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; trˢ; tr⁻ˢ; H1-pen; H1-fsT)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Align.OrdLabZBachmann using (fs-gt; pen→<; gt→≤; clash; gt→<)
open import OCF.Align.OrdLabZClosure using (Pen; fsT₊-pen′; lt→<; eq→≡)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.EmbVVLZExtra using (occ<)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.EmbVVOZUniformS
open import OCF.Align.EmbVVOZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.EmbVVOZDecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Align.EmbVVOZDecouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP; Lab0[])
open import OCF.Align.EmbVVOZGoodLBase
open import OCF.Align.EmbVVOZOmegaExpBase using (σ⊥; πw; onCons; cofΣ; predΣ; fsnΣ; fsTΣ; OccΣ; cofW; repW; ωW; γW; γW-eq; gtW; penW; H1W; ne-w; 1<γ; ++-ne; fsT-ne)
open import OCF.Align.EmbVVOZOmegaSqBase using (cmpΩ)
open import OCF.Free.Floor public
open import OCF.Align.LadderLabZUniform3Base public using (Ob; OccPre; ψΩᵗ; ψ₀ᵗ)
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; lt; eq; gt;
              []<; cofA) renaming (ψ to ψᵗ)
```

## §3 界: 逐点上确界

```agda
≺→⊑ : ∀ {a b} → a ≺ᴵ b → a ⊑ᴵ b
≺→⊑ (via e q) = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ e) (Sim→⊑ᴵ (λ r → <ᴵ-trans r q))

dem : ∀ {K φ η} (k : InF K φ) → (K ≺ᴵ η) ⊎ (K ≅ᴵ zero) → Dem η k
dem ink     h = h
dem inb     (inj₁ s)  = ≺→⊑ s
dem inb     (inj₂ z≅) = z⊑
dem (inl k) h = dem k h
dem (inr k) h = dem k h

open Top public
```

## §4 统一折叠

```agda
repA : ∀ d {fl ψ} → A d fl → A (suc d) ψ → ℕ → A d (fl ⊔ ψ)
repA d Q fr zero          = wk d proj₁ Q
repA d Q fr (suc zero)    = fr Q
repA d Q fr (suc (suc m)) = wk d (λ { (u , v) → (u , v) , v }) (fr (repA d Q fr (suc m)))

fold : ∀ d {fl k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → A d fl → Ordˢ k → A d (fl ⊔ φ)
fold d φ cv P Ord₊ˢ.zero = wk d proj₁ P
fold zero    φ cv P (Ord₊ˢ.suc a) ev p = Ord₊ˢ.lim (iter (fold zero φ cv P a ev p +ˢ_) Ord₊ˢ.zero)
fold (suc d) φ cv P (Ord₊ˢ.suc a) Q    = limA d (λ m → repA d Q (fold (suc d) φ cv P a) m)
fold d φ cv P (Ord₊ˢ.lim f) = limA d (λ m → fold d φ cv P (f m))
fold d φ cv P (Ord₊ˢ.limᵢ q f) = limᵢA d (λ ev → cv (proj₂ ev) q) (λ x → fold d φ cv P (f (intoˢ (<→◃ q) x)))
fold d {k = suc k′} φ cv P (Ord₊ˢ.up zero x) =
  wk d (λ { (u , v) → u , toFlo k′ (λ q → cv v (suc q)) }) (fold d (flo k′) (cvFlo k′) P x)
fold d {k = lim f s} φ cv P (Ord₊ˢ.up (self n) x) =
  wk d (λ { (u , v) → u , toFlo (f n) (λ q → cv v (lim n q)) }) (fold d (flo (f n)) (cvFlo (f n)) P x)
fold d {k = zero}    φ cv P (Ord₊ˢ.ŝ c t₀ g) =
  ĉA d c (toZ t₀) (λ η e → toZ (g η e)) (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d {k = suc _}   φ cv P (Ord₊ˢ.ŝ c t₀ g) = ŝA d c (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d {k = lim _ _} φ cv P (Ord₊ˢ.ŝ c t₀ g) = ŝA d c (fold d φ cv P t₀) (λ η e → fold d φ cv P (g η e))
fold d φ cv P (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) = ĉA d c t₀ g (fold d φ cv P o₀) (λ η e → fold d φ cv P (o η e))

Ω̂A : ∀ d → A (suc d) (fk zero)
Ω̂A d {fl} P = cloA d {fl} (fold d (fk zero) (λ e → e) P (Ωˢ (suc zero)))
                         (λ η → fold d (fk η) (λ e q → e (suc q)) P (Ωˢ η))
```

## §5 符号项

```agda
Sym : Flr → Set
Sym φ = ∀ d → A (suc d) φ

Ψ : ∀ {φ} → Sym φ → Sym (fk zero ⊔ φ)
Ψ Y d P = Y (suc d) (Ω̂A d) P

infixl 6 _⊕_
_⊕_ : ∀ {φ ψ} → Sym φ → Sym ψ → Sym (φ ⊔ ψ)
(X ⊕ Y) d P = wk d (λ { (u , (v , w)) → (u , v) , w }) (Y d (X d P))
```

## §6 标签的形状

```agda
Lab₀ : Ordˢ zero → T → Set
Lab₀ x t = Σ (Goodᴸ (toZ x)) λ G → Lab (forceᴸ _ G) t

LW : ∀ {φ} → Run φ → T → Set
LW {φ} R u = ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
             LabL₊ i Ll (R ev p) (ψᵗ w u ∷ [])

L0 : ∀ {φ} → Run φ → T → Set
L0 {φ} R u = ∀ {ℓ} (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) → NF₁ (ψ₀ᵗ u) → Lab₀ (R ev p) (ψ₀ᵗ u)

infix 4 _≈ᴿ_
_≈ᴿ_ : ∀ {φ ψ} → Run φ → Run ψ → Set
_≈ᴿ_ {φ} {ψ} R R′ = ∀ {i i′ ℓ ℓ′} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ ψ) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → R ev p ≅ˢ R′ ev′ p′

record GR {φ} (R : Run φ) (u : T) : Set where
  constructor gr
  field
    gW : LW R u
    g0 : L0 R u
    gR : R ≈ᴿ R
open GR public
```

## §7 深度 0 的行引理

```agda
module _ {φ} {ps : T} {y : PT} {ys : T} where
  lim0 : ∀ {F : ℕ → Run φ} → cof (y ∷ ys) ≡ cω → (∀ n → L0 (F n) (ps ++ fsn (y ∷ ys) n)) → L0 (limA 0 F) (ps ++ (y ∷ ys))
  lim0 {F} c h ev p nf =
    limᴸ nf cω′ (λ n → proj₁ (Rn n)) (λ n → subst (Lab _) (sym (ωW [] ps y ys c n)) (proj₂ (Rn n)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    Rn = λ n → h n ev p (subst NF₁ (ωW [] ps y ys c n) (NF₁-fsn nf cω′ n))
```

```agda
module _ {φ} {ps : T} {y : PT} {ys : T} where
  suc0 : ∀ {R : Run φ} → cof (y ∷ ys) ≡ c1 → L0 R (ps ++ pred (y ∷ ys)) → L0 (sucRun R) (ps ++ (y ∷ ys))
  suc0 {R} c h ev p nf =
    limᴸ nf cω′ (λ m → proj₁ (Rs m)) (λ m → subst (Lab _) (sym (repW [] ps y ys c m)) (proj₂ (Rs m)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
    Rp = h ev p (subst NF₁ (repW [] ps y ys c 1) (NF₁-fsn nf cω′ 1))
    Rs = repᴸ (proj₁ Rp) (proj₂ Rp) (λ m → subst NF₁ (repW [] ps y ys c m) (NF₁-fsn nf cω′ m))
```

```agda
chainA : ∀ {φ j ℓ} → (∀ {L} → Ev L φ → j <ᴵ L) → (Ordˢ j → Run φ) → Ev ℓ φ → ℕ → Ordˢ j
chainA {j = j} ac H ev = iter (λ x → H x ev (ac ev)) (Ωˢ j)

fold1A : ∀ {φ j i ℓ} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} →
         (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → limᵢA 0 ac H ev p ≡ Ord₊ˢ.lim (λ m → H (chainA ac H ev m) ev p)
fold1A {ac = ac} {ev = ev} {p = p} h with <ᴵ-dec (ac ev) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen1A : ∀ {φ j i ℓ N} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ} {ev : Ev ℓ φ} {p : i <ᴵ ℓ} →
        j ≅ᴵ N → N ≺ᴵ i →
        Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
        limᵢA 0 ac H ev p ≡ Ord₊ˢ.limᵢ r (λ y → H (tr⁻ˢ e (outˢ (<→◃ r) y)) ev p)
pen1A {ac = ac} {ev = ev} {p = p} ej νi with <ᴵ-dec (ac ev) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))
```

```agda
module _ {φ c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {ps : T} {y : PT} {ys : T} where
  ĉ0 : ∀ {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} → cof (y ∷ ys) ≡ cω → (K : CCᴸ c t₀ g) →
       L0 O₀ (ps ++ fsn (y ∷ ys) 0) → (∀ k → L0 (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) →
       L0 (ĉA 0 c t₀ g O₀ O) (ps ++ (y ∷ ys))
  ĉ0 cw K h₀ hk ev p nu =
    ĉᴸ-mk nu cω′ K (proj₁ R₀) (subst (Lab _) (sym (ωW [] ps y ys cw 0)) (proj₂ R₀))
          (λ k → proj₁ (Rk k)) (λ k → subst (Lab _) (sym (ωW [] ps y ys cw (suc k))) (proj₂ (Rk k)))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) cw)
    R₀ = h₀ ev p (subst NF₁ (ωW [] ps y ys cw 0) (NF₁-fsn nu cω′ 0))
    Rk = λ k → hk k ev p (subst NF₁ (ωW [] ps y ys cw (suc k)) (NF₁-fsn nu cω′ (suc k)))
```

```agda
domP : ∀ {c w Y} ps′ (hY : HS Y) (Iw : Idx w) → c ⊑ᴵ suc (lvI Iw) → Occ w ps′ → Lab Y (ψ₀ᵗ ps′) → NF₁ (ψ₀ᵗ ps′) →
       c ⊑ᴵ toLevel Y hY
domP ps′ hY (W , hW , lW , nW) bw o lY nb =
  ⊑ᴵ-trans bw (s⊑′ (toLevel-≺ hW hY (Lab-oc lY nb lW nW (occ< nb (c∷ c[]) (od o) (Lab→Ctbl lW nW)))))

module _ {φ c w′} {ps : T} {y : PT} {ys : T} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ}
         (cs : cof (y ∷ ys) ≡ cΩ []) (Iw′ : Idx w′) (bw : c ⊑ᴵ suc (lvI Iw′)) (ob : Ob w′ ps y ys) where
  ŝ0 : L0 T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
       (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) → L0 (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
       L0 (ŝA 0 c T₀ G) (ps ++ (y ∷ ys))
  ŝ0 h₀ hg ev p nu =
    ĉᴸ-mk nu cω′ K (proj₁ R₀) (subst (Lab _) (sym (gtW [] ps y ys [] cs refl 0)) (proj₂ R₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (gtW [] ps y ys [] cs refl (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) cs)
    nfγ : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
    nfγ m = subst NF₁ (gtW [] ps y ys [] cs refl m) (NF₁-fsn nu cω′ m)
    R₀ = h₀ ev p (nfγ 0)
    Rg : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : c ⊑ᴵ toLevel Y hY) →
         Lab₀ (G (toLevel Y hY) e ev p) (γW ps (y ∷ ys) [] (suc (suc m)))
    Rg m Y hY lY e = hg _ Y hY lY (nfγ m) (1<γ ps y ys cs m) e ev p (nfγ (suc m))
    K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ R₀) (proj₂ R₀)
            (domP _ _ Iw′ bw (ob (natT 1)) (proj₂ R₀) (nfγ 0))
            (λ m Y hY lY e → proj₁ (Rg m Y hY lY e)) (λ m Y hY lY e → proj₂ (Rg m Y hY lY e))
            (λ m Y hY lY e → domP _ _ Iw′ bw (ob (γW ps (y ∷ ys) [] (suc m))) (proj₂ (Rg m Y hY lY e)) (nfγ (suc m)))
```

```agda
FW : Flr → T → PT → T → Set
FW φ ps y ys = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Ob w ps y ys

sB : ∀ {a b} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → suc a ⊑ᴵ suc b
sB (inj₁ (via e r)) = s⊑ e (suc r)
sB (inj₂ e)         = s⊑ e zero

_≼_ : Ordᴵ → Ordᴵ → Set
a ≼ b = (a ≺ᴵ b) ⊎ (a ≅ᴵ b)

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≼-trans (inj₁ s) (inj₁ s′) = inj₁ (≺ᴵ-trans s s′)
≼-trans (inj₁ s) (inj₂ e)  = inj₁ (≺ᴵ-respʳ s e)
≼-trans (inj₂ e) (inj₁ s)  = inj₁ (≺ᴵ-respˡ e s)
≼-trans (inj₂ e) (inj₂ e′) = inj₂ (≅ᴵ-trans e e′)

≼→≺s : ∀ {a b} → a ≼ b → a ≺ᴵ suc b
≼→≺s (inj₁ (via e r)) = via e (suc r)
≼→≺s (inj₂ e)         = via e zero

maxI : ∀ {w₀ w₁} (I₀ : Idx w₀) (I₁ : Idx w₁) → (lvI I₀ ≼ lvI I₁) ⊎ (lvI I₁ ≼ lvI I₀)
maxI {w₀} {w₁} I₀ I₁ with cmpᵀ w₀ w₁ in e
... | lt = inj₁ (inj₁ (Ilt I₀ I₁ (lt→< w₀ w₁ e)))
... | gt = inj₂ (inj₁ (Ilt I₁ I₀ (gt→< w₀ w₁ e)))
... | eq with eq→≡ w₀ w₁ e
...   | refl = inj₁ (inj₂ (Ieq I₀ I₁))

record Pick (P : T → Set) (φ : Flr) (Sk : ∀ {K} → InF K φ → Set) (c : Ordᴵ) : Set where
  constructor pk
  field
    pw  : T
    pI  : Idx pw
    pP  : P pw
    pc  : c ≼ lvI pI
    pF  : ∀ {K} (k : InF K φ) → Sk k ⊎ (K ≼ lvI pI)

pickMax : ∀ {P : T → Set} (φ : Flr) (Sk : ∀ {K} → InF K φ → Set) {c} →
          (∀ {K} (k : InF K φ) → Sk k ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × P w) →
          ∀ {w₀} (I₀ : Idx w₀) → P w₀ → c ≼ lvI I₀ → Pick P φ Sk c
pickMax fz      Sk wit I₀ p₀ c₀ = pk _ I₀ p₀ c₀ (λ ())
pickMax (fk K)  Sk wit I₀ p₀ c₀ with wit ink
... | inj₁ k0 = pk _ I₀ p₀ c₀ (λ { ink → inj₁ k0 })
... | inj₂ (w , Iw , kw , pw) with maxI I₀ Iw
...   | inj₁ le = pk w Iw pw (≼-trans c₀ le) (λ { ink → inj₂ kw })
...   | inj₂ le = pk _ I₀ p₀ c₀ (λ { ink → inj₂ (≼-trans kw le) })
pickMax (fb K)  Sk wit I₀ p₀ c₀ with wit inb
... | inj₁ k0 = pk _ I₀ p₀ c₀ (λ { inb → inj₁ k0 })
... | inj₂ (w , Iw , kw , pw) with maxI I₀ Iw
...   | inj₁ le = pk w Iw pw (≼-trans c₀ le) (λ { inb → inj₂ kw })
...   | inj₂ le = pk _ I₀ p₀ c₀ (λ { inb → inj₂ (≼-trans kw le) })
pickMax (a ⊔ b) Sk {c} wit I₀ p₀ c₀ =
  pk (Pick.pw B) (Pick.pI B) (Pick.pP B) (≼-trans (Pick.pc A′) (Pick.pc B))
     (λ { (inl k) → lftA (Pick.pF A′ k) ; (inr k) → Pick.pF B k })
  where
  A′ = pickMax a (λ k → Sk (inl k)) (λ k → wit (inl k)) I₀ p₀ c₀
  B  = pickMax b (λ k → Sk (inr k)) (λ k → wit (inr k)) (Pick.pI A′) (Pick.pP A′) (inj₂ (≅ᴵ-refl _))
  lftA : ∀ {K} {k : InF K a} → (Sk (inl k)) ⊎ (K ≼ lvI (Pick.pI A′)) → (Sk (inl k)) ⊎ (K ≼ lvI (Pick.pI B))
  lftA (inj₁ k0) = inj₁ k0
  lftA (inj₂ kw) = inj₂ (≼-trans kw (Pick.pc B))

Tr0 : ∀ {K φ} → InF K φ → Set
Tr0 {K} _ = K ≅ᴵ zero

evη : ∀ {i ℓ} (φ : Flr) (B : Top i ℓ (φ ⊔ fk zero)) η (e : Bd B ⊑ᴵ η) → Ev (Mlev (Fc B) (suc η) (FB B e)) (φ ⊔ fk η)
evη φ B η e = liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)

≺-of-⊑ : ∀ {a b} → suc a ⊑ᴵ b → a ≺ᴵ b
≺-of-⊑ (s⊑ e q) = via e q

module _ {φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ []) where

  domC : ∀ {ℓ Y} (hY : HS Y) (B : Top zero ℓ (φ ⊔ fk zero)) →
         ∀ θ → Lab Y (ψ₀ᵗ (ps ++ fsT (y ∷ ys) θ)) → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) θ)) → Bd B ⊑ᴵ toLevel Y hY
  domC hY B θ lY nf = ubd B (≺-of-⊑ (one⊑lab hY lY nf []<)) (λ k → dem k (dm k))
    where
    dm : ∀ {K} → InF K (φ ⊔ fk zero) → (K ≺ᴵ toLevel _ hY) ⊎ (K ≅ᴵ zero)
    dm k with fw k
    ... | inj₁ k0 = inj₂ k0
    ... | inj₂ (w′ , Iw′ , kw , ob′) = inj₁ (≺-of-⊑ (domP _ hY Iw′ (sB kw) (ob′ θ) lY nf))

  clo0 : L0 t (ps ++ fsT (y ∷ ys) (natT 1)) →
         (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → L0 (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
         L0 (cloA 0 t g) (ps ++ (y ∷ ys))
  clo0 h₀ hg ev p nu =
    ĉᴸ-mk nu cω′ K (proj₁ R₀) (subst (Lab _) (sym (gtW [] ps y ys [] cs refl 0)) (proj₂ R₀))
          (λ k → CCᴸ.Gg K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k)))
          (λ k → subst (Lab _) (sym (gtW [] ps y ys [] cs refl (suc k)))
                       (CCᴸ.lE K k (Ptᴸ.x (ptK K k)) (Ptᴸ.hx (ptK K k)) (Ptᴸ.lx (ptK K k)) (Ptᴸ.dx (ptK K k))))
    where
    B = bound (φ ⊔ fk zero) ev p
    cω′ = trans (cofW [] ps y ys) (cong (cofA []) cs)
    nfγ : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
    nfγ m = subst NF₁ (gtW [] ps y ys [] cs refl m) (NF₁-fsn nu cω′ m)
    R₀ = h₀ ev p (nfγ 0)
    Rg : ∀ m Y (hY : HS Y) → Lab Y (γW ps (y ∷ ys) [] (suc m)) → (e : Bd B ⊑ᴵ toLevel Y hY) →
         Lab₀ (g (toLevel Y hY) (evη φ B (toLevel Y hY) e) (lim 0 (iF B))) (γW ps (y ∷ ys) [] (suc (suc m)))
    Rg m Y hY lY e = hg _ Y hY lY (nfγ m) (1<γ ps y ys cs m) (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) (nfγ (suc m))
    K = ccᴸ (λ m → γW ps (y ∷ ys) [] (suc m)) (proj₁ R₀) (proj₂ R₀)
            (domC _ B (natT 1) (proj₂ R₀) (nfγ 0))
            (λ m Y hY lY e → proj₁ (Rg m Y hY lY e)) (λ m Y hY lY e → proj₂ (Rg m Y hY lY e))
            (λ m Y hY lY e → domC _ B (γW ps (y ∷ ys) [] (suc m)) (proj₂ (Rg m Y hY lY e)) (nfγ (suc m)))
```

## §9 地板标签与 $\Omega_\Omega$ 的闭包定理 (深度 0)

```agda
FlrLab : Flr → T → Set
FlrLab φ ps = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Occ w ps

FlrLab-mono : ∀ {φ ps qs} → (∀ {w} → Occ w ps → Occ w qs) → FlrLab φ ps → FlrLab φ qs
FlrLab-mono f F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , f o)

FlrLab-⊔ : ∀ {fl φ π x} → FlrLab fl π → FlrLab φ x → FlrLab (fl ⊔ φ) (π ++ x)
FlrLab-⊔ {x = x} F G (inl k) = FlrLab-mono (OccPre x) F k
FlrLab-⊔ {π = π} F G (inr k) = FlrLab-mono (OccΣ π) G k

FlrLab-fz : ∀ {ps} → FlrLab fz ps
FlrLab-fz ()

GA0 : ∀ {fl} → Run fl → T → Set
GA0 {fl} P π = FlrLab fl π × GR P π
```

## §12 边界
