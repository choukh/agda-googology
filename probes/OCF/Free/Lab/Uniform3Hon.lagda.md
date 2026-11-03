# Uniform3Hon (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform3Hon](../../Align/Uniform3Hon.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform3Hon where

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
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; addˢ; tr⁻ˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; cof-ne; fs-rep)
open import OCF.Free.Lab.StandardOmega using (NF₁)
open import OCF.Free.Lab.Decouple using (Idx; lvI)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base
open import OCF.Free.Lab.Uniform3Rel
open import OCF.Free.Lab.Uniform3SqABase
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.Stage2Label using (one⁰)
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Decouple using (Ilt; Ieq; kdI′; gtν; cofP)
open import OCF.Free.Lab.Bachmann using (pen→<; gt→≤)
open import OCF.Free.Lab.Closure using (Pen)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.OmegaExpBase using (πw; OccΣ; cofW; repW; ωW; γW; gtW; penW; H1W; ne-w; 1<γ)
open import OCF.Free.Lab.Uniform3Depth1 using (cωΩ; cΩΩ; penΩ)
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; cofA; 𝟏; trm; cmpᵀ; sucT; lt; eq; gt) renaming (ψ to ψᵗ)
```

## §1 首项

```agda
NB : T → Set
NB [] = ⊥
NB (x ∷ _ ∷ _) = ⊤
NB (ψᵗ u (_ ∷ _) ∷ []) = ⊤
NB (ψᵗ u [] ∷ []) = ⊥

NB-sum : ∀ {w} ps {y ys} → NB (ψᵗ w (ps ++ (y ∷ ys)) ∷ [])
NB-sum [] = tt
NB-sum (p ∷ ps) = tt

data Hu (u : T) : T → Set where
  hn : Hu u []
  hc : ∀ {v vs} → Hu u (ψᵗ u v ∷ vs)

Hu-rep : ∀ {u v} n → Hu u (replicate n (ψᵗ u v))
Hu-rep zero    = hn
Hu-rep (suc n) = hc

Hu-fsT₊ : ∀ u b c η → Hu u (E.fsT₊ u b c η)
Hu-fsT₊ u b c0 η = hc
Hu-fsT₊ u b c1 η = hc
Hu-fsT₊ u b cω η = hc
Hu-fsT₊ u b (cΩ ν) η = go (E.cmpᵀ (E.sucT ν) u)
  where
  go : ∀ m → Hu u (E.fsTc u b ν m η)
  go E.lt = hc
  go E.eq = hc
  go E.gt = hc

Hu-fsn₊ : ∀ u y ys n c (be : cof (y ∷ ys) ≡ c) → Hu u (trm (E.fsn↓₊ u y ys c be n))
Hu-fsn₊ u y ys n c0 be = hn
Hu-fsn₊ u y ys n c1 be = subst (Hu u) (sym (E.rep-trm u (E.pred-< (y ∷ ys) be) n)) (Hu-rep n)
Hu-fsn₊ u y ys n cω be = hc
Hu-fsn₊ u y ys n (cΩ ν) be = go (E.cmpᵀ (E.sucT ν) u)
  where
  go : ∀ m → Hu u (trm (E.fsn↓c u y ys ν be m n))
  go E.lt = hc
  go E.eq = hc
  go E.gt = hc

Hu-fsn : ∀ u v vs → NB (ψᵗ u v ∷ vs) → ∀ n → Hu u (fsn (ψᵗ u v ∷ vs) n)
Hu-fsn u v (z ∷ zs) nb n = hc
Hu-fsn u (y ∷ ys) [] nb n = Hu-fsn₊ u y ys n (cof (y ∷ ys)) refl

Hu-fsT : ∀ u v vs → NB (ψᵗ u v ∷ vs) → ∀ η → Hu u (fsT (ψᵗ u v ∷ vs) η)
Hu-fsT u v (z ∷ zs) nb η = hc
Hu-fsT u (y ∷ ys) [] nb η = Hu-fsT₊ u (y ∷ ys) (cof (y ∷ ys)) η

Hu-pred : ∀ u v vs → NB (ψᵗ u v ∷ vs) → cof (ψᵗ u v ∷ vs) ≡ c1 → Σ T λ v′ → Σ T λ vs′ → pred (ψᵗ u v ∷ vs) ≡ ψᵗ u v′ ∷ vs′
Hu-pred u v (z ∷ zs) nb c = v , pred (z ∷ zs) , refl
Hu-pred u (y ∷ ys) [] nb c = ⊥-elim (notc1 (cof (y ∷ ys)) c)
  where
  go′ : ∀ {ν} m → E.cofψ₊ u ν m ≡ c1 → ⊥
  go′ E.lt ()
  go′ E.eq ()
  go′ E.gt ()
  notc1 : ∀ c′ → cofA u c′ ≡ c1 → ⊥
  notc1 c0 ()
  notc1 c1 ()
  notc1 cω ()
  notc1 (cΩ ν) e = go′ (E.cmpᵀ (E.sucT ν) u) e
```

```agda
HK : Ordᴵ → T → Set
HK K []            = ⊤
HK K (ψᵗ u v ∷ vs) = Σ (Idx u) λ I → K ≼ lvI I

FH : Flr → T → Set
FH φ y = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ (K ≅ᴵ one) ⊎ HK K y

HK-Hu : ∀ {K u z} → (Σ (Idx u) λ I → K ≼ lvI I) → Hu u z → HK K z
HK-Hu h hn = tt
HK-Hu h hc = h

FH-fsn : ∀ {φ y} → NB y → FH φ y → ∀ n → FH φ (fsn y n)
FH-fsn {y = ψᵗ u v ∷ vs} nb F n k with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) = inj₂ (inj₂ (HK-Hu h (Hu-fsn u v vs nb n)))

FH-fsT : ∀ {φ y} → NB y → FH φ y → ∀ η → FH φ (fsT y η)
FH-fsT {y = ψᵗ u v ∷ vs} nb F η k with F k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) = inj₂ (inj₂ (HK-Hu h (Hu-fsT u v vs nb η)))
```

## §2 `Hn`

```agda
data Hn {ℓ} : Ordˢ ℓ → T → Set where
  hΩ : ∀ {x w} → x ≡ Ωˢ ℓ → (I : Idx w) → ℓ ≅ᴵ lvI I → Hn x (ψᵗ w [] ∷ [])
  hz : ∀ {t} → Hn Ord₊ˢ.zero t
  hs : ∀ {t y} → NB t → Hn y (pred t) → Hn (Ord₊ˢ.suc y) t
  hl : ∀ {t} {F : ℕ → Ordˢ ℓ} → NB t → (∀ n → Hn (F n) (fsn t n)) → Hn (Ord₊ˢ.lim F) t
  hi : ∀ {t j} {q : j <ᴵ ℓ} {f : Uˢ j (<→◃ q) → Ordˢ ℓ} → NB t →
       (∀ η (x : Ordˢ j) → LabL x η → Hn (f (intoˢ (<→◃ q) x)) (fsT t η)) → Hn (Ord₊ˢ.limᵢ q f) t
  hĉ : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → NB t → cof t ≡ cω →
       (K : CCᴸ c t₀ g) → LabL₊ ℓ Ll o₀ (fsn t 0) → Hn o₀ (fsn t 0) →
       (∀ k → LabL₊ ℓ Ll (o (lvK K k) (dxK K k)) (fsn t (suc k))) → (∀ k → Hn (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
       Hn (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t
  hŝ : ∀ {t c} {t₀ : Ordˢ ℓ} {g : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → NB t →
       Hn t₀ (fsT t (natT 1)) →
       (∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c ⊑ᴵ toLevel Y hY) →
        Hn (g (toLevel Y hY) e) (fsT t θ)) →
       Hn (Ord₊ˢ.ŝ c t₀ g) t
```

```agda
HSumA : ∀ {ℓ} {a : Ordˢ ℓ} {σ : Simᴵ zero ℓ} {b : Ordˢ zero} {x ys} → LabL₊ ℓ Ll a (x ∷ []) → Hn a (x ∷ []) → Lab0ᴸ b ys → Hn (addˢ a σ b) (x ∷ ys)
HSumA {ys = []} ga la (lz c) = la
HSumA {ys = y ∷ ys} ga la (lz c) = ⊥-elim (cof-ne y ys c)
HSumA {ys = []} ga la (ls () l)
HSumA {ys = y ∷ ys} ga la (ls c l) = hs tt (HSumA ga la l)
HSumA {ys = []} ga la (ll () h)
HSumA {ys = y ∷ ys} ga la (ll c h) = hl tt (λ n → HSumA ga la (h n))
HSumA {ys = []} ga la (lŝ₀ () K h₀ hk)
HSumA {ys = y ∷ ys} ga la (lŝ₀ c K h₀ hk) = hĉ tt c K (LSumA ga h₀) (HSumA ga la h₀) (λ m → LSumA ga (hk m)) (λ m → HSumA ga la (hk m))
HSumA {ys = []} ga la (lĉ () K h₀ hk)
HSumA {ys = y ∷ ys} ga la (lĉ c K h₀ hk) = hĉ tt c K (LSumA ga h₀) (HSumA ga la h₀) (λ m → LSumA ga (hk m)) (λ m → HSumA ga la (hk m))

HSum  : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabL₊ ℓ Ll a (x ∷ []) → Hn a (x ∷ []) → LabL b ys → Hn (addˢ a σ b) (x ∷ ys)
HSum₊ : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → kd ℓ ≡ false → LabL₊ ℓ Ll a (x ∷ []) → Hn a (x ∷ []) → LabL₊ k Ll b ys → Hn (addˢ a σ b) (x ∷ ys)
HSum {k = zero} kl ga la at = HSumA ga la (atomL at)
HSum {k = suc _} kl ga la h = HSum₊ kl ga la h
HSum {k = lim _ _} kl ga la h = HSum₊ kl ga la h
HSum₊ {ys = []} kl ga la (gz c) = la
HSum₊ {ys = y ∷ ys} kl ga la (gz c) = ⊥-elim (cof-ne y ys c)
HSum₊ {ys = []} kl ga la (gs () h)
HSum₊ {ys = y ∷ ys} kl ga la (gs c h) = hs tt (HSum₊ kl ga la h)
HSum₊ {ys = []} kl ga la (gl () h)
HSum₊ {ys = y ∷ ys} kl ga la (gl c h) = hl tt (λ n → HSum₊ kl ga la (h n))
HSum₊ {σ = σ} kl ga la (gu {r = zero} h) = HSum {σ = λ q → σ (suc q)} kl ga la h
HSum₊ {σ = σ} kl ga la (gu {r = self n} h) = HSum {σ = λ q → σ (lim n q)} kl ga la h
HSum₊ {ys = []} kl ga la (gi () I ej h)
HSum₊ {a = a} {σ = σ} {x = x} {ys = y ∷ ys} kl ga la (gi {q = q} {f = f} c I ej h) =
  hi tt (λ η w l → subst (λ v → Hn (addˢ a σ (f (intoˢ (<→◃ q) v))) (x ∷ fsT (y ∷ ys) η))
                         (sym (out-intoˢ (<→◃ (σ q)) w)) (HSum₊ kl ga la (h η w (→Ll (<→◃ q) l))))
HSum₊ {ys = []} kl ga la (gĉ () K h₀ hk)
HSum₊ {ys = y ∷ ys} kl ga la (gĉ c K h₀ hk) = hĉ tt c K (LSum₊ kl ga h₀) (HSum₊ kl ga la h₀) (λ m → LSum₊ kl ga (hk m)) (λ m → HSum₊ kl ga la (hk m))
HSum₊ {k = zero} kl ga la (gŝ () c Ib bb ob h₀ hg)
HSum₊ {k = suc _} {ys = []} kl ga la (gŝ kk () Ib bb ob h₀ hg)
HSum₊ {k = suc _} {ys = y ∷ ys} kl ga la (gŝ kk c Ib bb ob h₀ hg) =
  hŝ tt (HSum₊ kl ga la h₀) (λ θ Y hY lY nθ lt e → HSum₊ kl ga la (hg θ Y hY lY nθ lt e))
HSum₊ {k = lim _ _} {ys = []} kl ga la (gŝ kk () Ib bb ob h₀ hg)
HSum₊ {k = lim _ _} {ys = y ∷ ys} kl ga la (gŝ kk c Ib bb ob h₀ hg) =
  hŝ tt (HSum₊ kl ga la h₀) (λ θ Y hY lY nθ lt e → HSum₊ kl ga la (hg θ Y hY lY nθ lt e))

HRep : ∀ {ℓ} {P : Ordˢ ℓ} {x} → kd ℓ ≡ false → LabL₊ ℓ Ll P (x ∷ []) → Hn P (x ∷ []) → ∀ n →
       Hn (iter (P +ˢ_) Ord₊ˢ.zero n) (replicate n x)
HRep kl gP lP zero    = hz
HRep kl gP lP (suc n) = HSum₊ kl gP lP (LRep kl gP n)
```

## §3 输出的诚实性: 行引理

```agda
Out : ∀ {i} → Ordˢ i → T → Set
Out {i} x t = LabL₊ i Ll x t × Hn x t

LWʰ[_] : ∀ {φ} → Ordᴵ → Run φ → T → Set
LWʰ[_] {φ} c R u = ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up c i → Out (R ev p) (ψᵗ w u ∷ [])

LWʰ→ : ∀ {c φ} {R : Run φ} {u} → LWʰ[ c ] R u → LW[ c ] R u
LWʰ→ h ev p Iw ei ki u = proj₁ (h ev p Iw ei ki u)

wkLWʰ : ∀ {c φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → LWʰ[ c ] R u → LWʰ[ c ] (wk 0 le R) u
wkLWʰ le h ev p = h (le ev) p

module _ {c φ} {ps : T} {y : PT} {ys : T} where
  limWʰ : ∀ {F : ℕ → Run φ} → cof (y ∷ ys) ≡ cω → (∀ n → LWʰ[ c ] (F n) (ps ++ fsn (y ∷ ys) n)) →
          LWʰ[ c ] (limA 0 F) (ps ++ (y ∷ ys))
  limWʰ {F} cc h {w = w} ev p Iw ei ki u =
    limWᶜ {F = F} cc (λ n → LWʰ→ (h n)) ev p Iw ei ki u ,
    hl (NB-sum ps) (λ n → subst (Hn _) (sym (ωW w ps y ys cc n)) (proj₂ (h n ev p Iw ei ki u)))

  sucWʰ : ∀ {R : Run φ} → cof (y ∷ ys) ≡ c1 → LWʰ[ c ] R (ps ++ pred (y ∷ ys)) → LWʰ[ c ] (sucRun R) (ps ++ (y ∷ ys))
  sucWʰ {R} cc h {w = w} ev p Iw ei ki u =
    sucWᶜ {R = R} cc (LWʰ→ h) ev p Iw ei ki u ,
    hl (NB-sum ps) (λ m → subst (Hn _) (sym (repW w ps y ys cc m)) (HRep ki (proj₁ (h ev p Iw ei ki u)) (proj₂ (h ev p Iw ei ki u)) m))

module _ {c φ c₀ t₀} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {ps : T} {y : PT} {ys : T} where
  ĉWʰ : ∀ {O₀ : Run φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → Run φ} → cof (y ∷ ys) ≡ cω → (K : CCᴸ c₀ t₀ g) →
        LWʰ[ c ] O₀ (ps ++ fsn (y ∷ ys) 0) → (∀ k → LWʰ[ c ] (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) →
        LWʰ[ c ] (ĉA 0 c₀ t₀ g O₀ O) (ps ++ (y ∷ ys))
  ĉWʰ {O₀} {O} cw K h₀ hk {w = w} ev p Iw ei ki u =
    ĉWᶜ {O₀ = O₀} {O = O} cw K (LWʰ→ h₀) (λ k → LWʰ→ (hk k)) ev p Iw ei ki u ,
    hĉ (NB-sum ps) (trans (cofW w ps y ys) (cong (cofA w) cw)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw 0)) (proj₁ (h₀ ev p Iw ei ki u)))
       (subst (Hn _) (sym (ωW w ps y ys cw 0)) (proj₂ (h₀ ev p Iw ei ki u)))
       (λ k → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw (suc k))) (proj₁ (hk k ev p Iw ei ki u)))
       (λ k → subst (Hn _) (sym (ωW w ps y ys cw (suc k))) (proj₂ (hk k ev p Iw ei ki u)))

module _ {c φ c₀ w′} {ps : T} {y : PT} {ys : T} {T₀ : Run φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → Run φ}
         (cs : cof (y ∷ ys) ≡ cΩ []) (Iw′ : Idx w′) (bw : c₀ ⊑ᴵ suc (lvI Iw′)) (ob : Ob w′ ps y ys) where
  ŝWʰ : LWʰ[ c ] T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
        (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → LWʰ[ c ] (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
        LWʰ[ c ] (ŝA 0 c₀ T₀ G) (ps ++ (y ∷ ys))
  ŝWʰ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  ŝWʰ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    ŝWᶜ cs Iw′ bw ob (LWʰ→ h₀) (λ θ Y hY lY nθ lt e → LWʰ→ (hg θ Y hY lY nθ lt e)) ev p Iw ei ki u ,
    hŝ (NB-sum ps)
       (subst (Hn _) (sym (H1W x xs ps y ys cs (natT 1))) (proj₂ (h₀ ev p Iw ei ki u)))
       (λ θ Y hY lY nθ lt e → subst (Hn _) (sym (H1W x xs ps y ys cs θ)) (proj₂ (hg θ Y hY lY nθ lt e ev p Iw ei ki u)))

module _ {c φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW[ c ] (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ []) where
  cloWʰ : LWʰ[ c ] t (ps ++ fsT (y ∷ ys) (natT 1)) →
          (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → LWʰ[ c ] (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
          LWʰ[ c ] (cloA 0 t g) (ps ++ (y ∷ ys))
  cloWʰ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  cloWʰ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    cloWᵗ {t = t} {g = g} fw cs (LWʰ→ h₀) (λ θ Y hY lY nθ lt → LWʰ→ (hg θ Y hY lY nθ lt)) ev p Iw ei ki u ,
    hŝ (NB-sum ps)
       (subst (Hn _) (sym (H1W x xs ps y ys cs (natT 1))) (proj₂ (h₀ ev p Iw ei ki u)))
       (λ θ Y hY lY nθ lt e → subst (Hn _) (sym (H1W x xs ps y ys cs θ))
            (proj₂ (hg θ Y hY lY nθ lt (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) Iw ei ki u)))
    where
    B = bound (φ ⊔ fk zero) ev p
```

```agda
module _ {c φ j ν} {ps : T} {y : PT} {ys : T} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ}
         (cc : cof (y ∷ ys) ≡ cΩ ν) (Iν : Idx ν) (ej : j ≅ᴵ lvI Iν) where

  limᵢWᴾ : (Inp : T → Ordˢ j → Set) → Inp (Ωt ν) (Ωˢ j) →
           (∀ η x → LabL x η → ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up c i → j ≺ᴵ i →
            Out (H x ev p) (ψᵗ w (ps ++ fsT (y ∷ ys) η) ∷ [])) →
           (∀ {η x} → Inp η x → kd j ≡ false → Up c j → ∀ {ℓ} (ev : Ev ℓ φ) → Inp (πw ν ps (fsT (y ∷ ys) η)) (H x ev (ac ev))) →
           (∀ {η x} → Inp η x → LWʰ[ c ] (H x) (ps ++ fsT (y ∷ ys) η)) →
           LWʰ[ c ] (limᵢA 0 ac H) (ps ++ (y ∷ ys))
  limᵢWᴾ Inp i₀ hPen hStep hOut {i = i} {w = w} ev p Iw ei ki u = go (cmpᵀ (sucT ν) w) refl
    where
    pen : Pen (cmpᵀ (sucT ν) w) → Out (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    pen pn with pen1A {ac = ac} {H = H} {ev = ev} {p = p} (≅ᴵ-refl j) jsi
      where
      jsi : j ≺ᴵ i
      jsi = ≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei)
    ... | j′ , e , r , eqn =
      subst (λ W → Out W (πw w ps (y ∷ ys))) (sym eqn)
        (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
            (λ η x l → subst (λ v → LabL₊ i Ll (H (tr⁻ˢ e v) ev p) (fsT (πw w ps (y ∷ ys)) η))
                             (sym (out-intoˢ (<→◃ r) x))
                             (subst (LabL₊ i Ll _) (sym (penW w ps y ys ν cc pn η))
                                    (proj₁ (hPen η (tr⁻ˢ e x) (LabL-tr⁻ e (Ll→ (<→◃ r) l)) ev p Iw ei ki u jsi′)))) ,
         hi (NB-sum ps)
            (λ η x l → subst (λ v → Hn (H (tr⁻ˢ e v) ev p) (fsT (πw w ps (y ∷ ys)) η))
                             (sym (out-intoˢ (<→◃ r) x))
                             (subst (Hn _) (sym (penW w ps y ys ν cc pn η))
                                    (proj₂ (hPen η (tr⁻ˢ e x) (LabL-tr⁻ e l) ev p Iw ei ki u jsi′)))))
      where
      cofE : cof (πw w ps (y ∷ ys)) ≡ cΩ ν
      cofE = trans (cofW w ps y ys) (trans (cong (cofA w) cc) (cofP pn))
      jsi′ : j ≺ᴵ i
      jsi′ = ≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei)
    fld : cmpᵀ (sucT ν) w ≡ gt → Out (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    fld em =
      subst (λ W → Out W (πw w ps (y ∷ ys))) (sym (fold1A {ac = ac} {H = H} {ev = ev} {p = p} ij))
        (gl (trans (cofW w ps y ys) (trans (cong (cofA w) cc) (cong (E.cofψ₊ w ν) em)))
            (λ m → subst (LabL₊ i Ll _) (sym (gtW w ps y ys ν cc em m)) (proj₁ (hOut (chainI m) ev p Iw ei ki u))) ,
         hl (NB-sum ps) (λ m → subst (Hn _) (sym (gtW w ps y ys ν cc em m)) (proj₂ (hOut (chainI m) ev p Iw ei ki u))))
      where
      gev : (lvI Iw ≺ᴵ lvI Iν) ⊎ (lvI Iw ≅ᴵ lvI Iν)
      gev with gt→≤ ν w em
      ... | inj₁ pw   = inj₁ (Ilt Iw Iν pw)
      ... | inj₂ refl = inj₂ (Ieq Iw Iν)
      ij : (i ≺ᴵ j) ⊎ (i ≅ᴵ j)
      ij with gev
      ... | inj₁ s  = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ ei s) (≅ᴵ-sym ej))
      ... | inj₂ c′ = inj₂ (≅ᴵ-trans ei (≅ᴵ-trans c′ (≅ᴵ-sym ej)))
      kj : kd j ≡ false
      kj = trans (kd-≅ ej) (kdI′ Iν (gtν em (ne-w Iw ei ki)))
      uj : Up c j
      uj = Up-ij u ij
      chainI : ∀ m → Inp (γW ps (y ∷ ys) ν m) (chainA ac H ev m)
      chainI zero    = i₀
      chainI (suc m) = hStep (chainI m) kj uj ev
    go : ∀ m → cmpᵀ (sucT ν) w ≡ m → Out (limᵢA 0 ac H ev p) (πw w ps (y ∷ ys))
    go E.lt em = pen (inj₁ em)
    go E.eq em = pen (inj₂ em)
    go E.gt em = fld em
```

## §6 $\Omega_\Omega$ 闭包
