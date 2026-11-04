# Decouple (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZDecouple](LadderLabZDecouple.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZDecouple where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; coeˢ; toZ; Ωˢ; addˢ; _+ˢ_; ψᴾ; Restrˢ; trˢ; tr⁻ˢ; resˢ; res⁻ˢ; Goodᶻ; force; force-HS)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω; fsT-c1)
open import OCF.Align.OrdLabZBachmann using (fs-gt; pen→<; gt→≤; gt→<; clash)
open import OCF.Align.OrdLabZClosure using (Pen; fsT₊-pen′)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-pred; NF₁-fsn; γ′-NF)
open import OCF.Align.OrdLabZStage2 using (Lab-uniq)
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZStage2Label using (chain0; Lab-oc; X₂ᶠ; GX₂)
open import OCF.Align.OrdLabZDecoupleBase
open import OCF.Align.OrdLabZSymbolic using (X₂ᵗ)
open import OCF.Align.OrdLabZLabel using (BTBO-label)
import OCF.Align.OrdLabZNoCumsum as N
import Data.List
```

```agda
open Ord-Ord using (iter)
open Restrˢ
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt; []<; hd<; tl<; lv<; ar<)
  renaming (ψ to ψᵗ)
```

## §2 带标签的下标

```agda
Idx : T → Set
Idx ν = Σ (Ordᶜ zero) λ Y → Σ (HS Y) λ hY → Lab Y ν × NF₁ ν

lvI : ∀ {ν} → Idx ν → Ordᴵ
lvI (Y , hY , _) = toLevel Y hY

Ilt : ∀ {v u} (Iv : Idx v) (Iu : Idx u) → v <ᵀ u → lvI Iv ≺ᴵ lvI Iu
Ilt (Y , hY , lY , nY) (X , hX , lX , nX) p = toLevel-≺ hY hX (Lab-oc lX nX lY nY p)

Ieq : ∀ {u} (I I′ : Idx u) → lvI I ≅ᴵ lvI I′
Ieq (Y , hY , lY , _) (X , hX , lX , _) = toLevel-≅ hY hX (Lab-uniq lY lX)

Lab0[] : ∀ {ν} → Lab Ord₊.zero ν → ν ≡ []
Lab0[] {ν = []} l = refl
Lab0[] {ν = y ∷ ys} (l0 c e) = ⊥-elim (cof-ne y ys c)
Lab0[] {ν = y ∷ ys} (l1 c () l)
Lab0[] {ν = y ∷ ys} (lω c () h)

kdI : ∀ {ν} (I : Idx ν) → kd (lvI I) ≡ true → ν ≡ []
kdI (Ord₊.zero , hY , lY , nY) k = Lab0[] lY
kdI (Ord₊.suc Y , hY , lY , nY) ()
kdI (Ord₊.lim F , hY , lY , nY) ()
kdI (Ord₊.limᵢ () f , hY , lY , nY) k
kdI (Ord₊.up () x , hY , lY , nY) k

kdI′ : ∀ {ν} (I : Idx ν) → (ν ≡ [] → ⊥) → kd (lvI I) ≡ false
kdI′ (Ord₊.zero , hY , lY , nY) ne = ⊥-elim (ne (Lab0[] lY))
kdI′ (Ord₊.suc Y , hY , lY , nY) ne = refl
kdI′ (Ord₊.lim F , hY , lY , nY) ne = refl
kdI′ (Ord₊.limᵢ () f , hY , lY , nY) ne
kdI′ (Ord₊.up () x , hY , lY , nY) ne

<1→[] : ∀ {w} → w <ᵀ natT 1 → w ≡ []
<1→[] []< = refl
<1→[] (hd< (lv< ()))
<1→[] (hd< (ar< ()))
<1→[] (tl< ())

gtν : ∀ {ν w} → cmpᵀ (sucT ν) w ≡ gt → (w ≡ [] → ⊥) → ν ≡ [] → ⊥
gtν {ν = []} {w = w} em ne refl = ne (<1→[] (gt→< (natT 1) w em))
```

## §3 全层级的关系式遗传标签 `LabG`

```agda
module _ (ℓ : Ordᴵ) (L< : (j : Ordᴵ) (r : j ◃ ℓ) → Uˢ j r → T → Set) where
  data LabG₊ : Ordˢ ℓ → T → Set where
    gz : ∀ {t} → cof t ≡ c0 → LabG₊ Ord₊ˢ.zero t
    gs : ∀ {t y} → cof t ≡ c1 → LabG₊ y (pred t) → LabG₊ (Ord₊ˢ.suc y) t
    gl : ∀ {t} {F : ℕ → Ordˢ ℓ} → cof t ≡ cω → (∀ n → LabG₊ (F n) (fsn t n)) → LabG₊ (Ord₊ˢ.lim F) t
    gu : ∀ {t k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} → L< k (◃₁→◃ r) x t → LabG₊ (Ord₊ˢ.up r x) t
    gi : ∀ {t ν j} {q : j <ᴵ ℓ} {f : Uˢ j (<→◃ q) → Ordˢ ℓ} → cof t ≡ cΩ ν → (I : Idx ν) → j ≅ᴵ lvI I →
         (∀ η (x : Ordˢ j) → L< j (<→◃ q) (intoˢ (<→◃ q) x) η → LabG₊ (f (intoˢ (<→◃ q) x)) (fsT t η)) →
         LabG₊ (Ord₊ˢ.limᵢ q f) t
    gĉ : ∀ {t c t₀} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {o₀ : Ordˢ ℓ} {o : (η : Ordᴵ) → c ⊑ᴵ η → Ordˢ ℓ} → cof t ≡ cω →
         (∀ (K : CC c t₀ g) → LabG₊ o₀ (fsn t 0)) →
         (∀ (K : CC c t₀ g) k → LabG₊ (o (lvK K k) (dxK K k)) (fsn t (suc k))) →
         LabG₊ (Ord₊ˢ.ĉᴸ c t₀ g o₀ o) t

LvG : (i : Ordᴵ) → ((j : Ordᴵ) (r : j ◃ i) → Uˢ j r → T → Set) → Ordˢ i → T → Set
LvG zero      L x t = Atom x t
LvG (suc i)   L x t = LabG₊ (suc i) L x t
LvG (lim f s) L x t = LabG₊ (lim f s) L x t

Lg : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → T → Set
Lg i zero         x t = LvG i Lg x t
Lg i (suc r)      x t = Lg i r x t
Lg _ (self {f} n) x t = LvG (f n) Lg x t
Lg i (lim n r)    x t = Lg i r x t

LabG : ∀ {ℓ} → Ordˢ ℓ → T → Set
LabG {ℓ} x t = LvG ℓ Lg x t
```

```agda
Lg→ : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → Lg i r (intoˢ r x) t → LabG x t
Lg→ zero      h = h
Lg→ (suc r)   h = Lg→ r h
Lg→ (self n)  h = h
Lg→ (lim n r) h = Lg→ r h

→Lg : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordˢ i} {t} → LabG x t → Lg i r (intoˢ r x) t
→Lg zero      h = h
→Lg (suc r)   h = →Lg r h
→Lg (self n)  h = h
→Lg (lim n r) h = →Lg r h

toG₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabG x t → LabG₊ i Lg x t
toG₊ {i = zero}    () h
toG₊ {i = suc _}   k h = h
toG₊ {i = lim _ _} k h = h

frG₊ : ∀ {i} {x : Ordˢ i} {t} → kd i ≡ false → LabG₊ i Lg x t → LabG x t
frG₊ {i = zero}    () h
frG₊ {i = suc _}   k h = h
frG₊ {i = lim _ _} k h = h

Atom-≅ : ∀ {x y : Ordˢ zero} {θ} → Atom x θ → y ≅ˢ x → Atom y θ
Atom-≅ (ex , G , l) d = ≅ˢ-reflˡ d , Goodᶻ-tr (toZ-≅ (≅ˢ-sym d)) G , Lab-≅ (force-≅ (toZ-≅ d) _ G) l
```

## §4 沿 $\cong^\mathsf I$ 搬运

```agda
LabG-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabG x t → LabG (trˢ e x) t
LabG-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabG x t → LabG (tr⁻ˢ e x) t
LabG-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {t} → LabG u t → LabG (backˢ (resˢ q e) u) t
LabG-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {t} → LabG u t → LabG (backˢ (res⁻ˢ q e) u) t
G-tr  : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ a} {t} → LabG₊ a Lg x t → LabG₊ b Lg (trˢ e x) t
G-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordˢ b} {t} → LabG₊ b Lg x t → LabG₊ a Lg (tr⁻ˢ e x) t

LabG-tr z≅ at = Atom-≅ at (trˢ-≅ z≅ (proj₁ at))
LabG-tr (s≅ e) h = G-tr (s≅ e) h
LabG-tr (l≅ k) h = G-tr (l≅ k) h
LabG-tr⁻ z≅ at = Atom-≅ at (tr⁻ˢ-≅ z≅ (proj₁ at))
LabG-tr⁻ (s≅ e) h = G-tr⁻ (s≅ e) h
LabG-tr⁻ (l≅ k) h = G-tr⁻ (l≅ k) h

G-tr e (gz c)   = gz c
G-tr e (gs c h) = gs c (G-tr e h)
G-tr e (gl c h) = gl c (λ n → G-tr e (h n))
G-tr (s≅ e) (gu {r = zero} h)   = gu (LabG-tr e h)
G-tr (l≅ k) (gu {r = self n} h) = gu (LabG-tr (k n) h)
G-tr e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej)
     (λ η x l → subst (λ v → LabG₊ _ Lg (trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) x))
                      (G-tr e (h η (backˢ (resˢ q e) x) (→Lg (<→◃ q) (LabG-back q e (Lg→ (<→◃ (ltˢ (resˢ q e))) l))))))
G-tr e (gĉ c h₀ hk) = gĉ c (λ K → G-tr e (h₀ K)) (λ K k → G-tr e (hk K k))

G-tr⁻ e (gz c)   = gz c
G-tr⁻ e (gs c h) = gs c (G-tr⁻ e h)
G-tr⁻ e (gl c h) = gl c (λ n → G-tr⁻ e (h n))
G-tr⁻ (s≅ e) (gu {r = zero} h)   = gu (LabG-tr⁻ e h)
G-tr⁻ (l≅ k) (gu {r = self n} h) = gu (LabG-tr⁻ (k n) h)
G-tr⁻ e {t = t} (gi {q = q} {f = f} c I ej h) =
  gi c I (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej)
     (λ η x l → subst (λ v → LabG₊ _ Lg (tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) v)))) (fsT t η))
                      (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) x))
                      (G-tr⁻ e (h η (backˢ (res⁻ˢ q e) x) (→Lg (<→◃ q) (LabG-back⁻ q e (Lg→ (<→◃ (ltˢ (res⁻ˢ q e))) l))))))
G-tr⁻ e (gĉ c h₀ hk) = gĉ c (λ K → G-tr⁻ e (h₀ K)) (λ K k → G-tr⁻ e (hk K k))

LabG-back zero      (s≅ e) h = LabG-tr⁻ e h
LabG-back (suc q)   (s≅ e) h = LabG-back q e h
LabG-back (lim n q) (l≅ k) h = LabG-back q (k n) h

LabG-back⁻ zero      (s≅ e) h = LabG-tr e h
LabG-back⁻ (suc q)   (s≅ e) h = LabG-back⁻ q e h
LabG-back⁻ (lim n q) (l≅ k) h = LabG-back⁻ q (k n) h
```

## §5 带标签的层号上的 $\Omega$

```agda
LabG-Ω : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {a} → a ≅ᴵ toLevel Y hY → LabG (Ωˢ a) (Ωt θ)
LabG-Ω {θ = []} Ord₊.zero hY l nθ z≅ = Ωˢ-refl zero , Goodᶻ.gs Goodᶻ.gz , l1 refl (s≅ z≅) (l0 refl z≅)
LabG-Ω {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ with Lab0[] l
... | ()
LabG-Ω {θ = θ} (Ord₊.suc Y) hY (l0 c ()) nθ (s≅ e)
LabG-Ω {θ = θ} (Ord₊.suc Y) hY (lω c () h) nθ (s≅ e)
LabG-Ω {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e)
LabG-Ω {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c (s≅ e′) l) nθ (s≅ e) =
  gi (cong (E.cofψ0 (w ∷ ws)) c) (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c) e
     (λ η x lx → gu (subst (LabG x) (sym (fsT-c1 (w ∷ ws) (cof (w ∷ ws)) c η)) lx))
LabG-Ω {θ = θ} (Ord₊.lim F) hY (l0 c ()) nθ (l≅ k)
LabG-Ω {θ = θ} (Ord₊.lim F) hY (l1 c () l) nθ (l≅ k)
LabG-Ω {θ = []} (Ord₊.lim F) hY (lω () (l≅ k′) h) nθ (l≅ k)
LabG-Ω {θ = w ∷ ws} (Ord₊.lim F) hY (lω c (l≅ k′) h) nθ (l≅ k) =
  gl (cong (E.cofψ0 (w ∷ ws)) c)
     (λ n → gu (subst (LabG _) (sym (E.fsn0-eq w ws n c))
                      (LabG-Ω (F n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c n) (k n))))
LabG-Ω (Ord₊.limᵢ () f) hY l nθ e
LabG-Ω (Ord₊.up () x) hY l nθ e
```

## §6 和

```agda
GSumA : ∀ {ℓ} {a : Ordˢ ℓ} {σ : Simᴵ zero ℓ} {b : Ordˢ zero} {x ys} → LabG₊ ℓ Lg a (x ∷ []) → Lab₁ b ys →
        LabG₊ ℓ Lg (addˢ a σ b) (x ∷ ys)
GSumA {ys = []} la (lz c) = la
GSumA {ys = y ∷ ys} la (lz c) = ⊥-elim (cof-ne y ys c)
GSumA {ys = []} la (ls () l)
GSumA {ys = y ∷ ys} la (ls c l) = gs c (GSumA la l)
GSumA {ys = []} la (ll () h)
GSumA {ys = y ∷ ys} la (ll c h) = gl c (λ n → GSumA la (h n))
GSumA la (lu {r = ()} l)
GSumA la (li {q = ()} c h)
GSumA la (lŝ () c h₀ hg)
GSumA {ys = []} la (lŝ₀ () h₀ hk)
GSumA {ys = y ∷ ys} la (lŝ₀ c h₀ hk) = gĉ c (λ K → GSumA la (h₀ K)) (λ K m → GSumA la (hk K m))
GSumA {ys = []} la (lĉ () h₀ hk)
GSumA {ys = y ∷ ys} la (lĉ c h₀ hk) = gĉ c (λ K → GSumA la (h₀ K)) (λ K m → GSumA la (hk K m))

GSum  : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → LabG₊ ℓ Lg a (x ∷ []) → LabG b ys →
        LabG₊ ℓ Lg (addˢ a σ b) (x ∷ ys)
GSum₊ : ∀ {k ℓ} {a : Ordˢ ℓ} {σ : Simᴵ k ℓ} {b : Ordˢ k} {x ys} → LabG₊ ℓ Lg a (x ∷ []) → LabG₊ k Lg b ys →
        LabG₊ ℓ Lg (addˢ a σ b) (x ∷ ys)
GSum {k = zero} la at = GSumA la (atomL at)
GSum {k = suc _} la h = GSum₊ la h
GSum {k = lim _ _} la h = GSum₊ la h
GSum₊ {ys = []} la (gz c) = la
GSum₊ {ys = y ∷ ys} la (gz c) = ⊥-elim (cof-ne y ys c)
GSum₊ {ys = []} la (gs () h)
GSum₊ {ys = y ∷ ys} la (gs c h) = gs c (GSum₊ la h)
GSum₊ {ys = []} la (gl () h)
GSum₊ {ys = y ∷ ys} la (gl c h) = gl c (λ n → GSum₊ la (h n))
GSum₊ {σ = σ} la (gu {r = zero} h) = GSum {σ = λ q → σ (suc q)} la h
GSum₊ {σ = σ} la (gu {r = self n} h) = GSum {σ = λ q → σ (lim n q)} la h
GSum₊ {ys = []} la (gi () I ej h)
GSum₊ {a = a} {σ = σ} {x = x} {ys = y ∷ ys} la (gi {q = q} {f = f} c I ej h) =
  gi c I ej (λ η w l → subst (λ v → LabG₊ _ Lg (addˢ a σ (f (intoˢ (<→◃ q) v))) (x ∷ fsT (y ∷ ys) η))
                             (sym (out-intoˢ (<→◃ (σ q)) w))
                             (GSum₊ la (h η w (→Lg (<→◃ q) (Lg→ (<→◃ (σ q)) l)))))
GSum₊ {ys = []} la (gĉ () h₀ hk)
GSum₊ {ys = y ∷ ys} la (gĉ c h₀ hk) = gĉ c (λ K → GSum₊ la (h₀ K)) (λ K m → GSum₊ la (hk K m))

GRep : ∀ {ℓ} {P : Ordˢ ℓ} {x} → LabG₊ ℓ Lg P (x ∷ []) → ∀ n → LabG₊ ℓ Lg (iter (P +ˢ_) Ord₊ˢ.zero n) (replicate n x)
GRep lP zero    = gz refl
GRep lP (suc n) = GSum₊ lP (GRep lP n)
```

## §7 派发

```agda
fold0 : ∀ {i k ℓ j} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → ψ0 p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.lim (λ m → ψ0 p σ (f (intoˢ (<→◃ q) (chain0 σ q f m))))
fold0 {p = p} {σ = σ} {q = q} h with <ᴵ-dec (σ q) p
... | injᵃ s = ⊥-elim (clash s h)
... | injᵇ _ = refl
... | injᶜ _ = refl

pen0 : ∀ {i k ℓ j N} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
       j ≅ᴵ N → N ≺ᴵ i →
       Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
       ψ0 p σ (Ord₊ˢ.limᵢ q f) ≡ Ord₊ˢ.limᵢ r (λ y → ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
pen0 {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))

kdI[] : (I : Idx []) → kd (lvI I) ≡ true
kdI[] (Ord₊.zero , hY , lY , nY) = refl
kdI[] (Ord₊.suc Y , hY , l0 c () , nY)
kdI[] (Ord₊.suc Y , hY , l1 () e l , nY)
kdI[] (Ord₊.suc Y , hY , lω () e h , nY)
kdI[] (Ord₊.lim F , hY , l0 c () , nY)
kdI[] (Ord₊.lim F , hY , l1 () e l , nY)
kdI[] (Ord₊.lim F , hY , lω () e h , nY)
kdI[] (Ord₊.limᵢ () f , hY , lY , nY)
kdI[] (Ord₊.up () x , hY , lY , nY)

cofP : ∀ {w ν} → Pen (cmpᵀ (sucT ν) w) → E.cofψ₊ w ν (cmpᵀ (sucT ν) w) ≡ cΩ ν
cofP {w} {ν} (inj₁ em) = cong (E.cofψ₊ w ν) em
cofP {w} {ν} (inj₂ em) = cong (E.cofψ₊ w ν) em

-- the Ω_{ν+1}-row of ψ_w, given the two recursive calls as oracles
giPsi : ∀ {k ℓ i w ν j y ys} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {q : j <ᴵ k} {f : Uˢ j (<→◃ q) → Ordˢ k} →
        (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
        (rec : ∀ η (x : Ordˢ j) → LabG x η → LabG₊ i Lg (ψ0 p σ (f (intoˢ (<→◃ q) x))) (ψᵗ w (fsT (y ∷ ys) η) ∷ [])) →
        (recC : kd j ≡ false → ∀ η (x : Ordˢ j) → LabG x η →
                LabG₊ j Lg (ψ0 (σ q) σ (f (intoˢ (<→◃ q) x))) (ψᵗ ν (fsT (y ∷ ys) η) ∷ [])) →
        LabG₊ i Lg (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
giPsi {i = i} {w = w} {ν = ν} {j = j} {y = y} {ys = ys} {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej rec recC =
  go (cmpᵀ (sucT ν) w) refl
  where
  pen : Pen (cmpᵀ (sucT ν) w) → LabG₊ i Lg (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  pen pn with pen0 {p = p} {σ = σ} {q = q} {f = f} (≅ᴵ-refl j)
                   (≺ᴵ-respʳ (≺ᴵ-respˡ ej (Ilt Iν Iw (pen→< ν w pn))) (≅ᴵ-sym ei))
  ... | j′ , e , r , eqn =
    subst (λ W → LabG₊ i Lg W (ψᵗ w (y ∷ ys) ∷ [])) (sym eqn)
          (gi cofE Iν (≅ᴵ-trans (≅ᴵ-sym e) ej)
              (λ η x l → subst (λ v → LabG₊ i Lg (ψ0 p σ (f (intoˢ (<→◃ q) (tr⁻ˢ e v)))) (fsT (ψᵗ w (y ∷ ys) ∷ []) η))
                               (sym (out-intoˢ (<→◃ r) x))
                               (subst (LabG₊ i Lg _) (sym (fsT₊-pen′ w (y ∷ ys) ν (cof (y ∷ ys)) c pn η))
                                      (rec η (tr⁻ˢ e x) (LabG-tr⁻ e (Lg→ (<→◃ r) l))))))
    where
    cofE : cof (ψᵗ w (y ∷ ys) ∷ []) ≡ cΩ ν
    cofE = trans (cong (E.cofA w) c) (cofP pn)
  ne-w : w ≡ [] → ⊥
  ne-w refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
  fold : cmpᵀ (sucT ν) w ≡ gt → LabG₊ i Lg (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  fold em =
    subst (λ W → LabG₊ i Lg W (ψᵗ w (y ∷ ys) ∷ [])) (sym (fold0 {p = p} {σ = σ} {q = q} {f = f} ij))
          (gl (trans (cong (E.cofA w) c) (cong (E.cofψ₊ w ν) em))
              (λ m → subst (LabG₊ i Lg _) (sym (fs-gt w y ys ν c em m)) (rec _ _ (chainL m))))
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
    kj = trans (kd-≅ ej) (kdI′ Iν (gtν em ne-w))
    chainL : ∀ m → LabG (chain0 σ q f m) (γT (y ∷ ys) ν m)
    chainL zero    = LabG-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
    chainL (suc m) = frG₊ kj (recC kj _ _ (chainL m))
  go : ∀ m → cmpᵀ (sucT ν) w ≡ m → LabG₊ i Lg (ψ0 p σ (Ord₊ˢ.limᵢ q f)) (ψᵗ w (y ∷ ys) ∷ [])
  go lt em = pen (inj₁ em)
  go eq em = pen (inj₂ em)
  go gt em = fold em
```

## §8 不带前缀的 $\psi_w$ 的上下文引理

```agda
PsiA : ∀ {ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ zero ℓ} {X : Ordˢ zero} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
       Lab₁ X b → LabG₊ i Lg (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiA {b = []} (Y , hY , lY , nY) ei ki (lz c) = toG₊ ki (LabG-Ω Y hY lY nY ei)
PsiA {b = y ∷ ys} Iw ei ki (lz c) = ⊥-elim (cof-ne y ys c)
PsiA {b = []} Iw ei ki (ls () l)
PsiA {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ls c l) =
  gl (cong (E.cofA w) c) (λ n → subst (LabG₊ _ Lg _) (sym (fs-rep w y ys c n)) (GRep (PsiA {p = p} {σ = σ} Iw ei ki l) n))
PsiA {b = []} Iw ei ki (ll () h)
PsiA {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (ll c h) =
  gl (cong (E.cofA w) c) (λ n → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c n)) (PsiA {p = p} {σ = σ} Iw ei ki (h n)))
PsiA Iw ei ki (lu {r = ()} l)
PsiA Iw ei ki (li {q = ()} c h)
PsiA Iw ei ki (lŝ () c h₀ hg)
PsiA {b = []} Iw ei ki (lŝ₀ () h₀ hk)
PsiA {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lŝ₀ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c 0)) (PsiA {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c (suc m))) (PsiA {p = p} {σ = σ} Iw ei ki (hk K m)))
PsiA {b = []} Iw ei ki (lĉ () h₀ hk)
PsiA {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (lĉ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c 0)) (PsiA {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c (suc m))) (PsiA {p = p} {σ = σ} Iw ei ki (hk K m)))

PsiV  : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
        LabG X b → LabG₊ i Lg (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiG₊ : ∀ {k ℓ i w} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {X : Ordˢ k} {b} (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false →
        LabG₊ k Lg X b → LabG₊ i Lg (ψ0 p σ X) (ψᵗ w b ∷ [])
PsiV {k = zero}    {p = p} {σ = σ} Iw ei ki at = PsiA {p = p} {σ = σ} Iw ei ki (atomL at)
PsiV {k = suc _}   {p = p} {σ = σ} Iw ei ki h  = PsiG₊ {p = p} {σ = σ} Iw ei ki h
PsiV {k = lim _ _} {p = p} {σ = σ} Iw ei ki h  = PsiG₊ {p = p} {σ = σ} Iw ei ki h

PsiG₊ {b = []} (Y , hY , lY , nY) ei ki (gz c) = toG₊ ki (LabG-Ω Y hY lY nY ei)
PsiG₊ {b = y ∷ ys} Iw ei ki (gz c) = ⊥-elim (cof-ne y ys c)
PsiG₊ {b = []} Iw ei ki (gs () l)
PsiG₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gs c l) =
  gl (cong (E.cofA w) c) (λ n → subst (LabG₊ _ Lg _) (sym (fs-rep w y ys c n)) (GRep (PsiG₊ {p = p} {σ = σ} Iw ei ki l) n))
PsiG₊ {b = []} Iw ei ki (gl () h)
PsiG₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gl c h) =
  gl (cong (E.cofA w) c) (λ n → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c n)) (PsiG₊ {p = p} {σ = σ} Iw ei ki (h n)))
PsiG₊ {p = p} {σ = σ} Iw ei ki (gu {r = zero} h)   = PsiV {p = p} {σ = λ q → σ (suc q)} Iw ei ki h
PsiG₊ {p = p} {σ = σ} Iw ei ki (gu {r = self n} h) = PsiV {p = p} {σ = λ q → σ (lim n q)} Iw ei ki h
PsiG₊ {b = []} Iw ei ki (gi () Iν ej h)
PsiG₊ {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gi {q = q} {f = f} c Iν ej h) =
  giPsi {p = p} {σ = σ} {q = q} {f = f} Iw ei ki c Iν ej
        (λ η x l → PsiG₊ {p = p} {σ = σ} Iw ei ki (h η x (→Lg (<→◃ q) l)))
        (λ kj η x l → PsiG₊ {p = σ q} {σ = σ} Iν ej kj (h η x (→Lg (<→◃ q) l)))
PsiG₊ {b = []} Iw ei ki (gĉ () h₀ hk)
PsiG₊ {w = w} {p = p} {σ = σ} {b = y ∷ ys} Iw ei ki (gĉ c h₀ hk) =
  gĉ (cong (E.cofA w) c) (λ K → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c 0)) (PsiG₊ {p = p} {σ = σ} Iw ei ki (h₀ K)))
     (λ K m → subst (LabG₊ _ Lg _) (sym (fs-ω w y ys c (suc m))) (PsiG₊ {p = p} {σ = σ} Iw ei ki (hk K m)))
```

## §9 两个假设与 $X_2$ 的标签

```agda
conv : ∀ {X : Ordˢ one} {t} → LabG₊ one Lg X t → Lab₁ X t
conv (gz c)   = lz c
conv (gs c h) = ls c (conv h)
conv (gl c h) = ll c (λ n → conv (h n))
conv (gu {r = zero} at) = lu (atomL at)
conv (gi {q = zero} c I ej h) = li (trans c (cong cΩ (kdI I (sym (kd-≅ ej))))) (λ θ x at → conv (h θ x at))
conv (gi {q = suc ()} c I ej h)
conv (gĉ c h₀ hk) = lĉ c (λ K → conv (h₀ K)) (λ K m → conv (hk K m))

one⁰ : Ordᶜ zero
one⁰ = suc zero

I1 : Idx (natT 1)
I1 = one⁰ , hs hz , l1 refl (s≅ z≅) (l0 refl z≅) , γ′-NF 0

Hθ′ : ∀ θ (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ →
      ∀ {ℓ} (p : one <ᴵ ℓ) (σ : Simᴵ (toLevel Y hY) ℓ) → Lab₁ (ψ0 p σ (Ωˢ (toLevel Y hY))) (ψ₁Ω θ)
Hθ′ θ Y hY lY nθ p σ = conv (PsiV {p = p} {σ = σ} I1 (≅ᴵ-refl one) refl (LabG-Ω Y hY lY nθ (≅ᴵ-refl _)))

H₀ : ∀ {ℓ} (p : one <ᴵ ℓ) (σ : Simᴵ one ℓ) → Lab₁ (ψ0 p σ (Ωˢ one)) (ψ₁Ω (natT 1))
H₀ p σ = Hθ′ (natT 1) one⁰ (hs hz) (l1 refl (s≅ z≅) (l0 refl z≅)) (γ′-NF 0) p σ

open Pre1M H₀ (λ θ Y hY lY nθ _ → Hθ′ θ Y hY lY nθ) public using (Pre1; X₂-label)
```

## §11 结论与边界
