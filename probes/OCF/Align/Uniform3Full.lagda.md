# 统一形 (三): 一般层号的深度 1 折叠定理

> 接 [Uniform3Hon](Uniform3Hon.lagda.md). 结论先说:
>
> 1. **`TΩ2-label` (§8): $\psi_0(\Omega_\Omega^2)$ 的无条件标签.** 对一切环境与证据, `Lab₀ (ψᵀ (Ψ (Ψ ∅ᵀ)) ev z) tΩ2`. 这正是 OmegaSqA `¬TΩ2-label` 否定的类型; 修正之后它是定理.
> 2. **一般层号的深度 1 折叠定理 (§5–§6).** `WH`/`OH`/`FullH`: 诚实的尾巴 (`Hn`), 地板被标签首项见证 (`FH`), 任意层号. `WΩ`/`OΩ`: 裸的 $\Omega_\theta$, 对一切带标签的 $\theta$, 层号可以是后继或极限.
> 3. **好帧的 $\Omega_\Omega$ 闭包仍是好帧 (§7, `goodΩ̂₁ʰ`).** `GA1ʰ E ζ → GA1ʰ (Ω̂A 1 E) (ζ ++ Ω_Ω)`, 无前提. `FullΩ`: Relative `BranchΩᴬ` 的强形式也是定理.
> 4. **中间检验 (§8).** `TΩ₄-label` ($\psi_0(\psi_\Omega(\Omega_4))$, OmegaSqA 的停点), `TΩω-label` ($\psi_0(\psi_\Omega(\Omega_\omega))$, RelativeBase §9 的反例位置), `TΩθ-label` (一切带标签的 $\theta$).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 终止是 `(层号, Hn 推导)` 的字典序, Agda 自己认出来.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform3Full where

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
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_)
import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; []<; 𝟏; cofA; sucT; cmpᵀ) renaming (ψ to ψᵗ)
open import OCF.Align.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1; fs-rep)
open import OCF.Align.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred; walkD; tO-desc-NF)
open import OCF.Align.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Stage2Label using (one⁰; Lab-oc)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.OmegaKBase using (tΩ2; tΩ2-NF)
open import OCF.Align.OmegaExp using (ψΩ₀; tΩ1-NF)
open import OCF.Align.Standard using (d₀)
open import OCF.Align.Decouple using (Idx; lvI; kdI; kdI[]; Ieq; Lab0[])
open import OCF.Align.GoodLBase
open import OCF.Align.OmegaExpBase using (OccΣ; repW; ωW; snoc; πw; γW; cofW; gtW; fsT-ne)
open import OCF.Align.UniformS
open import OCF.Align.Uniform3Base
open import OCF.Align.Uniform3Depth1 using (wkLW; wkL0; c1Ω; cωΩ; cΩΩ; penΩ)
open import OCF.Align.Uniform3Rel
open import OCF.Align.Uniform3SqABase
open import OCF.Align.Uniform3SqA using (FP0; FP0→FP; FP0-fz; FP0-z; FP0-rep; LW0→LW; L0≡π; L0≡ζ; wkGRᴬ; Up0)
open import OCF.Align.Uniform3Hon
open GRᴬ
```

## §1 带诚实性的好前缀与好帧

```agda
GRH : ∀ {φ} → Run φ → T → Set
GRH R u = GRᴬ R u × LWʰ[ zero ] R u

GA0ʰ : ∀ {fl} → Run fl → T → Set
GA0ʰ {fl} P π = FlrLab fl π × GRH P π

record GA1ʰ {φ} (E : A 1 φ) (ζ : T) : Set where
  constructor ga1ʰ
  field
    fl1ʰ : FlrLabΩ φ ζ
    gw1ʰ : ∀ {c} → GWʰ c E ζ
    g01ʰ : ∀ {fl} {P : Run fl} {π} → GA0ʰ P π → L0 (E P) (π ++ ψΩᵗ ζ)
    gr1ʰ : E ≈₁ᴬ E
open GA1ʰ public

wOf : ∀ {φ} {E : A 1 φ} {ζ} → GA1ʰ E ζ → GA1ʷ E ζ
wOf G = ga1ʷ (fl1ʰ G) (gw1ʰ G)

gv1ʰ : ∀ {φ} {F : A 1 φ} {b} → GA1ʰ F b → ∀ {fl} {P : Run fl} {π} → GA0ʰ P π → GRH (F P) (π ++ ψΩᵗ b)
gv1ʰ G (F , GP , HP) =
  grᴬ (LW0→LW (LWʰ→ h)) (g01ʰ G (F , GP , HP)) (gr1ʰ G (∼ᶠ-refl _) (gRᴬ GP)) , h
  where h = gw1ʰ G (FlrLab→[] F) HP

wkGRH : ∀ {φ ψ} {R : Run φ} (le : ∀ {L} → Ev L ψ → Ev L φ) {u} → GRH R u → GRH (wk 0 le R) u
wkGRH le (G , H) = wkGRᴬ le G , wkLWʰ le H

copyGAʰ : ∀ {ψ fl} {P : Run fl} {π b} {fr : A 1 ψ} → GA0ʰ P π → (∀ m → FlrLab ψ (replicate (suc m) (ψᵗ Ωᵗ b))) →
          (∀ {fl′} {Q : Run fl′} {ρ} → GA0ʰ Q ρ → GRH (fr Q) (ρ ++ ψΩᵗ b)) →
          ∀ m → GA0ʰ (repA 0 P fr (suc m)) (π ++ replicate (suc m) (ψᵗ Ωᵗ b))
copyGAʰ (F , GP) Fψ Gfr zero = FlrLab-⊔ F (Fψ 0) , Gfr (F , GP)
copyGAʰ {π = π} {b = b} (F , GP) Fψ Gfr (suc m) =
  FlrLab-⊔ F (Fψ (suc m)) ,
  wkGRH _ (subst (GRH _) (snoc π (suc m) (ψᵗ Ωᵗ b)) (Gfr (copyGAʰ (F , GP) Fψ Gfr m)))

copyGRʰ : ∀ {ψ fl} {P : Run fl} {π b} {fr : A 1 ψ} → GA0ʰ P π → (∀ m → FlrLab ψ (replicate (suc m) (ψᵗ Ωᵗ b))) →
          (∀ {fl′} {Q : Run fl′} {ρ} → GA0ʰ Q ρ → GRH (fr Q) (ρ ++ ψΩᵗ b)) →
          ∀ m → GRH (repA 0 P fr m) (π ++ replicate m (ψᵗ Ωᵗ b))
copyGRʰ {ψ = ψ} {π = π} (F , GP) Fψ Gfr zero =
  wkGRH (proj₁ {B = λ _ → Ev _ ψ}) (subst (GRH _) (sym (++-identityʳ π)) GP)
copyGRʰ GP Fψ Gfr (suc m) = proj₂ (copyGAʰ GP Fψ Gfr m)
```

## §2 第 0 层的尾巴

与 OmegaSqA `OA`/`FullA` 逐字 (地板策略 `FP0`).

```agda
module Atoms {flE} {E : A 1 flE} {ζ : T} (GE : GA1ʰ E ζ) where
  open WGenʰ (wOf GE)

  OAʰ : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP0 φ → Lab0ᴸ t y → t ≅ᴬ t →
        ∀ {fl} {P : Run fl} {π} → GA0ʰ P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))
  FullAʰ : ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ zero L} {t : Ordˢ zero} {y} → FP0 φ → Lab0ᴸ t y → t ≅ᴬ t →
           GA1ʰ (fold 1 φ cv E t) (ζ ++ y)

  FullAʰ {φ} {cv} {y = y} fp l ex =
    ga1ʰ (FlrLabΩ-⊔ (FlrLabΩ-ext y (fl1ʰ GE)) (FP→FlrLabΩ fp)) (λ {c} → WAʰ (FP0→FP fp) l) (OAʰ fp l ex)
         (fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ʰ GE) z≅ (∼ᶠ-refl φ) ex)

  OAʰ {y = []} fp (lz c) ex {P = P} GP = wkL0 {R = E P} (λ ev → proj₁ ev , proj₁ (proj₂ ev)) (L0≡ζ (E P) (sym (++-identityʳ ζ)) (g01ʰ GE GP))
  OAʰ {y = y ∷ ys} fp (lz c) ex GP = ⊥-elim (cof-ne y ys c)
  OAʰ {y = []} fp (ls () l) ex GP
  OAʰ {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y ∷ ys} fp (ls c l) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ c)
         (λ m → L0≡π (repA 0 P (fold 1 φ cv E a) m) π (sym (repW Ωᵗ ζ y ys c m))
                      (g0ᴬ (proj₁ (copyGRʰ GP (FP0-rep (fl1ʰ GE) fp) (gv1ʰ (FullAʰ {cv = cv} fp l (s-invᴬ ex))) m))))
  OAʰ {y = []} fp (ll () h) ex GP
  OAʰ {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (ll c h) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ c)
         (λ n → L0≡π (fold 1 φ cv E (G n) P) π (sym (ωW Ωᵗ ζ y ys c n)) (OAʰ {cv = cv} fp (h n) (l-invᴬ ex n) GP))
  OAʰ {y = []} fp (lŝ₀ () K h₀ hk) ex GP
  OAʰ {φ = φ} {cv = cv} {y = y ∷ ys} fp (lŝ₀ {t₀ = t₀} {g = g} c K h₀ hk) ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E t₀ P} {O = λ η e → fold 1 φ cv E (g η e) P}
       (cωΩ ζ c) K (L0≡π (fold 1 φ cv E t₀ P) π (sym (ωW Ωᵗ ζ y ys c 0)) (OAʰ {cv = cv} fp h₀ (ŝ-refl₀ᴬ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (g (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys c (suc k)))
                   (OAʰ {cv = cv} fp (hk k) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)) GP))
  OAʰ {y = []} fp (lĉ () K h₀ hk) ex GP
  OAʰ {φ = φ} {cv = cv} {y = y ∷ ys} fp (lĉ {o₀ = o₀} {o = o} c K h₀ hk) ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
       (cωΩ ζ c) K (L0≡π (fold 1 φ cv E o₀ P) π (sym (ωW Ωᵗ ζ y ys c 0)) (OAʰ {cv = cv} fp h₀ (ĉ-refl₀ᴬ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (o (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys c (suc k))) (OAʰ {cv = cv} fp (hk k) (ĉ-reflgᴬ ex _ _) GP))
```

## §3 地板见证的搬运

```agda
FHc : Ordᴵ → Flr → T → Set
FHc c φ y = ∀ {K} (k : InF K φ) → IgnK c k ⊎ (K ≅ᴵ one) ⊎ HK K y

FH→FHc : ∀ {c φ y} → FH φ y → FHc c φ y
FH→FHc F k with F k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ h = inj₂ h

FHc-fsn : ∀ {c φ y} → NB y → FHc c φ y → ∀ n → FHc c φ (fsn y n)
FHc-fsn {y = ψᵗ u v ∷ vs} nb F n k with F k
... | inj₁ g = inj₁ g
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) = inj₂ (inj₂ (HK-Hu h (Hu-fsn u v vs nb n)))

FHc-fsT : ∀ {c φ y} → NB y → FHc c φ y → ∀ η → FHc c φ (fsT y η)
FHc-fsT {y = ψᵗ u v ∷ vs} nb F η k with F k
... | inj₁ g = inj₁ g
... | inj₂ (inj₁ e) = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) = inj₂ (inj₂ (HK-Hu h (Hu-fsT u v vs nb η)))

Pr : T → Set
Pr y = Σ T λ u → Σ T λ v → Σ T λ vs → y ≡ ψᵗ u v ∷ vs

pred-Pr : ∀ {u v vs} → NB (ψᵗ u v ∷ vs) → cof (ψᵗ u v ∷ vs) ≡ c1 → Σ T λ v′ → Σ T λ vs′ → pred (ψᵗ u v ∷ vs) ≡ ψᵗ u v′ ∷ vs′
pred-Pr {u} {v} {vs} = Hu-pred u v vs

FHc-pred : ∀ {c φ u v vs} → NB (ψᵗ u v ∷ vs) → cof (ψᵗ u v ∷ vs) ≡ c1 → FHc c φ (ψᵗ u v ∷ vs) → FHc c φ (pred (ψᵗ u v ∷ vs))
FHc-pred {u = u} {v} {vs} nb c F k with F k | pred-Pr {u} {v} {vs} nb c
... | inj₁ g | _ = inj₁ g
... | inj₂ (inj₁ e) | _ = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) | v′ , vs′ , eq = inj₂ (inj₂ (subst (HK _) (sym eq) h))

FH-pred : ∀ {φ u v vs} → NB (ψᵗ u v ∷ vs) → cof (ψᵗ u v ∷ vs) ≡ c1 → FH φ (ψᵗ u v ∷ vs) → FH φ (pred (ψᵗ u v ∷ vs))
FH-pred {u = u} {v} {vs} nb c F k with F k | pred-Pr {u} {v} {vs} nb c
... | inj₁ g | _ = inj₁ g
... | inj₂ (inj₁ e) | _ = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) | v′ , vs′ , eq = inj₂ (inj₂ (subst (HK _) (sym eq) h))

FHc-rep : ∀ {c flE φ ζ b u v vs} → b ≡ ψᵗ u v ∷ vs → FlrLabΩ flE ζ → FHc c φ b → ∀ m → FlrLab[ c ] (flE ⊔ φ) (replicate (suc m) (ψᵗ Ωᵗ (ζ ++ b)))
FHc-rep {b = b} refl FE f m (inl k) with FE k
... | inj₁ e = inj₁ (inj₁ (inj₁ e))
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , occ-hd (o b))
FHc-rep {ζ = ζ} {u = u} refl FE f m (inr k) with f k
... | inj₁ g = inj₁ g
... | inj₂ (inj₁ e1) with wit1 e1
...   | w , Iw , kw , o = inj₂ (w , Iw , kw , occ-hd (o _))
FHc-rep {ζ = ζ} {u = u} refl FE f m (inr k) | inj₂ (inj₂ (I , kw)) = inj₂ (u , I , kw , occ-hd (od (OccΣ ζ oh)))

FH-rep : ∀ {flE φ ζ b u v vs} → b ≡ ψᵗ u v ∷ vs → FlrLabΩ flE ζ → FH φ b → ∀ m → FlrLab (flE ⊔ φ) (replicate (suc m) (ψᵗ Ωᵗ (ζ ++ b)))
FH-rep {b = b} refl FE f m (inl k) with FE k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , occ-hd (o b))
FH-rep {ζ = ζ} {u = u} refl FE f m (inr k) with f k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e1) with wit1 e1
...   | w , Iw , kw , o = inj₂ (w , Iw , kw , occ-hd (o _))
FH-rep {ζ = ζ} {u = u} refl FE f m (inr k) | inj₂ (inj₂ (I , kw)) = inj₂ (u , I , kw , occ-hd (od (OccΣ ζ oh)))

FH→Ω : ∀ {φ ζ z u v vs} → z ≡ ψᵗ u v ∷ vs → FH φ z → FlrLabΩ φ (ζ ++ z)
FH→Ω {ζ = ζ} {u = u} {v} {vs} refl f k with f k
... | inj₁ e = inj₁ e
... | inj₂ (inj₁ e1) with wit1 e1
...   | w , Iw , kw , o = inj₂ (w , Iw , kw , λ b → o _)
FH→Ω {ζ = ζ} {u = u} {v} {vs} refl f k | inj₂ (inj₂ (I , kw)) =
  inj₂ (u , I , kw , λ b → subst (λ w → Occ u (ψᵗ Ωᵗ w ∷ [])) (sym (++-assoc ζ (ψᵗ u v ∷ vs) b)) (od (OccΣ ζ oh)))

flo≼ : ∀ {j L} → j ≅ᴵ L → ∀ {K} → InF K (flo j) → K ≼ L
flo≼ {j = zero} e ()
flo≼ {j = suc j} e ink = inj₁ (≺ᴵ-respʳ (via (≅ᴵ-refl j) zero) e)
flo≼ {j = lim f s} e inb = inj₂ e

FlrLab[]-up : ∀ {c c′ φ ps} → Up c c′ → FlrLab[ c ] φ ps → FlrLab[ c′ ] φ ps
FlrLab[]-up u F k with F k
... | inj₁ (inj₁ (inj₁ e0)) = inj₁ (inj₁ (inj₁ e0))
... | inj₁ (inj₁ (inj₂ kc)) = inj₁ (inj₁ (inj₂ (≼-trans kc u)))
... | inj₁ (inj₂ (b , le)) = inj₁ (inj₂ (b , ⊑ᴵ-trans le (sB u)))
... | inj₂ w = inj₂ w

LWʰ-up : ∀ {c c′ φ} {R : Run φ} {u} → Up c c′ → LWʰ[ c ] R u → LWʰ[ c′ ] R u
LWʰ-up u h ev p Iw ei ki u′ = h ev p Iw ei ki (≼-trans u u′)

Zc : Ordᴵ → Ordᴵ → Flr → Set
Zc c zero φ = FP c φ
Zc c (suc _) φ = ⊤
Zc c (lim _ _) φ = ⊤

Zc-of : ∀ {c k φ w} (I : Idx w) → k ≅ᴵ lvI I → FHc c φ (Ωt w) → Zc c k φ
Zc-of {k = zero} I e f k₁ with f k₁
... | inj₁ g = inj₁ g
... | inj₂ (inj₁ e1) = inj₂ e1
... | inj₂ (inj₂ (I′ , kw)) with ≼-trans kw (inj₂ (≅ᴵ-trans (Ieq I′ I) (≅ᴵ-sym e)))
...   | inj₁ (via _ ())
...   | inj₂ e0 = inj₁ (inj₁ (inj₁ e0))
Zc-of {k = suc _} I e f = tt
Zc-of {k = lim _ _} I e f = tt

Zc-flo : ∀ {c} k → Zc c k (flo k)
Zc-flo zero = FP-fz
Zc-flo (suc k) = tt
Zc-flo (lim f s) = tt
```

## §4 目标 0 的 `limᵢ` 行, 只对链点

```agda
limᵢ0ᴾ : ∀ {φ j ν} {ps : T} {y : PT} {ys : T} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ} →
         kd j ≡ false → cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (Inp : T → Ordˢ j → Set) → Inp (Ωt ν) (Ωˢ j) →
         (∀ {η x} → Inp η x → ∀ {ℓ} (ev : Ev ℓ φ) → Inp (πw ν ps (fsT (y ∷ ys) η)) (H x ev (ac ev))) →
         (∀ {η x} → Inp η x → L0 (H x) (ps ++ fsT (y ∷ ys) η)) →
         L0 (limᵢA 0 ac H) (ps ++ (y ∷ ys))
limᵢ0ᴾ {j = zero} () c Iν ej Inp i₀ hS hO ev p nu
limᵢ0ᴾ {j = suc j′} {ν = []} kj c Iν ej Inp i₀ hS hO ev p nu = ⊥-elim (tf (trans (sym (kdI[] Iν)) (sym (kd-≅ ej))))
limᵢ0ᴾ {j = suc j′} {ν = v ∷ vs} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} kj c Iν ej Inp i₀ hS hO ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₁ (z≺I Iν ej (λ ())))
  nf : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  chainI : ∀ m → Inp (γW ps (y ∷ ys) (v ∷ vs) m) (chainA ac H ev m)
  chainI zero    = i₀
  chainI (suc m) = hS (chainI m) ev
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  outp m = hO (chainI m) ev p (nf m)
limᵢ0ᴾ {j = lim f s} {ν = []} kj c Iν ej Inp i₀ hS hO ev p nu = ⊥-elim (tf (trans (sym (kdI[] Iν)) (sym (kd-≅ ej))))
limᵢ0ᴾ {j = lim f s} {ν = v ∷ vs} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} kj c Iν ej Inp i₀ hS hO ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₁ (z≺I Iν ej (λ ())))
  nf : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  chainI : ∀ m → Inp (γW ps (y ∷ ys) (v ∷ vs) m) (chainA ac H ev m)
  chainI zero    = i₀
  chainI (suc m) = hS (chainI m) ev
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  outp m = hO (chainI m) ev p (nf m)
```

## §5 一般层号: W 部分

`WH`: 诚实的尾巴 (任意层号 $\ne0$), 地板由首项见证, 则在一切目标 $\succeq c$ 处输出带标签且诚实. `WΩ`: 裸的 $\Omega_\theta$, 对 $\theta$ 的树递归: 后继层是 `limᵢWᴾ` (低目标处只对链点, 链点的诚实性来自 `WVʰ`), 极限层是 `lim` + `up (self n)` (地板换成 `flo (f n)`, 这就是 Uniform3 的修正起作用的地方). 终止: `WΩ` 到 `WTail` 层号严格下降; `WH` 到 `WΩ` 层号不变, `WH` 到 `WH` 在 `Hn` 上结构下降.

```agda
module Main {flE} {E : A 1 flE} {ζ : T} (GE : GA1ʰ E ζ) where
  open WGenʰ (wOf GE)
  open Atoms GE

  CH : (j : Ordᴵ) → T → Ordˢ j → Set
  CH j η x = kd j ≡ false → Hn x η × FH (flo j) η

  Inp : (j : Ordᴵ) → T → Ordˢ j → Set
  Inp j η x = LabL x η × CH j η x

  WH : ∀ {c k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FHc c φ y → Hn t y → LabL₊ k Ll t y → GWʰ c (fold 1 φ cv E t) (ζ ++ y)
  WΩ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {k} → k ≅ᴵ toLevel Y hY → ∀ {c φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} → Zc c k φ →
       GWʰ c (fold 1 φ cv E (Ωˢ k)) (ζ ++ Ωt θ)
  WTail : ∀ {c j} {x : Ordˢ j} {η} → Inp j η x → GWʰ c (fold 1 (flo j) (cvFlo j) E x) (ζ ++ η)

  WTail {j = zero}    (l , ch) = WVʰ FP-fz (inj₂ lw0) l
  WTail {j = suc _}   (l , ch) = WH (FH→FHc (proj₂ (ch refl))) (proj₁ (ch refl)) l
  WTail {j = lim _ _} (l , ch) = WH (FH→FHc (proj₂ (ch refl))) (proj₁ (ch refl)) l

  WH fp (hΩ {w = w} refl (Y , hY , lY , nY) e) l = WΩ Y hY lY nY e (Zc-of (Y , hY , lY , nY) e fp)
  WH {c = c} {y = []} fp hz (gz cc) F hP = wkLWʰ _ (subst (λ u → LWʰ[ c ] _ (_ ++ ψΩᵗ u)) (sym (++-identityʳ ζ)) (gw1ʰ GE F hP))
  WH {y = y ∷ ys} fp hz (gz cc) F hP = ⊥-elim (cof-ne y ys cc)
  WH {y = []} fp (hs () n) l
  WH {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y@(ψᵗ _ _) ∷ ys} fp (hs nb n) (gs cc l) {P = P} {π = π} F hP =
    limWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ cc)
          (λ m → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (repW Ωᵗ ζ y ys cc m))
                       (copyWʰ F (FHc-rep (proj₂ (proj₂ (pred-Pr nb cc))) (fl1ʰ GE) (FHc-pred nb cc fp)) hP (WH (FHc-pred nb cc fp) n l) m))
  WH {y = []} fp (hl () n) l
  WH {c = c} {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (hl nb n) (gl cc h) {P = P} {π = π} F hP =
    limWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ cc)
          (λ m → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cc m)) (WH (FHc-fsn nb fp m) (n m) (h m) F hP))
  WH {y = []} fp (hi () n) l
  WH {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp (hi {q = q} {f = f} nb n) (gi cc I ej h) {P = P} {π = π} F hP =
    limᵢWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) q}
           {H = λ x → fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P} (cΩΩ ζ cc I) I ej
           (λ η x l → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I η))
                            (WH (FHc-fsT nb fp η) (n η x l) (h η x (→Ll (<→◃ q) l)) F hP))
  WH {y = []} fp (hĉ () cw K g₀ n₀ gk nk) l
  WH {c = c} {φ = φ} {cv = cv} {y = y ∷ ys} fp (hĉ {o₀ = o₀} {o = o} nb cw K g₀ n₀ gk nk) l {P = P} {π = π} F hP =
    ĉWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
        (cωΩ ζ cw) K (subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cw 0)) (WH (FHc-fsn nb fp 0) n₀ g₀ F hP))
        (λ k → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ y ys cw (suc k))) (WH (FHc-fsn nb fp (suc k)) (nk k) (gk k) F hP))
  WH {k = zero} fp (hŝ nb n₀ nk) (gŝ () c Iw bw ob h₀ hg)
  WH {k = suc _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg)
  WH {c = c} {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ {w = w} {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) {P = P} {π = π} F hP =
    ŝWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
        (cΩΩ ζ cc I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ cc I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
        (subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 (natT 1))) (WH (FHc-fsT nb fp (natT 1)) n₀ h₀ F hP))
        (λ θ Y hY lY nθ lt e → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 θ))
                                     (WH (FHc-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e) F hP))
  WH {k = lim _ _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg)
  WH {c = c} {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ {w = w} {t₀ = t₀} {g = g} kk cc Iw bw ob h₀ hg) {P = P} {π = π} F hP =
    ŝWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
        (cΩΩ ζ cc I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ cc I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
        (subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 (natT 1))) (WH (FHc-fsT nb fp (natT 1)) n₀ h₀ F hP))
        (λ θ Y hY lY nθ lt e → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (penΩ ζ cc I0 θ))
                                     (WH (FHc-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e) F hP))

  WΩ {θ = []} Ord₊.zero hY l nθ z≅ zc = WVʰ zc (inj₂ lw0) (LabL-Ω Ord₊.zero hY l nθ z≅)
  WΩ {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ zc with Lab0[] l
  ... | ()
  WΩ (Ord₊.suc Y) hY (l0 c ()) nθ (s≅ e) zc
  WΩ (Ord₊.suc Y) hY (lω c () h) nθ (s≅ e) zc
  WΩ {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) zc
  WΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc j} (s≅ e) {c} {φ} {cv} zc {fl} {P} {π} F hP =
    limᵢWᴾ {c = c} {φ = fl ⊔ (flE ⊔ φ)} {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ωt θ)} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) zero}
           {H = λ x → fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P} (cΩΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I) I e
           (Inp j) i₀ hPen hStep hOut
    where
    θ : T
    θ = w ∷ ws
    cΩθ : cof (Ωt θ) ≡ cΩ (pred θ)
    cΩθ = cong (E.cofψ0 θ) c₁
    I : Idx (pred θ)
    I = Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁
    pen′ : ∀ η → fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η ≡ ψᵗ Ωᵗ (ζ ++ η) ∷ []
    pen′ η = trans (penΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I η) (cong (λ u → ψᵗ Ωᵗ (ζ ++ u) ∷ []) (fsT-c1 θ (cof θ) c₁ η))
    le : ∀ {L} → Ev L (fl ⊔ (flE ⊔ φ)) → Ev L (fl ⊔ (flE ⊔ flo j))
    le ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo j (λ q → cv (proj₂ (proj₂ ev)) (suc q)))
    i₀ : Inp j (Ωt (pred θ)) (Ωˢ j)
    i₀ = LabL-Ω Y (hs⁻ hY) (Lab-≅ e′ l) (NF₁-pred nθ c₁) e , λ _ → hΩ refl I e , (λ k → inj₂ (inj₂ (I , flo≼ e k)))
    hPen : ∀ η x → LabL x η → ∀ {i ℓ w′} (ev : Ev ℓ (fl ⊔ (flE ⊔ φ))) (p : i <ᴵ ℓ) (Iw : Idx w′) → i ≅ᴵ lvI Iw → kd i ≡ false → Up c i → j ≺ᴵ i →
           Out (fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P ev p) (ψᵗ w′ (π ++ fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η) ∷ [])
    hPen η x lx {i} {w′ = w′} ev p Iw ei ki u s =
      subst (λ v → Out _ (ψᵗ w′ (π ++ v) ∷ [])) (sym (pen′ η))
            (WVʰ {c = i} {φ = flo j} {cv = cvFlo j} (FP-flo′ lvᵢ) lvᵢ lx (FlrLab[]-up u F) (LWʰ-up u hP) (le ev) p Iw ei ki (inj₂ (≅ᴵ-refl i)))
      where
      lvᵢ : LvOK i j
      lvᵢ = inj₁ (⊑ᴵ-trans (≺→⊑ s) (⊑-suc i))
    hStep : ∀ {η x} → Inp j η x → kd j ≡ false → Up c j → ∀ {ℓ} (ev : Ev ℓ (fl ⊔ (flE ⊔ φ))) →
            Inp j (πw (pred θ) π (fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η)) (fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P ev (cv (proj₂ (proj₂ ev)) zero))
    hStep {η} {x} (lx , ch) kj uj ev =
      subst (λ v → Inp j (ψᵗ (pred θ) (π ++ v) ∷ []) _) (sym (pen′ η))
            (frL₊ kj (proj₁ o) , λ _ → proj₂ o , (λ k → inj₂ (inj₂ (I , flo≼ e k))))
      where
      lvⱼ : LvOK j j
      lvⱼ = inj₁ (⊑-suc j)
      o = WVʰ {c = j} {φ = flo j} {cv = cvFlo j} (FP-flo′ lvⱼ) lvⱼ lx (FlrLab[]-up uj F) (LWʰ-up uj hP) (le ev) (cv (proj₂ (proj₂ ev)) zero) I e kj (inj₂ (≅ᴵ-refl j))
    hOut : ∀ {η x} → Inp j η x → LWʰ[ c ] (fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P) (π ++ fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η)
    hOut {η} {x} ix = subst (λ v → LWʰ[ c ] _ (π ++ v)) (sym (pen′ η)) (wkLWʰ le (WTail ix F hP))
  WΩ (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) zc
  WΩ (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) zc
  WΩ {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) zc
  WΩ {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {k = lim f s} (l≅ ee) {c} {φ} {cv} zc {fl} {P} {π} F hP =
    limWʰ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ωt θ)} {ys = []} {F = λ n → fold 1 φ cv E (Ord₊ˢ.up (self n) (Ωˢ (f n))) P} (cωΩ ζ {y = ψᵗ θ []} {ys = []} cωθ)
          (λ n → subst (λ u → LWʰ[ c ] _ (π ++ u)) (sym (ωW Ωᵗ ζ (ψᵗ θ []) [] cωθ n))
                       (subst (λ u → LWʰ[ c ] _ (π ++ ψᵗ Ωᵗ (ζ ++ u) ∷ [])) (sym (E.fsn0-eq w ws n c₁))
                              (wkLWʰ (le n) (WΩ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) {c} {flo (f n)} {cvFlo (f n)} (Zc-flo (f n)) F hP))))
    where
    θ : T
    θ = w ∷ ws
    cωθ : cof (Ωt θ) ≡ cω
    cωθ = cong (E.cofψ0 θ) c₁
    le : ∀ n {L} → Ev L (fl ⊔ (flE ⊔ φ)) → Ev L (fl ⊔ (flE ⊔ flo (f n)))
    le n ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo (f n) (λ q → cv (proj₂ (proj₂ ev)) (lim n q)))
  WΩ (Ord₊.limᵢ () f) hY l nθ e zc
  WΩ (Ord₊.up () x) hY l nθ e zc
```

## §6 一般层号: 目标 0 与折叠定理

```agda
  Zc₀ : Ordᴵ → Flr → Set
  Zc₀ zero φ = FP0 φ
  Zc₀ (suc _) φ = ⊤
  Zc₀ (lim _ _) φ = ⊤

  Zc₀-of : ∀ {k φ w} (I : Idx w) → k ≅ᴵ lvI I → FH φ (Ωt w) → Zc₀ k φ
  Zc₀-of {k = zero} I e f k₁ with f k₁
  ... | inj₁ e0 = inj₁ e0
  ... | inj₂ (inj₁ e1) = inj₂ e1
  ... | inj₂ (inj₂ (I′ , kw)) with ≼-trans kw (inj₂ (≅ᴵ-trans (Ieq I′ I) (≅ᴵ-sym e)))
  ...   | inj₁ (via _ ())
  ...   | inj₂ e0 = inj₁ e0
  Zc₀-of {k = suc _} I e f = tt
  Zc₀-of {k = lim _ _} I e f = tt

  Zc₀-flo : ∀ k → Zc₀ k (flo k)
  Zc₀-flo zero = FP0-fz
  Zc₀-flo (suc k) = tt
  Zc₀-flo (lim f s) = tt

  Inp′ : (j : Ordᴵ) → T → Ordˢ j → Set
  Inp′ j η x = LabL x η × (x ≅ᴬ x) × CH j η x

  OH : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {y} → FH φ y → Hn t y → LabL₊ k Ll t y → t ≅ᴬ t →
       ∀ {fl} {P : Run fl} {π} → GA0ʰ P π → L0 (fold 1 φ cv E t P) (π ++ ψΩᵗ (ζ ++ y))
  FullH : ∀ {k φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} {t : Ordˢ k} {z u v vs} → z ≡ ψᵗ u v ∷ vs → FH φ z → Hn t z → LabL₊ k Ll t z → t ≅ᴬ t →
          GA1ʰ (fold 1 φ cv E t) (ζ ++ z)
  OΩ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → ∀ {k} → k ≅ᴵ toLevel Y hY → ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} → Zc₀ k φ →
       ∀ {fl} {P : Run fl} {π} → GA0ʰ P π → L0 (fold 1 φ cv E (Ωˢ k) P) (π ++ ψΩᵗ (ζ ++ Ωt θ))
  OΩs : ∀ {w ws j} → kd j ≡ false → cof (w ∷ ws) ≡ c1 → (I : Idx (pred (w ∷ ws))) → j ≅ᴵ lvI I → ∀ {φ} {cv : ∀ {L} → Ev L φ → Simᴵ (suc j) L} →
        ∀ {fl} {P : Run fl} {π} → GA0ʰ P π → L0 (fold 1 φ cv E (Ωˢ (suc j)) P) (π ++ ψΩᵗ (ζ ++ Ωt (w ∷ ws)))

  FullH {k = k} {φ} {cv} {z = z} refl fp n l ex =
    ga1ʰ (FlrLabΩ-⊔ (FlrLabΩ-ext z (fl1ʰ GE)) (FH→Ω refl fp)) (λ {c} → WH (FH→FHc fp) n l) (OH fp n l ex)
         (fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ʰ GE) (≅ᴵ-refl k) (∼ᶠ-refl φ) ex)

  OH fp (hΩ refl (Y , hY , lY , nY) e) l ex GP = OΩ Y hY lY nY e (Zc₀-of (Y , hY , lY , nY) e fp) GP
  OH {y = []} fp hz (gz c) ex {P = P} GP = wkL0 {R = E P} (λ ev → proj₁ ev , proj₁ (proj₂ ev)) (L0≡ζ (E P) (sym (++-identityʳ ζ)) (g01ʰ GE GP))
  OH {y = y ∷ ys} fp hz (gz c) ex GP = ⊥-elim (cof-ne y ys c)
  OH {y = []} fp (hs () n) l ex GP
  OH {φ = φ} {cv = cv} {t = Ord₊ˢ.suc a} {y = y@(ψᵗ _ _) ∷ ys} fp (hs nb n) (gs c l) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → repA 0 P (fold 1 φ cv E a) m} (c1Ω ζ c)
         (λ m → L0≡π (repA 0 P (fold 1 φ cv E a) m) π (sym (repW Ωᵗ ζ y ys c m))
                      (g0ᴬ (proj₁ (copyGRʰ GP (FH-rep (proj₂ (proj₂ (pred-Pr nb c))) (fl1ʰ GE) (FH-pred nb c fp))
                                              (gv1ʰ (FullH {cv = cv} (proj₂ (proj₂ (pred-Pr nb c))) (FH-pred nb c fp) n l (s-invᴬ ex))) m))))
  OH {y = []} fp (hl () n) l ex GP
  OH {φ = φ} {cv = cv} {t = Ord₊ˢ.lim G} {y = y ∷ ys} fp (hl nb n) (gl c h) ex {P = P} {π = π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {F = λ m → fold 1 φ cv E (G m) P} (cωΩ ζ c)
         (λ m → L0≡π (fold 1 φ cv E (G m) P) π (sym (ωW Ωᵗ ζ y ys c m)) (OH {cv = cv} (FH-fsn nb fp m) (n m) (h m) (l-invᴬ ex m) GP))
  OH {y = []} fp (hi () n) l ex GP
  OH {k = k} {φ = φ} {cv = cv} {y = y ∷ ys} fp (hi {q = q} {f = f} nb n) (gi c I ej h) ex {fl = fl} {P = P} {π = π} GP =
    limᵢ0ᴬ {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) q}
           {H = λ x → fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P} (cΩΩ ζ c I) I ej
           (λ η x l → subst (λ u → LW _ (π ++ u)) (sym (penΩ ζ c I η))
                            (LW0→LW (LWʰ→ (WH (FH→FHc (FH-fsT nb fp η)) (n η x l) (h η x (→Ll (<→◃ q) l)) (FlrLab→[] (proj₁ GP)) (proj₂ (proj₂ GP))))))
           (λ η x l xx → L0≡π (fold 1 φ cv E (f (intoˢ (<→◃ q) x)) P) π (sym (penΩ ζ c I η))
                               (OH {cv = cv} (FH-fsT nb fp η) (n η x l) (h η x (→Ll (<→◃ q) l)) (i-respᴬ ex xx) GP) ,
                         fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ʰ GE) (≅ᴵ-refl k) (∼ᶠ-refl φ) (i-respᴬ ex xx) (∼ᶠ-refl fl) (gRᴬ (proj₁ (proj₂ GP))))
  OH {y = []} fp (hĉ () cw K g₀ n₀ gk nk) l ex GP
  OH {φ = φ} {cv = cv} {y = y ∷ ys} fp (hĉ {o₀ = o₀} {o = o} nb cw K g₀ n₀ gk nk) l ex {P = P} {π = π} GP =
    ĉ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {O₀ = fold 1 φ cv E o₀ P} {O = λ η e → fold 1 φ cv E (o η e) P}
       (cωΩ ζ cw) K (L0≡π (fold 1 φ cv E o₀ P) π (sym (ωW Ωᵗ ζ y ys cw 0)) (OH {cv = cv} (FH-fsn nb fp 0) n₀ g₀ (ĉ-refl₀ᴬ ex) GP))
       (λ k → L0≡π (fold 1 φ cv E (o (lvK K k) (dxK K k)) P) π (sym (ωW Ωᵗ ζ y ys cw (suc k))) (OH {cv = cv} (FH-fsn nb fp (suc k)) (nk k) (gk k) (ĉ-reflgᴬ ex _ _) GP))
  OH {k = zero} fp (hŝ nb n₀ nk) (gŝ () c Iw bw ob h₀ hg) ex GP
  OH {k = suc _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg) ex GP
  OH {k = suc _} {φ = φ} {cv = cv} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ {w = w} {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex {P = P} {π = π} GP =
    ŝ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
       (cΩΩ ζ c I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ c I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
       (L0≡π (fold 1 φ cv E t₀ P) π (sym (penΩ ζ c I0 (natT 1))) (OH {cv = cv} (FH-fsT nb fp (natT 1)) n₀ h₀ (ŝ-refl₀ᴬ ex) GP))
       (λ θ Y hY lY nθ lt e → L0≡π (fold 1 φ cv E (g (toLevel Y hY) e) P) π (sym (penΩ ζ c I0 θ))
                                    (OH {cv = cv} (FH-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)) GP))
  OH {k = lim _ _} {y = []} fp (hŝ nb n₀ nk) (gŝ kk () Iw bw ob h₀ hg) ex GP
  OH {k = lim _ _} {φ = φ} {cv = cv} {y = y ∷ ys} fp (hŝ nb n₀ nk) (gŝ {w = w} {t₀ = t₀} {g = g} kk c Iw bw ob h₀ hg) ex {P = P} {π = π} GP =
    ŝ0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ (y ∷ ys))} {ys = []} {T₀ = fold 1 φ cv E t₀ P} {G = λ η e → fold 1 φ cv E (g η e) P}
       (cΩΩ ζ c I0) Iw bw (λ θ → subst (λ u → Occ w (π ++ u)) (sym (penΩ ζ c I0 θ)) (OccΣ π (od (OccΣ ζ (ob θ)))))
       (L0≡π (fold 1 φ cv E t₀ P) π (sym (penΩ ζ c I0 (natT 1))) (OH {cv = cv} (FH-fsT nb fp (natT 1)) n₀ h₀ (ŝ-refl₀ᴬ ex) GP))
       (λ θ Y hY lY nθ lt e → L0≡π (fold 1 φ cv E (g (toLevel Y hY) e) P) π (sym (penΩ ζ c I0 θ))
                                    (OH {cv = cv} (FH-fsT nb fp θ) (nk θ Y hY lY nθ lt e) (hg θ Y hY lY nθ lt e) (ŝ-reflgᴬ ex _ _ _ _ (≅ᴵ-refl _)) GP))

  OΩ {θ = []} Ord₊.zero hY l nθ z≅ zc GP = OAʰ zc (atomL (LabL-Ω Ord₊.zero hY l nθ z≅)) (Ωˢ-≅ᴬ z≅) GP
  OΩ {θ = y ∷ ys} Ord₊.zero hY l nθ z≅ zc GP with Lab0[] l
  ... | ()
  OΩ (Ord₊.suc Y) hY (l0 c ()) nθ (s≅ e) zc GP
  OΩ (Ord₊.suc Y) hY (lω c () h) nθ (s≅ e) zc GP
  OΩ {θ = []} (Ord₊.suc Y) hY (l1 () (s≅ e′) l) nθ (s≅ e) zc GP
  OΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc (suc j)} (s≅ e) zc GP =
    OΩs refl c₁ (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e GP
  OΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc (lim f s)} (s≅ e) zc GP =
    OΩs refl c₁ (Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁) e GP
  OΩ {θ = w ∷ ws} (Ord₊.suc Y) hY (l1 c₁ (s≅ e′) l) nθ {k = suc zero} (s≅ e) {φ} {cv} zc {fl} {P} {π} GP =
    limᵢ0ᴬ {φ = fl ⊔ (flE ⊔ φ)} {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ωt θ)} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) zero}
           {H = λ x → fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P} (cΩΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I) I e
           (λ η x l′ → subst (λ u → LW _ (π ++ u)) (sym (pen′ η))
                             (wkLW {φ = fl ⊔ (flE ⊔ fz)} le
                                   (LW0→LW (LWʰ→ (WVʰ {φ = fz} {cv = σ⊥f} FP-fz (inj₂ lw0) l′ (FlrLab→[] (proj₁ GP)) (proj₂ (proj₂ GP)))))))
           (λ η x l′ xx → L0≡π (fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P) π (sym (pen′ η))
                                (wkL0 {φ = fl ⊔ (flE ⊔ fz)} {R = fold 1 fz σ⊥f E (intoˢ (<→◃ zero) x) P} le
                                      (OAʰ FP0-fz (atomL l′) xx GP)) ,
                          wkRᴬ le le (fold-≅1ᴬ {φ = fz} {φ′ = fz} {cv = σ⊥f} {cv′ = σ⊥f} (∼ᶠ-refl flE) (gr1ʰ GE) z≅ fz∼ xx (∼ᶠ-refl fl) (gRᴬ (proj₁ (proj₂ GP)))))
    where
    θ : T
    θ = w ∷ ws
    cΩθ : cof (Ωt θ) ≡ cΩ (pred θ)
    cΩθ = cong (E.cofψ0 θ) c₁
    I : Idx (pred θ)
    I = Y , hs⁻ hY , Lab-≅ e′ l , NF₁-pred nθ c₁
    pen′ : ∀ η → fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η ≡ ψᵗ Ωᵗ (ζ ++ η) ∷ []
    pen′ η = trans (penΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I η) (cong (λ u → ψᵗ Ωᵗ (ζ ++ u) ∷ []) (fsT-c1 θ (cof θ) c₁ η))
    σ⊥f : ∀ {L} → Ev L fz → Simᴵ zero L
    σ⊥f = cvFlo zero
    le : ∀ {L} → Ev L (fl ⊔ (flE ⊔ φ)) → Ev L (fl ⊔ (flE ⊔ fz))
    le ev = proj₁ ev , (proj₁ (proj₂ ev) , tt)
  OΩ (Ord₊.lim F′) hY (l0 c₁ ()) nθ (l≅ k) zc GP
  OΩ (Ord₊.lim F′) hY (l1 c₁ () l) nθ (l≅ k) zc GP
  OΩ {θ = []} (Ord₊.lim F′) hY (lω () (l≅ k′) h) nθ (l≅ k) zc GP
  OΩ {θ = w ∷ ws} (Ord₊.lim F′) hY (lω c₁ (l≅ k′) h) nθ {k = lim f s} (l≅ ee) {φ} {cv} zc {fl} {P} {π} GP =
    lim0 {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ωt θ)} {ys = []} {F = λ n → fold 1 φ cv E (Ord₊ˢ.up (self n) (Ωˢ (f n))) P} (cωΩ ζ {y = ψᵗ θ []} {ys = []} cωθ)
         (λ n → L0≡π (fold 1 φ cv E (Ord₊ˢ.up (self n) (Ωˢ (f n))) P) π (sym (ωW Ωᵗ ζ (ψᵗ θ []) [] cωθ n))
                     (L0≡ζ′ n {R = fold 1 φ cv E (Ord₊ˢ.up (self n) (Ωˢ (f n))) P} (wkL0 {φ = fl ⊔ (flE ⊔ flo (f n))} {R = fold 1 (flo (f n)) (cvFlo (f n)) E (Ωˢ (f n)) P} (le n)
                                    (OΩ (F′ n) (hl₁ hY n) (Lab-≅ (k′ n) (h n)) (NF₁-fsn nθ c₁ n) (ee n) {flo (f n)} {cvFlo (f n)} (Zc₀-flo (f n)) GP))))
    where
    θ : T
    θ = w ∷ ws
    cωθ : cof (Ωt θ) ≡ cω
    cωθ = cong (E.cofψ0 θ) c₁
    le : ∀ n {L} → Ev L (fl ⊔ (flE ⊔ φ)) → Ev L (fl ⊔ (flE ⊔ flo (f n)))
    le n ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo (f n) (λ q → cv (proj₂ (proj₂ ev)) (lim n q)))
    L0≡ζ′ : ∀ n {R : Run (fl ⊔ (flE ⊔ φ))} → L0 R (π ++ ψΩᵗ (ζ ++ Ωt (fsn θ n))) → L0 R (π ++ ψΩᵗ (ζ ++ fsn (Ωt θ) n))
    L0≡ζ′ n {R} = subst (λ u → L0 R (π ++ ψΩᵗ (ζ ++ u))) (sym (E.fsn0-eq w ws n c₁))
  OΩ (Ord₊.limᵢ () f) hY l nθ e zc GP
  OΩ (Ord₊.up () x) hY l nθ e zc GP

  OΩs {w} {ws} {j} kj c₁ I e {φ} {cv} {fl} {P} {π} GP =
    limᵢ0ᴾ {φ = fl ⊔ (flE ⊔ φ)} {ps = π} {y = ψᵗ Ωᵗ (ζ ++ Ωt θ)} {ys = []} {ac = λ ev → cv (proj₂ (proj₂ ev)) zero}
           {H = λ x → fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P} kj (cΩΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I) I e
           (Inp′ j) i₀ hS hO
    where
    θ : T
    θ = w ∷ ws
    cΩθ : cof (Ωt θ) ≡ cΩ (pred θ)
    cΩθ = cong (E.cofψ0 θ) c₁
    pen′ : ∀ η → fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η ≡ ψᵗ Ωᵗ (ζ ++ η) ∷ []
    pen′ η = trans (penΩ ζ {y = ψᵗ θ []} {ys = []} cΩθ I η) (cong (λ u → ψᵗ Ωᵗ (ζ ++ u) ∷ []) (fsT-c1 θ (cof θ) c₁ η))
    le : ∀ {L} → Ev L (fl ⊔ (flE ⊔ φ)) → Ev L (fl ⊔ (flE ⊔ flo j))
    le ev = proj₁ ev , (proj₁ (proj₂ ev) , toFlo j (λ q → cv (proj₂ (proj₂ ev)) (suc q)))
    uj : Up zero j
    uj = Up0 I e kj
    i₀ : Inp′ j (Ωt (pred θ)) (Ωˢ j)
    i₀ = LabL-Ω (proj₁ I) (proj₁ (proj₂ I)) (proj₁ (proj₂ (proj₂ I))) (proj₂ (proj₂ (proj₂ I))) e , Ωˢ-≅ᴬ (≅ᴵ-refl j) ,
         λ _ → hΩ refl I e , (λ k → inj₂ (inj₂ (I , flo≼ e k)))
    hS : ∀ {η x} → Inp′ j η x → ∀ {ℓ} (ev : Ev ℓ (fl ⊔ (flE ⊔ φ))) →
         Inp′ j (πw (pred θ) π (fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η)) (fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P ev (cv (proj₂ (proj₂ ev)) zero))
    hS {η} {x} (lx , xx , ch) ev =
      subst (λ v → Inp′ j (ψᵗ (pred θ) (π ++ v) ∷ []) _) (sym (pen′ η))
            (frL₊ kj (proj₁ o) , slf , λ _ → proj₂ o , (λ k → inj₂ (inj₂ (I , flo≼ e k))))
      where
      lvⱼ : LvOK j j
      lvⱼ = inj₁ (⊑-suc j)
      o = WVʰ {c = j} {φ = flo j} {cv = cvFlo j} (FP-flo′ lvⱼ) lvⱼ lx (FlrLab[]-up uj (FlrLab→[] (proj₁ GP))) (LWʰ-up uj (proj₂ (proj₂ GP))) (le ev) (cv (proj₂ (proj₂ ev)) zero) I e kj (inj₂ (≅ᴵ-refl j))
      slf = fold-≅1ᴬ {φ = flo j} {φ′ = flo j} {cv = cvFlo j} {cv′ = cvFlo j} (∼ᶠ-refl flE) (gr1ʰ GE) (≅ᴵ-refl j) (∼ᶠ-refl (flo j)) xx (∼ᶠ-refl fl) (gRᴬ (proj₁ (proj₂ GP)))
               (le ev) (cv (proj₂ (proj₂ ev)) zero) (le ev) (cv (proj₂ (proj₂ ev)) zero) (≅ᴵ-refl j)
    hO : ∀ {η x} → Inp′ j η x → L0 (fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P) (π ++ fsT (ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []) η)
    hO {η} {x} (lx , xx , ch) =
      L0≡π (fold 1 φ cv E (Ord₊ˢ.up zero (intoˢ (<→◃ zero) x)) P) π (sym (pen′ η))
           (wkL0 {φ = fl ⊔ (flE ⊔ flo j)} {R = fold 1 (flo j) (cvFlo j) E x P} le
                 (OH {cv = cvFlo j} (proj₂ (ch kj)) (proj₁ (ch kj)) (toL₊ kj lx) xx GP))
```

## §7 分支与 $\Omega_\Omega$ 的闭包 (深度 1)

`FullΩ`: 带标签 $\theta$ 的分支帧 $\psi_\Omega(\zeta+\Omega_\theta)$ 是好帧 (Relative 的 `BranchΩᴬ` 的强形式). `goodΩ̂₁ʰ`: **好帧的 $\Omega_\Omega$ 闭包仍是好帧**, 即 OmegaPlus1 的闭包前提在深度 1 的内容.

```agda
  ZcK : ∀ {c} k → Zc c k (fk k)
  ZcK zero = FP-z
  ZcK (suc k) = tt
  ZcK (lim f s) = tt

  Zc₀K : ∀ k → Zc₀ k (fk k)
  Zc₀K zero = FP0-z
  Zc₀K (suc k) = tt
  Zc₀K (lim f s) = tt

  FullΩ : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ →
          GA1ʰ (fold 1 (fk (toLevel Y hY)) (λ e q → e (suc q)) E (Ωˢ (toLevel Y hY))) (ζ ++ Ωt θ)
  FullΩ {θ} Y hY lY nθ =
    ga1ʰ (FlrLabΩ-⊔ (FlrLabΩ-ext (Ωt θ) (fl1ʰ GE))
                    (FH→Ω refl (λ { ink → inj₂ (inj₂ ((Y , hY , lY , nθ) , inj₂ (≅ᴵ-refl _))) })))
         (λ {c} → WΩ Y hY lY nθ (≅ᴵ-refl _) {c} {fk (toLevel Y hY)} {λ e q → e (suc q)} (ZcK (toLevel Y hY)))
         (OΩ Y hY lY nθ (≅ᴵ-refl _) {fk (toLevel Y hY)} {λ e q → e (suc q)} (Zc₀K (toLevel Y hY)))
         (fold-≅1ᴬ (∼ᶠ-refl flE) (gr1ʰ GE) (≅ᴵ-refl _) (fk∼ (≅ᴵ-refl _)) (Ωˢ-≅ᴬ (≅ᴵ-refl _)))

  T₁ : A 1 (flE ⊔ fk zero)
  T₁ = fold 1 (fk zero) (λ e → e) E (Ωˢ (suc zero))
  Gη : (η : Ordᴵ) → A 1 (flE ⊔ fk η)
  Gη η = fold 1 (fk η) (λ e q → e (suc q)) E (Ωˢ η)

  selfT₁ : T₁ ≈₁ᴬ T₁
  selfT₁ = fold-≅1ᴬ {φ = fk zero} {φ′ = fk zero} {k₁ = suc zero} {k₂ = suc zero} {cv = λ e → e} {cv′ = λ e → e} {a = Ωˢ (suc zero)} {b = Ωˢ (suc zero)}
                    (∼ᶠ-refl flE) (gr1ʰ GE) (≅ᴵ-refl _) (fk∼ z≅) (Ωˢ-≅ᴬ (≅ᴵ-refl _))
  selfG : ∀ {η η′} → η ≅ᴵ η′ → Gη η ≈₁ᴬ Gη η′
  selfG {η} {η′} eη = fold-≅1ᴬ {φ = fk η} {φ′ = fk η′} {k₁ = η} {k₂ = η′} {cv = λ e q → e (suc q)} {cv′ = λ e q → e (suc q)} {a = Ωˢ η} {b = Ωˢ η′}
                               (∼ᶠ-refl flE) (gr1ʰ GE) eη (fk∼ eη) (Ωˢ-≅ᴬ eη)

  F1 : GA1ʰ T₁ (ζ ++ Ωt (natT 1))
  F1 = FullΩ′
    where
    FullΩ′ : GA1ʰ T₁ (ζ ++ Ωt (natT 1))
    FullΩ′ =
      ga1ʰ (FlrLabΩ-⊔ (FlrLabΩ-ext (Ωt (natT 1)) (fl1ʰ GE)) (FlrLab→Ω (λ { ink → inj₁ z≅ })))
           (λ {c} → WΩ one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _) {c} {fk zero} {λ e → e} tt)
           (OΩ one⁰ (hs hz) lab1 nf1 (≅ᴵ-refl _) {fk zero} {λ e → e} tt)
           selfT₁

  y₀ : PT
  y₀ = ψᵗ Ωᵗ (ζ ++ ΩΩ ∷ [])
  cs : cof (y₀ ∷ []) ≡ cΩ []
  cs = cΩΩ ζ {y = ΩΩ} {ys = []} refl I0
  pen : ∀ θ → fsT (y₀ ∷ []) θ ≡ ψᵗ Ωᵗ (ζ ++ Ωt θ) ∷ []
  pen θ = penΩ ζ {y = ΩΩ} {ys = []} refl I0 θ

  r : ∀ {fl L} → Ev L ((fl ⊔ flE) ⊔ fk zero) → Ev L (fl ⊔ (flE ⊔ fk zero))
  r ((u , v) , w) = u , (v , w)
  rη : ∀ {fl L η} → Ev L ((fl ⊔ flE) ⊔ fk η) → Ev L (fl ⊔ (flE ⊔ fk η))
  rη ((u , v) , w) = u , (v , w)
  r′ : ∀ {fl L} → Ev L (fl ⊔ (flE ⊔ fk zero)) → Ev L ((fl ⊔ flE) ⊔ fk zero)
  r′ (u , (v , w)) = (u , v) , w

  fwΩ : ∀ {fl π} → FlrLab fl π → FW ((fl ⊔ flE) ⊔ fk zero) π y₀ []
  fwΩ F (inr ink) = inj₁ z≅
  fwΩ F (inl (inl k)) with F k
  ... | inj₁ e = inj₁ e
  ... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → OccPre _ o)
  fwΩ {π = π} F (inl (inr k)) with fl1ʰ GE k
  ... | inj₁ e = inj₁ e
  ... | inj₂ (w , Iw , kw , o) =
    inj₂ (w , Iw , kw , λ θ → subst (λ u → Occ w (π ++ u)) (sym (pen θ)) (OccΣ π (o (Ωt θ))))

  fwΩᶜ : ∀ {c fl π} → FlrLab[ c ] fl π → FW[ c ] ((fl ⊔ flE) ⊔ fk zero) π y₀ []
  fwΩᶜ F (inr ink) = inj₁ (inj₁ (inj₁ z≅))
  fwΩᶜ F (inl (inl k)) with F k
  ... | inj₁ e = inj₁ e
  ... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , λ θ → OccPre _ o)
  fwΩᶜ {π = π} F (inl (inr k)) with fl1ʰ GE k
  ... | inj₁ e = inj₁ (inj₁ (inj₁ e))
  ... | inj₂ (w , Iw , kw , o) =
    inj₂ (w , Iw , kw , λ θ → subst (λ u → Occ w (π ++ u)) (sym (pen θ)) (OccΣ π (o (Ωt θ))))

  oΩ̂₁ : ∀ {fl} {P : Run fl} {π} → GA0ʰ P π → L0 (Ω̂A 1 E P) (π ++ ψΩᵗ (ζ ++ ΩΩ ∷ []))
  oΩ̂₁ {fl} {P} {π} GP =
    wkL0 {R = cloA 0 (wk 0 r (T₁ P)) (λ η → wk 0 rη (Gη η P))} r′
         (clo0 {φ = fl ⊔ flE} {ps = π} {y = y₀} {ys = []} {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)} (fwΩ (proj₁ GP)) cs
                  (L0≡π (wk 0 r (T₁ P)) π (sym (pen (natT 1))) (wkL0 r (g01ʰ F1 GP)))
                  (λ θ Y hY lY nθ lt → L0≡π (wk 0 rη (Gη (toLevel Y hY) P)) π (sym (pen θ)) (wkL0 rη (g01ʰ (FullΩ Y hY lY nθ) GP))))

  wΩ̂₁ : ∀ {c} → GWʰ c (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])
  wΩ̂₁ {c} {fl} {P} {π} F hP =
    wkLWʰ r′ (cloWʰ {φ = fl ⊔ flE} {ps = π} {y = y₀} {ys = []} {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)} (fwΩᶜ F) cs
                    (subst (λ u → LWʰ[ c ] (wk 0 r (T₁ P)) (π ++ u)) (sym (pen (natT 1))) (wkLWʰ r (gw1ʰ F1 F hP)))
                    (λ θ Y hY lY nθ lt → subst (λ u → LWʰ[ c ] (wk 0 rη (Gη (toLevel Y hY) P)) (π ++ u)) (sym (pen θ))
                                               (wkLWʰ rη (gw1ʰ (FullΩ Y hY lY nθ) F hP))))

  rΩ̂₁ : Ω̂A 1 E ≈₁ᴬ Ω̂A 1 E
  rΩ̂₁ {fl} {fl′} {P} {P′} s H =
    wkRᴬ r′ r′ (cloRᴬ {t = wk 0 r (T₁ P)} {g = λ η → wk 0 rη (Gη η P)} {t′ = wk 0 r (T₁ P′)} {g′ = λ η → wk 0 rη (Gη η P′)}
                      (⊔∼ s (∼ᶠ-refl flE))
                      (wkRᴬ r r (selfT₁ s H))
                      (λ η η′ eη → wkRᴬ rη rη (selfG eη s H)))

  goodΩ̂₁ʰ : GA1ʰ (Ω̂A 1 E) (ζ ++ ΩΩ ∷ [])
  goodΩ̂₁ʰ = ga1ʰ (FlrLabΩ-⊔ (FlrLabΩ-ext (ΩΩ ∷ []) (fl1ʰ GE)) (FlrLab→Ω (λ { ink → inj₁ z≅ }))) wΩ̂₁ oΩ̂₁ rΩ̂₁
```

## §8 决定性检验

```agda
goodΩ̂₀ʰ : GA1ʰ (Ω̂A 0) []
goodΩ̂₀ʰ = ga1ʰ (fl1ᴴ goodΩ̂₀ᴴ) goodΩ̂0Wʰ (λ { (F , GP , _) → g01ᴴ goodΩ̂₀ᴴ (F , GP) }) selfΩ̂0ᴬ

∅ᴿ-hon : LWʰ[ zero ] ∅ᴿ []
∅ᴿ-hon {i} {w = w} ev p (Y , hY , lY , nY) ei ki u =
  toL₊ ki (LabL-Ω Y hY lY nY ei) , hΩ refl (Y , hY , lY , nY) ei

∅ᴿ-goodʰ : GA0ʰ ∅ᴿ []
∅ᴿ-goodʰ = proj₁ ∅ᴿ-good , proj₂ ∅ᴿ-good , ∅ᴿ-hon

-- ψ₀(Ω_Ω²): 无条件定理
TΩ2-label : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) (z : zero <ᴵ ℓ) → Lab₀ (ψᵀ (Ψ (Ψ ∅ᵀ)) ev z) tΩ2
TΩ2-label ev z =
  wkL0 {φ = fz ⊔ (fk zero ⊔ fk zero)} {ψ = fz ⊔ (fk zero ⊔ (fk zero ⊔ fz))} {R = Ω̂A 1 (Ω̂A 0) ∅ᴿ}
       (λ {L} (ev′ : Ev L (fz ⊔ (fk zero ⊔ (fk zero ⊔ fz)))) → proj₁ ev′ , (proj₁ (proj₂ ev′) , proj₁ (proj₂ (proj₂ ev′))))
       (Main.oΩ̂₁ goodΩ̂₀ʰ ∅ᴿ-goodʰ) ev z tΩ2-NF
```

**中间检验.** `TΩθ-label`: 对一切带标签的 $\theta$, $\psi_0(\psi_\Omega(\Omega_\theta))$ 的标签; 记号侧只要 `NF₁`. 第 4 层 ($\Omega_4$, OmegaSqA 的停点) 与极限层 ($\Omega_\omega$, RelativeBase §9 的反例位置).

```agda
TΩθ-label : ∀ {θ} (Y : Ordᶜ zero) (hY : HS Y) → Lab Y θ → NF₁ θ → NF₁ (ψΩ₀ (Ωt θ)) →
            ∀ {ℓ} ev (z : zero <ᴵ ℓ) →
            Lab₀ (ψᵀ (Ψ (tlᵀ (flo (toLevel Y hY)) (cvFlo (toLevel Y hY)) (Ωˢ (toLevel Y hY)))) ev z) (ψΩ₀ (Ωt θ))
TΩθ-label Y hY lY nθ nf ev z =
  Main.OΩ goodΩ̂₀ʰ Y hY lY nθ (≅ᴵ-refl _) {flo (toLevel Y hY)} {cvFlo (toLevel Y hY)} (Main.Zc₀-flo goodΩ̂₀ʰ (toLevel Y hY)) ∅ᴿ-goodʰ ev z nf
```

```agda
natω : T
natω = ψᵗ [] (natT 1) ∷ []

ω-NF : NF₁ natω
ω-NF = NF₁-fsn (NF₁-fsn (NF₁-fsn (NF₁-fsn tΩ1-NF refl 0) refl 1) refl 0) refl 0

fsω : ∀ n → fsn natω n ≡ natT n
fsω n = trans (fs-rep [] 𝟏 [] refl n) (rep𝟏 n)
  where
  rep𝟏 : ∀ m → replicate m (ψᵗ [] []) ≡ natT m
  rep𝟏 zero = refl
  rep𝟏 (suc m) = cong (𝟏 ∷_) (rep𝟏 m)

nfN : ∀ n → NF₁ (natT n)
nfN n = subst NF₁ (fsω n) (NF₁-fsn ω-NF refl n)

labN : ∀ n → Lab (natᶜ n) (natT n)
labN zero = l0 refl z≅
labN (suc n) = l1 (E.cof-natT n) (≅-refl⁰ _) (subst (Lab _) (sym (E.pred-natT n)) (labN n))

-- ψ₀(ψ_Ω(Ω₄)) = ψ₀(Ω_Ω·Ω₄): OmegaSqA 的停点
tΩ₄ : T
tΩ₄ = ψΩ₀ (Ωt (natT 4))

tΩ₄-NF : NF₁ tΩ₄
tΩ₄-NF = tO-desc-NF (walkD d₀ (1 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 4 ∷ []) (refl , refl , refl , refl , refl , refl , refl , tt))

TΩ₄-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) →
            Lab₀ (ψᵀ (Ψ (tlᵀ (flo (toLevel (natᶜ 4) (natᶜ-HS 4))) (cvFlo (toLevel (natᶜ 4) (natᶜ-HS 4))) (Ωˢ (toLevel (natᶜ 4) (natᶜ-HS 4))))) ev z) tΩ₄
TΩ₄-label = TΩθ-label (natᶜ 4) (natᶜ-HS 4) (labN 4) (nfN 4) tΩ₄-NF

-- ψ₀(ψ_Ω(Ω_ω)): 极限层, RelativeBase §9 的反例位置
labω : Lab ωᶜ natω
labω = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab (natᶜ n)) (sym (fsω n)) (labN n))

tΩω : T
tΩω = ψΩ₀ (Ωt natω)

tΩω-NF : NF₁ tΩω
tΩω-NF = NF₁-fsn (NF₁-fsn (NF₁-fsn (NF₁-fsn (NF₁-fsn tΩ2-NF refl 1) refl 0) refl 1) refl 0) refl 0

TΩω-label : ∀ {ℓ} ev (z : zero <ᴵ ℓ) →
            Lab₀ (ψᵀ (Ψ (tlᵀ (flo (toLevel ωᶜ ωᶜ-HS)) (cvFlo (toLevel ωᶜ ωᶜ-HS)) (Ωˢ (toLevel ωᶜ ωᶜ-HS)))) ev z) tΩω
TΩω-label = TΩθ-label ωᶜ ωᶜ-HS labω ω-NF tΩω-NF
```

## §9 结论与边界

**修正的影响.** Uniform2 的九个标签与 $\Omega_3$、第 2 层指数的标签全部原样成立. 改动集中在界的定义 (Uniform3Base §3) 与 `up (self n)` 子句; 标签证明本身几乎不动.

**证明里新增的不是定义.** 地板修正之后, 剩下的是 OmegaSqA §6 记下的那件事: 第 $\ge3$ 层尾巴的目标 0 部分要 "首项见证沿输出遗传". 它的精确形式是 `Hn` (Uniform3Hon): `LabL` 含伪树 (第 3 层的字面 `suc zero` 带标签 $1$), 它们在目标 0 处确实没有证书; 真正当尾巴用的只有链点, 而链点是输出, 输出的裸 $\Omega_w$ 节点字面是 `Ωˢ ℓ`. `Hn` 不进入树的定义, 只是标签理论的一个不变量.

**字面与模 $\cong$.** `TΩ2-label` 等都是对一切环境的定理; 字面 `refl` 只在 Uniform3Walk 与记号侧.

**未做.** 深度 $\ge2$ 的闭包定理, 见 [Uniform3Plus1](Uniform3Plus1.lagda.md).
