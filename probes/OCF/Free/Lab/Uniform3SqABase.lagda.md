# Uniform3SqABase (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform3SqABase](../../Align/Uniform3SqABase.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform3SqABase where

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
open import OCF.Free.Lab.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_; trˢ; tr⁻ˢ; H1-pen)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Free.Lab.Bachmann using (pen→<; gt→≤; clash)
open import OCF.Free.Lab.Closure using (Pen)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-fsn)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.Stage2Label using (one⁰)
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.OmegaExpBase using (πw; OccΣ; cofW; repW; ωW; γW; gtW; penW; H1W; ne-w; 1<γ)
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base
open import OCF.Free.Lab.Uniform3Depth1 using (wkL0; cωΩ; cΩΩ; penΩ)
open import OCF.Free.Lab.Uniform3Rel
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; sucT; cmpᵀ; lt; eq; gt; []<; cofA)
  renaming (ψ to ψᵗ)
open GRᴬ public
```

## §1 $\cong^\mathsf A$ 的反演

```agda
≅ˢ₀→≅ᴬ : ∀ {x y : Ordˢ zero} → x ≅ˢ y → x ≅ᴬ y
≅ˢ₀→≅ᴬ z≅ = zᴬ
≅ˢ₀→≅ᴬ (s≅ d) = sᴬ (≅ˢ₀→≅ᴬ d)
≅ˢ₀→≅ᴬ (l≅ h) = lᴬ (λ n → ≅ˢ₀→≅ᴬ (h n))
≅ˢ₀→≅ᴬ (lᵢ≅ {p = ()} e h)
≅ˢ₀→≅ᴬ (upˡ {r = ()} d)
≅ˢ₀→≅ᴬ (upʳ {r = ()} d)
≅ˢ₀→≅ᴬ (ŝ≅ k ec et eg) = ŝᴬ k ec (≅ˢ₀→≅ᴬ et) (λ η e η′ e′ eη → ≅ˢ₀→≅ᴬ (eg η e η′ e′ eη))
≅ˢ₀→≅ᴬ (ĉ≅ ec dt dg eo eO) = ĉᴬ ec dt dg (≅ˢ₀→≅ᴬ eo) (λ η e η′ e′ eη → ≅ˢ₀→≅ᴬ (eO η e η′ e′ eη))
```

## §2 深度 0 的标签理论在 $\cong^\mathsf A$ 上

```agda
H0ᴬ : ∀ {φ j} → (Ordˢ j → Run φ) → (T → T) → Set
H0ᴬ {j = j} H lab = ∀ η (x : Ordˢ j) → LabL x η → x ≅ᴬ x → L0 (H x) (lab η) × (H x ≈ᴬ H x)

limᵢ0ᴬ : ∀ {φ j ν} {ps : T} {y : PT} {ys : T} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {H : Ordˢ j → Run φ} →
         cof (y ∷ ys) ≡ cΩ ν → (Iν : Idx ν) → j ≅ᴵ lvI Iν →
         (∀ η x → LabL x η → LW (H x) (ps ++ fsT (y ∷ ys) η)) → H0ᴬ H (λ η → ps ++ fsT (y ∷ ys) η) →
         L0 (limᵢA 0 ac H) (ps ++ (y ∷ ys))
limᵢ0ᴬ {j = zero} {ν = ν} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys [] c₀ refl m)) (proj₂ (outp m))))
  where
  c₀ : cof (y ∷ ys) ≡ cΩ []
  c₀ = trans c (cong cΩ (kdI Iν (sym (kd-≅ ej))))
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c₀)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₂ z≅)
  nfγ : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
  nfγ m = subst NF₁ (gtW [] ps y ys [] c₀ refl m) (NF₁-fsn nu cω′ m)
  atm : ∀ m → Atomᴸ (chainA ac H ev m) (γW ps (y ∷ ys) [] m)
  atm zero    = Ωˢ-refl zero , gs gz , l1 refl (s≅ z≅) (l0 refl z≅)
  atm (suc m) = ≅ᴬ→≅ˢ₀ (proj₂ (h0 _ _ (atm m) (≅ˢ₀→≅ᴬ (proj₁ (atm m)))) ev (ac ev) ev (ac ev) z≅) ,
                proj₁ (h0 _ _ (atm m) (≅ˢ₀→≅ᴬ (proj₁ (atm m)))) ev (ac ev) (nfγ m)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)))
  outp m = proj₁ (h0 _ _ (atm m) (≅ˢ₀→≅ᴬ (proj₁ (atm m)))) ev p (nfγ m)
limᵢ0ᴬ {j = suc j′} {ν = []} c Iν ej hW h0 ev p nu = ⊥-elim (tf (trans (sym (kdI[] Iν)) (sym (kd-≅ ej))))
limᵢ0ᴬ {j = suc j′} {ν = v ∷ vs} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₁ (z≺I Iν ej (λ ())))
  nf : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  chainL : ∀ m → LabL (chainA ac H ev m) (γW ps (y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
  chainL (suc m) = hW _ _ (chainL m) ev (ac ev) Iν ej refl
  selfC : ∀ m → chainA ac H ev m ≅ᴬ chainA ac H ev m
  selfC zero    = Ωˢ-≅ᴬ (≅ᴵ-refl _)
  selfC (suc m) = proj₂ (h0 _ _ (chainL m) (selfC m)) ev (ac ev) ev (ac ev) (≅ᴵ-refl _)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  outp m = proj₁ (h0 _ _ (chainL m) (selfC m)) ev p (nf m)
limᵢ0ᴬ {j = lim f s} {ν = []} c Iν ej hW h0 ev p nu = ⊥-elim (tf (trans (sym (kdI[] Iν)) (sym (kd-≅ ej))))
limᵢ0ᴬ {j = lim f s} {ν = v ∷ vs} {ps = ps} {y = y} {ys = ys} {ac = ac} {H = H} c Iν ej hW h0 ev p nu =
  subst (λ W → Lab₀ W (ψ₀ᵗ (ps ++ (y ∷ ys)))) (sym eqf)
        (limᴸ nu cω′ (λ m → proj₁ (outp m)) (λ m → subst (Lab _) (sym (gtW [] ps y ys (v ∷ vs) c refl m)) (proj₂ (outp m))))
  where
  cω′ = trans (cofW [] ps y ys) (cong (cofA []) c)
  eqf = fold1A {ac = ac} {H = H} {ev = ev} {p = p} (inj₁ (z≺I Iν ej (λ ())))
  nf : ∀ m → NF₁ (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  nf m = subst NF₁ (gtW [] ps y ys (v ∷ vs) c refl m) (NF₁-fsn nu cω′ m)
  chainL : ∀ m → LabL (chainA ac H ev m) (γW ps (y ∷ ys) (v ∷ vs) m)
  chainL zero    = LabL-Ω (proj₁ Iν) (proj₁ (proj₂ Iν)) (proj₁ (proj₂ (proj₂ Iν))) (proj₂ (proj₂ (proj₂ Iν))) ej
  chainL (suc m) = hW _ _ (chainL m) ev (ac ev) Iν ej refl
  selfC : ∀ m → chainA ac H ev m ≅ᴬ chainA ac H ev m
  selfC zero    = Ωˢ-≅ᴬ (≅ᴵ-refl _)
  selfC (suc m) = proj₂ (h0 _ _ (chainL m) (selfC m)) ev (ac ev) ev (ac ev) (≅ᴵ-refl _)
  outp : ∀ m → Lab₀ (H (chainA ac H ev m) ev p) (ψ₀ᵗ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) (v ∷ vs) m)))
  outp m = proj₁ (h0 _ _ (chainL m) (selfC m)) ev p (nf m)
```

## §3 依目标的行引理

```agda
Up-ij : ∀ {c i j} → Up c i → (i ≺ᴵ j) ⊎ (i ≅ᴵ j) → Up c j
Up-ij u (inj₁ s) = Up-≺ u s
Up-ij u (inj₂ e) = Up-≅ u e

module _ {c φ} {ps : T} {y : PT} {ys : T} where
  limWᶜ : ∀ {F : ℕ → Run φ} → cof (y ∷ ys) ≡ cω → (∀ n → LW[ c ] (F n) (ps ++ fsn (y ∷ ys) n)) →
          LW[ c ] (limA 0 F) (ps ++ (y ∷ ys))
  limWᶜ {F} cc h {w = w} ev p Iw ei ki u =
    gl (trans (cofW w ps y ys) (cong (cofA w) cc)) (λ n → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cc n)) (h n ev p Iw ei ki u))

  sucWᶜ : ∀ {R : Run φ} → cof (y ∷ ys) ≡ c1 → LW[ c ] R (ps ++ pred (y ∷ ys)) → LW[ c ] (sucRun R) (ps ++ (y ∷ ys))
  sucWᶜ {R} cc h {w = w} ev p Iw ei ki u =
    gl (trans (cofW w ps y ys) (cong (cofA w) cc))
       (λ m → subst (LabL₊ _ Ll _) (sym (repW w ps y ys cc m)) (LRep ki (h ev p Iw ei ki u) m))

module _ {c φ c₀ t₀} {g : (η : Ordᴵ) → c₀ ⊑ᴵ η → Z} {ps : T} {y : PT} {ys : T} where
  ĉWᶜ : ∀ {O₀ : Run φ} {O : (η : Ordᴵ) → c₀ ⊑ᴵ η → Run φ} → cof (y ∷ ys) ≡ cω → (K : CCᴸ c₀ t₀ g) →
        LW[ c ] O₀ (ps ++ fsn (y ∷ ys) 0) → (∀ k → LW[ c ] (O (lvK K k) (dxK K k)) (ps ++ fsn (y ∷ ys) (suc k))) →
        LW[ c ] (ĉA 0 c₀ t₀ g O₀ O) (ps ++ (y ∷ ys))
  ĉWᶜ cw K h₀ hk {w = w} ev p Iw ei ki u =
    gĉ (trans (cofW w ps y ys) (cong (cofA w) cw)) K
       (subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw 0)) (h₀ ev p Iw ei ki u))
       (λ k → subst (LabL₊ _ Ll _) (sym (ωW w ps y ys cw (suc k))) (hk k ev p Iw ei ki u))

module _ {c φ c₀ w′} {ps : T} {y : PT} {ys : T} {T₀ : Run φ} {G : (η : Ordᴵ) → c₀ ⊑ᴵ η → Run φ}
         (cs : cof (y ∷ ys) ≡ cΩ []) (Iw′ : Idx w′) (bw : c₀ ⊑ᴵ suc (lvI Iw′)) (ob : Ob w′ ps y ys) where
  ŝWᶜ : LW[ c ] T₀ (ps ++ fsT (y ∷ ys) (natT 1)) →
        (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → (e : c₀ ⊑ᴵ toLevel Y hY) → LW[ c ] (G (toLevel Y hY) e) (ps ++ fsT (y ∷ ys) θ)) →
        LW[ c ] (ŝA 0 c₀ T₀ G) (ps ++ (y ∷ ys))
  ŝWᶜ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  ŝWᶜ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) cs) (H1-pen x xs))) Iw′ bw
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys cs θ)) (od (ob θ)))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs (natT 1))) (h₀ ev p Iw ei ki u))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs θ)) (hg θ Y hY lY nθ lt e ev p Iw ei ki u))
```

## §4 地板策略、层号条件与一般层号尾巴的 W 定理

```agda
FP : Ordᴵ → Flr → Set
FP c φ = ∀ {K} (k : InF K φ) → IgnK c k ⊎ (K ≅ᴵ one)

IgnL→FP : ∀ {c φ} → IgnL c φ → FP c φ
IgnL→FP g k = inj₁ (g k)

data Low : Ordᴵ → Set where
  lw0 : Low zero
  lw1 : Low one
  lw2 : Low two

LvOK : Ordᴵ → Ordᴵ → Set
LvOK c k = (k ⊑ᴵ suc c) ⊎ Low k

FP-flo′ : ∀ {c k} → LvOK c k → FP c (flo k)
FP-flo′ {k = k} (inj₁ le) = IgnL→FP (floIgn k le)
FP-flo′ (inj₂ lw0) ()
FP-flo′ (inj₂ lw1) ink = inj₁ (inj₁ (inj₁ z≅))
FP-flo′ (inj₂ lw2) ink = inj₂ (≅ᴵ-refl one)

LvOK-pred : ∀ {c k′} → LvOK c (suc k′) → LvOK c k′
LvOK-pred (inj₁ le) = inj₁ (⊑ᴵ-trans (≼→⊑ (s⊑s→≼ le)) (⊑-suc _))
LvOK-pred (inj₂ lw1) = inj₂ lw0
LvOK-pred (inj₂ lw2) = inj₂ lw1

FP-flo : ∀ {c k′} → LvOK c (suc k′) → FP c (flo k′)
FP-flo lv = FP-flo′ (LvOK-pred lv)

LvOK-self : ∀ {c f s} → LvOK c (lim f s) → ∀ n → LvOK c (f n)
LvOK-self (inj₁ le) n = inj₁ (⊑ᴵ-trans (Sim→⊑ᴵ (λ q → lim n q)) le)
LvOK-self (inj₂ ()) n
```

```agda
FlrLabΩ : Flr → T → Set
FlrLabΩ φ ζ = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) ×
                                                              (∀ b → Occ w (ψᵗ Ωᵗ (ζ ++ b) ∷ []))

FlrLab[]-mono : ∀ {c φ ps qs} → (∀ {w} → Occ w ps → Occ w qs) → FlrLab[ c ] φ ps → FlrLab[ c ] φ qs
FlrLab[]-mono f F k with F k
... | inj₁ e = inj₁ e
... | inj₂ (w , Iw , kw , o) = inj₂ (w , Iw , kw , f o)
```

## §5 $\Omega_\Omega$ 闭包的好帧
