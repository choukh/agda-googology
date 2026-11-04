# Uniform3Full (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform3Full](LadderLabZUniform3Full.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform3Full where

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
open import OCF.Align.OrdLabZPrefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; _+ˢ_)
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fsT-c1; fs-rep)
open import OCF.Align.LadderLabZStandardOmega using (NF₁; NF₁-fsn; NF₁-pred; walkD; tO-desc-NF)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ)
open import OCF.Align.OrdLabZStage2Label using (one⁰; Lab-oc)
open import OCF.Align.OrdLabZDecoupleBase using (ΩΩ)
open import OCF.Align.Standard using (d₀)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI; kdI; kdI[]; Ieq; Lab0[])
open import OCF.Align.OrdLabZGoodLBase
open import OCF.Align.OrdLabZOmegaExpBase using (OccΣ; repW; ωW; πw; γW; cofW; gtW; fsT-ne)
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZUniform3Base
open import OCF.Align.OrdLabZUniform3Depth1 using (wkL0; cωΩ; cΩΩ; penΩ)
open import OCF.Align.OrdLabZUniform3Rel
open import OCF.Align.OrdLabZUniform3SqABase
open import OCF.Align.OrdLabZUniform3SqA using (FP0; LW0→LW; Up0)
open import OCF.Align.OrdLabZUniform3Hon
open import OCF.Align.LadderLabZUniform3Full public using (pred-Pr)
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; []<; 𝟏; cofA; sucT; cmpᵀ) renaming (ψ to ψᵗ)
open GRᴬ
```

## §1 带诚实性的好前缀与好帧

```agda
GRH : ∀ {φ} → Run φ → T → Set
GRH R u = GRᴬ R u × LWʰ[ zero ] R u

GA0ʰ : ∀ {fl} → Run fl → T → Set
GA0ʰ {fl} P π = FlrLab fl π × GRH P π

```

## §3 地板见证的搬运

```agda
FH-pred : ∀ {φ u v vs} → NB (ψᵗ u v ∷ vs) → cof (ψᵗ u v ∷ vs) ≡ c1 → FH φ (ψᵗ u v ∷ vs) → FH φ (pred (ψᵗ u v ∷ vs))
FH-pred {u = u} {v} {vs} nb c F k with F k | pred-Pr {u} {v} {vs} nb c
... | inj₁ g | _ = inj₁ g
... | inj₂ (inj₁ e) | _ = inj₂ (inj₁ e)
... | inj₂ (inj₂ h) | v′ , vs′ , eq = inj₂ (inj₂ (subst (HK _) (sym eq) h))

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

## §8 决定性检验

```agda
∅ᴿ-hon : LWʰ[ zero ] ∅ᴿ []
∅ᴿ-hon {i} {w = w} ev p (Y , hY , lY , nY) ei ki u =
  toL₊ ki (LabL-Ω Y hY lY nY ei) , hΩ refl (Y , hY , lY , nY) ei

∅ᴿ-goodʰ : GA0ʰ ∅ᴿ []
∅ᴿ-goodʰ = proj₁ ∅ᴿ-good , proj₂ ∅ᴿ-good , ∅ᴿ-hon

-- ψ₀(Ω_Ω²): 无条件定理
```

## §9 结论与边界
