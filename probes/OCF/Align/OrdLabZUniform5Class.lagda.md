# Uniform5Class (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform5Class](LadderLabZUniform5Class.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform5Class where

open import Data.Nat using (ℕ; zero; suc)
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
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.LadderLabZStandardOmega using (NF₁)
open import OCF.Align.LadderLabZSystemOmega using (Occ; oh; od; os; ot; oτ; TailOf; th; ts)
open import OCF.Align.OrdLabZDecouple using (Idx; lvI)
open import OCF.Align.OrdLabZGoodLBase
open import OCF.Align.OrdLabZUniformS
open import OCF.Align.OrdLabZUniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Align.OrdLabZUniform3Rel
open import OCF.Align.OrdLabZUniform3SqABase
open import OCF.Align.OrdLabZUniform3Hon
open import OCF.Align.OrdLabZUniform3Depth2Class
open import OCF.Align.OrdLabZUniform3Depth2W using (InpW; CH; FHν)
open import OCF.Align.OrdLabZUniform3Full using (FlrLab[]-up; LWʰ-up)
open import OCF.Align.OrdLabZUniform5Head
open import OCF.Align.OrdLabZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2)
open import OCF.Free.Tree
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
```

## §1 模式与地板

```agda
data Mode : Set where
  hon : Mode
  wkm : Ordᴵ → Mode

Fw : Mode → Flr → T → PT → T → Set
Fw hon     φ ps y ys = FW₀ φ ps y ys
Fw (wkm c) φ ps y ys = FW[ c ] φ ps y ys

FlU : Mode → Flr → T → Set
FlU hon     φ u = ∀ {K} → InF K φ → (K ≅ᴵ zero) ⊎ (K ≅ᴵ one) ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × Occ w u
FlU (wkm c) φ u = ∀ {K} (k : InF K φ) → IgnK c k ⊎ (K ≅ᴵ one) ⊎ Σ T λ w → Σ (Idx w) λ Iw → (K ≼ lvI Iw) × Occ w u

data Cv : Mode → Mode → Set where
  cv-h : ∀ {m} → Cv hon m
  cv-w : ∀ {c c′} → Up c c′ → Cv (wkm c) (wkm c′)
```

## §2 `Ld`

```agda
FC : Bool → Ordᴵ → T → Set
FC false c u = ⊤
FC true  c u = FlrLab (flo c) u
```

## §3 模式转换

```agda
Cv-tr : ∀ {a b d} → Cv a b → Cv b d → Cv a d
Cv-tr cv-h q = cv-h
Cv-tr (cv-w u) (cv-w v) = cv-w (≼-trans u v)

Cv-refl : ∀ m → Cv m m
Cv-refl hon = cv-h
Cv-refl (wkm c) = cv-w (≼-refl c)

IgnK-up′ : ∀ {c c′ K φ} {k : InF K φ} → Up c c′ → IgnK c k → IgnK c′ k
IgnK-up′ u (inj₁ (inj₁ e0)) = inj₁ (inj₁ e0)
IgnK-up′ u (inj₁ (inj₂ kc)) = inj₁ (inj₂ (≼-trans kc u))
IgnK-up′ u (inj₂ (b , le))  = inj₂ (b , ⊑ᴵ-trans le (sB u))

Fw-cv : ∀ {a b φ ps y ys} → Cv a b → Fw a φ ps y ys → Fw b φ ps y ys
Fw-cv {b = hon} cv-h F = F
Fw-cv {b = wkm c} cv-h F = FW→FW[] F
Fw-cv (cv-w u) F k with F k
... | inj₁ g = inj₁ (IgnK-up′ u g)
... | inj₂ w = inj₂ w

FlU-cv : ∀ {a b φ u} → Cv a b → FlU a φ u → FlU b φ u
FlU-cv {b = hon} cv-h F = F
FlU-cv {b = wkm c} cv-h F k with F k
... | inj₁ e0 = inj₁ (inj₁ (inj₁ e0))
... | inj₂ (inj₁ e1) = inj₂ (inj₁ e1)
... | inj₂ (inj₂ w) = inj₂ (inj₂ w)
FlU-cv (cv-w u) F k with F k
... | inj₁ g = inj₁ (IgnK-up′ u g)
... | inj₂ w = inj₂ w

FlM : Mode → Flr → T → Set
FlM hon     φ u = FlrLab φ u
FlM (wkm c) φ u = FlrLab[ c ] φ u

FlM-cv : ∀ {a b φ u} → Cv a b → FlM a φ u → FlM b φ u
FlM-cv {b = hon} cv-h F = F
FlM-cv {b = wkm c} cv-h F = FlrLab→[] F
FlM-cv (cv-w u) F = FlrLab[]-up u F
```
