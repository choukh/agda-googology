# SystemOmega (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [SystemOmega](../../Align/SystemOmega.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.SystemOmega where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst) 
open import OCF.Free.Lab.Level using (Ordᴵ; _≺ᴵ_; _≅ᴵ_)
open import OCF.Free.Lab.Label using (System; module GS; St; prev)
open import OCF.Free.Lab.Closure using (lt→<; lt→<ᴾ; <→lt; eq→≡ᴾ; <ᵀ-trans)
open import OCF.Free.Lab.Bachmann using (fs<ᵀ; gt→<)
open import OCF.Free.Lab.Correspond using (γᴱ; βᴱ)
open import OCF.Free.Lab.Standard using (_≤ᵀ_; <≤-trans; []≤; Ctbl; c[]; c∷; Ctbl-pred; Ctbl-fsn; Ctbl-≤; Ctbl-cof; Desc; d₀; dω; d₁; diag-Ctbl)
import OCF.Free.Lab.Standard as Std
open import OCF.Free.Lab.Stage2 using (Ωᵗ; t2; γ′ᴱ)
open import OCF.Free.Lab.StandardOmega
import OCF.Align.EBO as E
```

```agda
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; pred; sucT; Ωt; natT; fsn; fsT;
              _<ᵀ_; []<; hd<; tl<; lv<; ar<)
       renaming (ψ to ψᵗ)
```

## §1 派发事实

```agda
Ω+ : T → T
Ω+ c = Ω₁ ∷ c

cmp-CΩ : ∀ {v} → Ctbl v → ∀ c → cmpᵀ v (Ω+ c) ≡ lt
cmp-CΩ c[]      c = refl
cmp-CΩ (c∷ cv)  c = refl

cmp-ΩC : ∀ {v} → Ctbl v → ∀ c → cmpᵀ (Ω+ c) v ≡ gt
cmp-ΩC c[]      c = refl
cmp-ΩC (c∷ cv)  c = refl
```

```agda
Ctbl-suc : ∀ {c} → Ctbl c → Ctbl (sucT c)
Ctbl-suc c[]     = c∷ c[]
Ctbl-suc (c∷ c)  = c∷ (Ctbl-suc c)
```

## §3 出现与支配

```agda
data Occ (x : T) : T → Set where
  oh : ∀ {a xs}   → Occ x (ψᵗ x a ∷ xs)
  od : ∀ {y a xs} → Occ x a → Occ x (ψᵗ y a ∷ xs)
  os : ∀ {y a xs} → Occ x y → Occ x (ψᵗ y a ∷ xs)
  ot : ∀ {y xs}   → Occ x xs → Occ x (y ∷ xs)

occVis : ∀ {y e xs t} → Occ (ψᵗ y e ∷ xs) t → Vis₁ [] e t
occVis oh     = vs ([]≤ _) (vh ([]≤ _))
occVis (od o) = vd ([]≤ _) (occVis o)
occVis (os o) = vs ([]≤ _) (occVis o)
occVis (ot o) = vt (occVis o)
```

```agda
tl<₁ : ∀ {x ts} → NF₁ (x ∷ ts) → ts <ᵀ x ∷ ts
tl<₁ (n∷ _ n[] _) = []<
tl<₁ {x} (n∷ _ (n∷ {x = y} ny nys hy) (inj₁ e)) = hd< (lt→<ᴾ y x e)
tl<₁ {x} (n∷ _ (n∷ {x = y} ny nys hy) (inj₂ e)) with eq→≡ᴾ y x e
... | refl = tl< (tl<₁ (n∷ ny nys hy))

occ< : ∀ {x t} → NF₁ t → Ctbl t → Occ x t → Ctbl x → x <ᵀ t
occ< nt (c∷ ct) oh cx = []<
occ< (n∷ (nψ _ _ na g) _ _) (c∷ ct) (od o) c[]      = []<
occ< (n∷ (nψ _ _ na g) _ _) (c∷ ct) (od o) (c∷ cx)  = hd< (ar< (g (occVis o)))
occ< nt (c∷ ct) (os ()) cx
occ< (n∷ nx nts h) (c∷ ct) (ot o) cx = <ᵀ-trans (occ< nts ct o cx) (tl<₁ (n∷ nx nts h))
```

## §6 结论与边界
