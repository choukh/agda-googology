# OmegaExpBase (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [OmegaExpBase](../../Align/OmegaExpBase.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.OmegaExpBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Data.List.Properties using (++-identityʳ; ++-assoc) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Symbolic using (Mlev; σ1)
open import OCF.Free.Lab.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; addˢ; _+ˢ_; z<suc; H1-pen; H1-fsT; trˢ; tr⁻ˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; fs-rep; fs-ω)
open import OCF.Free.Lab.Bachmann using (fs-gt; pen→<; gt→≤; clash)
open import OCF.Free.Lab.Closure using (Pen; fsT₊-pen′; lt→<)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-pred; NF₁-fsn; walk; walkD)
open import OCF.Free.Lab.Standard using (Desc; d₀; Ctbl; c[]; c∷)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot; occ<)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Stage2Label using (one⁰; Lab-oc)
open import OCF.Free.Lab.DecoupleBase using (ΩΩ; ŝ-reflg)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Ilt; Ieq; kdI; kdI′; gtν; kdI[]; cofP)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Aux public using (σ⊥)
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; _<ᵀ_; γT; sucT; cmpᵀ; Cmp; lt; eq; gt;
              []<; hd<; tl<; lv<; ar<; cofA; cofψ0; cofψ₊) renaming (ψ to ψᵗ)
```

## §1 记号

```agda
πw : T → T → T → T
πw w ps b = ψᵗ w (ps ++ b) ∷ []

onCons : (P : T → Set) → (∀ x xs → P (x ∷ xs)) → ∀ ps y ys → P (ps ++ (y ∷ ys))
onCons P h []       y ys = h y ys
onCons P h (x ∷ ps) y ys = h x (ps ++ (y ∷ ys))

cofΣ : ∀ ps y ys → cof (ps ++ (y ∷ ys)) ≡ cof (y ∷ ys)
cofΣ []           y ys = refl
cofΣ (x ∷ [])     y ys = refl
cofΣ (x ∷ x′ ∷ ps) y ys = cofΣ (x′ ∷ ps) y ys

predΣ : ∀ ps y ys → pred (ps ++ (y ∷ ys)) ≡ ps ++ pred (y ∷ ys)
predΣ []            y ys = refl
predΣ (x ∷ [])      y ys = refl
predΣ (x ∷ x′ ∷ ps) y ys = cong (x ∷_) (predΣ (x′ ∷ ps) y ys)

fsnΣ : ∀ ps y ys m → fsn (ps ++ (y ∷ ys)) m ≡ ps ++ fsn (y ∷ ys) m
fsnΣ []            y ys m = refl
fsnΣ (x ∷ [])      y ys m = refl
fsnΣ (x ∷ x′ ∷ ps) y ys m = cong (x ∷_) (fsnΣ (x′ ∷ ps) y ys m)

fsTΣ : ∀ ps y ys θ → fsT (ps ++ (y ∷ ys)) θ ≡ ps ++ fsT (y ∷ ys) θ
fsTΣ []            y ys θ = refl
fsTΣ (x ∷ [])      y ys θ = refl
fsTΣ (x ∷ x′ ∷ ps) y ys θ = cong (x ∷_) (fsTΣ (x′ ∷ ps) y ys θ)

OccΣ : ∀ {w a} ps → Occ w a → Occ w (ps ++ a)
OccΣ []       o = o
OccΣ (x ∷ ps) o = ot (OccΣ ps o)

cofW : ∀ w ps y ys → cof (πw w ps (y ∷ ys)) ≡ cofA w (cof (y ∷ ys))
cofW w []       y ys = refl
cofW w (x ∷ ps) y ys = cong (cofA w) (cofΣ (x ∷ ps) y ys)

repW : ∀ w ps y ys → cof (y ∷ ys) ≡ c1 → ∀ m → fsn (πw w ps (y ∷ ys)) m ≡ replicate m (ψᵗ w (ps ++ pred (y ∷ ys)))
repW w ps y ys c m =
  trans (onCons (λ a → cof a ≡ c1 → fsn (ψᵗ w a ∷ []) m ≡ replicate m (ψᵗ w (pred a))) (λ x xs c′ → fs-rep w x xs c′ m)
                ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → replicate m (ψᵗ w t)) (predΣ ps y ys))

ωW : ∀ w ps y ys → cof (y ∷ ys) ≡ cω → ∀ m → fsn (πw w ps (y ∷ ys)) m ≡ πw w ps (fsn (y ∷ ys) m)
ωW w ps y ys c m =
  trans (onCons (λ a → cof a ≡ cω → fsn (ψᵗ w a ∷ []) m ≡ ψᵗ w (fsn a m) ∷ []) (λ x xs c′ → fs-ω w x xs c′ m)
                ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → ψᵗ w t ∷ []) (fsnΣ ps y ys m))

γW : T → T → T → ℕ → T
γW ps a ν zero    = Ωt ν
γW ps a ν (suc m) = πw ν ps (fsT a (γW ps a ν m))

γW-eq : ∀ ps y ys ν m → γT (ps ++ (y ∷ ys)) ν m ≡ γW ps (y ∷ ys) ν m
γW-eq ps y ys ν zero    = refl
γW-eq ps y ys ν (suc m) =
  cong (λ t → ψᵗ ν t ∷ []) (trans (cong (fsT (ps ++ (y ∷ ys))) (γW-eq ps y ys ν m)) (fsTΣ ps y ys _))

gtW : ∀ w ps y ys ν → cof (y ∷ ys) ≡ cΩ ν → cmpᵀ (sucT ν) w ≡ gt → ∀ m →
      fsn (πw w ps (y ∷ ys)) m ≡ πw w ps (fsT (y ∷ ys) (γW ps (y ∷ ys) ν m))
gtW w ps y ys ν c em m =
  trans (onCons (λ a → cof a ≡ cΩ ν → fsn (ψᵗ w a ∷ []) m ≡ ψᵗ w (fsT a (γT a ν m)) ∷ [])
                (λ x xs c′ → fs-gt w x xs ν c′ em m) ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → ψᵗ w t ∷ []) (trans (cong (fsT (ps ++ (y ∷ ys))) (γW-eq ps y ys ν m)) (fsTΣ ps y ys _)))

penW : ∀ w ps y ys ν → cof (y ∷ ys) ≡ cΩ ν → Pen (cmpᵀ (sucT ν) w) → ∀ η →
       fsT (πw w ps (y ∷ ys)) η ≡ πw w ps (fsT (y ∷ ys) η)
penW w ps y ys ν c pn η =
  trans (onCons (λ a → cof a ≡ cΩ ν → fsT (ψᵗ w a ∷ []) η ≡ ψᵗ w (fsT a η) ∷ [])
                (λ x xs c′ → fsT₊-pen′ w (x ∷ xs) ν (cof (x ∷ xs)) c′ pn η) ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → ψᵗ w t ∷ []) (fsTΣ ps y ys η))

H1W : ∀ x xs ps y ys → cof (y ∷ ys) ≡ cΩ [] → ∀ θ → fsT (πw (x ∷ xs) ps (y ∷ ys)) θ ≡ πw (x ∷ xs) ps (fsT (y ∷ ys) θ)
H1W x xs ps y ys c θ =
  trans (onCons (λ a → cof a ≡ cΩ [] → fsT (ψᵗ (x ∷ xs) a ∷ []) θ ≡ ψᵗ (x ∷ xs) (fsT a θ) ∷ [])
                (λ v vs c′ → H1-fsT x xs v vs c′ θ) ps y ys (trans (cofΣ ps y ys) c))
        (cong (λ t → ψᵗ (x ∷ xs) t ∷ []) (fsTΣ ps y ys θ))
```

## §4 一般栈上的带前缀 $\psi_w$, 目标 $w\ne0$

```agda
ne-w : ∀ {i w} → (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → w ≡ [] → ⊥
ne-w Iw ei ki refl = tf (trans (sym (kdI[] Iw)) (trans (sym (kd-≅ ei)) ki))
```

## §5 一般栈上的带前缀 $\psi_0$: 证书与标签一起

```agda
1<ψ : ∀ b → (b ≡ [] → ⊥) → natT 1 <ᵀ ψᵗ [] b ∷ []
1<ψ []       ne = ⊥-elim (ne refl)
1<ψ (v ∷ vs) ne = lt→< (natT 1) (ψᵗ [] (v ∷ vs) ∷ []) refl

++-ne : ∀ ps {b : T} → (b ≡ [] → ⊥) → ps ++ b ≡ [] → ⊥
++-ne []       ne e = ne e
++-ne (x ∷ ps) ne ()

fsT0-ne : ∀ w ws c θ → (θ ≡ [] → ⊥) → E.fsT0 (w ∷ ws) c θ ≡ [] → ⊥
fsT0-ne w ws c0     θ ne ()
fsT0-ne w ws c1     θ ne e = ne e
fsT0-ne w ws cω     θ ne ()
fsT0-ne w ws (cΩ ν) θ ne ()

fsTc-ne : ∀ u b ν m θ → E.fsTc u b ν m θ ≡ [] → ⊥
fsTc-ne u b ν lt θ ()
fsTc-ne u b ν eq θ ()
fsTc-ne u b ν gt θ ()

fsT₊-ne : ∀ u b c θ → E.fsT₊ u b c θ ≡ [] → ⊥
fsT₊-ne u b c0     θ ()
fsT₊-ne u b c1     θ ()
fsT₊-ne u b cω     θ ()
fsT₊-ne u b (cΩ ν) θ e = fsTc-ne u b ν (cmpᵀ (sucT ν) u) θ e

fsT-ne : ∀ y ys θ → cof (y ∷ ys) ≡ cΩ [] → (θ ≡ [] → ⊥) → fsT (y ∷ ys) θ ≡ [] → ⊥
fsT-ne y (v ∷ vs) θ c ne ()
fsT-ne (ψᵗ u (v ∷ vs)) [] θ c ne e = fsT₊-ne u (v ∷ vs) (cof (v ∷ vs)) θ e
fsT-ne (ψᵗ (w ∷ ws) []) [] θ c ne e = fsT0-ne w ws (cof (w ∷ ws)) θ ne e
fsT-ne (ψᵗ [] []) [] θ () ne e

γW-ne : ∀ ps a ν m → γW ps a ν m ≡ [] → ⊥
γW-ne ps a ν zero    ()
γW-ne ps a ν (suc m) ()

1<γ : ∀ ps y ys → cof (y ∷ ys) ≡ cΩ [] → ∀ m → natT 1 <ᵀ γW ps (y ∷ ys) [] (suc m)
1<γ ps y ys c m = 1<ψ (ps ++ fsT (y ∷ ys) (γW ps (y ∷ ys) [] m)) (++-ne ps (fsT-ne y ys _ c (γW-ne ps (y ∷ ys) [] m)))
```

## §8 结论与边界
