# NotFree (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [NotFree](../../Align/NotFree.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.NotFree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Symbolic using (Ctx; Pt; lvP; Γᶜ; χᶜ-step)
open import OCF.Free.Lab.Prefix using (Z; ĉᴸ; Ord₊ˢ; Ordˢ; toZ; Goodᶻ; force; force-HS; outs; X₂ˢ)
open import OCF.Free.Lab.UniformS using (_≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ; toZ-≅)
import OCF.Free.Lab.GoodLBase as GL
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Free.Lab.Symbolic using (σ1; X₂ᵗ)
open import OCF.Free.Lab.Prefix using (Ωˢ)
open import OCF.Free.Lab.UniformS using (Ωˢ-refl; ψ1; ⊑ᴵ-≅ʳ)
import OCF.Free.Lab.NoCumsum as N
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; Lab-≅)
open import OCF.Free.Lab.Stage2 using (Lab-uniq; γ′ᴱ; t2; ctx; ≺→⊑)
open import OCF.Free.Lab.StandardOmega using (γ′-NF)
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Stage2Label using (GX₂; X₂ᶠ; pop0≅; Lab-oc)
open import OCF.Free.Lab.Decouple using (X₂-label)
open import OCF.Free.Lab.UniformS using (ψ1-cong; Ω-monoᵒ; idO)
open import OCF.Free.Lab.Symbolic using (Mlev) 
open import Data.List using ([]; _∷_)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; ot) 
open import OCF.Free.Lab.UniformS using (two) 
open import OCF.Free.Force public using (Goodᴺ; gz; gs; gl; gc; forceᴺ; forceᴺ-HS; forceᴺ-≅; outsᴺ; outsᴺ-HS; outsᴺ-step; outsᴺ-≅; ys-≅)
```

```agda
open GL using (Goodᴸ; forceᴸ; forceᴸ-HS; Ptᴸ; ptsᴸ; lvᴸ)
```

## §3 桥: 从 Prefix 的证书与从 `Goodᴸ`

```agda
ofL   : ∀ {x} → Goodᴸ x → Goodᴺ x
ofL-≅ : ∀ {x} (G : Goodᴸ x) → forceᴺ x (ofL G) ≅ forceᴸ x G

ofL GL.gz = gz
ofL (GL.gs G) = gs (ofL G)
ofL (GL.gl G st) = gl (λ n → ofL (G n))
  (λ n → ⊑-trans (≅→⊑ (ofL-≅ (G n))) (⊑-trans (st n) (≅→⊑ (≅-sym (ofL-≅ (G (suc n)))))))
ofL {ĉᴸ c t₀ g o₀ o} (GL.gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) =
  gc (λ m → Ptᴸ.x (P m)) (λ m → Ptᴸ.hx (P m)) (λ m → Ptᴸ.dx (P m))
     (ofL G₀) (ofL-≅ G₀) (λ m → ofL (Gm m)) (λ m → ofL-≅ (Gm m))
     (ofL Go₀) (λ k → ofL (Go k))
     (⊑-trans (≅→⊑ (ofL-≅ Go₀)) (⊑-trans mo₀ (≅→⊑ (≅-sym (ofL-≅ (Go 0))))))
     (λ k → ⊑-trans (≅→⊑ (ofL-≅ (Go k))) (⊑-trans (mo k) (≅→⊑ (≅-sym (ofL-≅ (Go (suc k)))))))
  where
  P : ∀ k → Ptᴸ c γ k
  P = ptsᴸ (forceᴸ t₀ G₀) (forceᴸ-HS t₀ G₀) l₀ d₀ (λ m Y hY lY e → forceᴸ _ (Gg m Y hY lY e))
           (λ m Y hY lY e → forceᴸ-HS _ (Gg m Y hY lY e)) lE dE
  Gm : ∀ m → Goodᴸ (g (lvᴸ (P m)) (Ptᴸ.dx (P m)))
  Gm m = Gg m (Ptᴸ.x (P m)) (Ptᴸ.hx (P m)) (Ptᴸ.lx (P m)) (Ptᴸ.dx (P m))

ofL-≅ GL.gz = z≅
ofL-≅ (GL.gs G) = s≅ (ofL-≅ G)
ofL-≅ (GL.gl G st) = l≅ (λ n → ofL-≅ (G n))
ofL-≅ (GL.gc γ G₀ l₀ d₀ Gg lE dE Go₀ Go mo₀ mo) = l≅ eo
  where
  eo : ∀ n → _
  eo zero    = ofL-≅ Go₀
  eo (suc k) = ofL-≅ (Go k)
```

## §4 检验 (b) 与第 0 个链点: 记号无关的证书

```agda
open E using (T; _<ᵀ_; []<; cmpᵀ; lt; natT; Ωt) renaming (ψ to ψᵗ)

```

## §9 结论与边界
