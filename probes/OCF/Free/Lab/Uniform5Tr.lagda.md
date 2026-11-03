# Uniform5Tr (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform5Tr](../../Align/Uniform5Tr.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform5Tr where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Z; Ord₊ˢ; Ordˢ; Ωˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-fsn; NF₁-pred)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Lab0[])
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Stage2Label using (one⁰)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.OmegaExpBase using (OccΣ; cofΣ; predΣ)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base hiding (_⊕_) renaming (FW to FW₀)
open import OCF.Free.Lab.Uniform3Rel
open import OCF.Free.Lab.Uniform3SqABase
open import OCF.Free.Lab.Uniform3Hon
open import OCF.Free.Lab.Uniform3Depth2Class
open import OCF.Free.Lab.Uniform3Depth2W using (InpW; CH; FHν; fsTΩ)
open import OCF.Free.Lab.Uniform3Depth2Fold using (Zc₀; Zc₀-of)
open import OCF.Free.Lab.Uniform3Full using (FlrLab[]-up; LWʰ-up; FH-pred; pred-Pr)
open import OCF.Free.Lab.Uniform5Head
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2)
open import OCF.Free.Tree
open import OCF.Free.Lab.Uniform5Class
open import OCF.Free.Lab.Uniform5Close
open import OCF.Free.Lab.Uniform5Tail
```

```agda
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cmpᵀ; lt; eq; gt) renaming (ψ to ψᵗ; _<ᵀ_ to _<ᵗ_)
open RestrO
```

```agda
Ld-tr  : ∀ {a b m φ} (e : a ≅ᴵ b) {x : O a φ} {u} → Ld a m x u → Ld b m (trO e x) u
Ld-tr⁻ : ∀ {a b m φ} (e : a ≅ᴵ b) {x : O b φ} {u} → Ld b m x u → Ld a m (tr⁻O e x) u
Ld-res : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {m ξ} {z : O (repO (resO q e)) ξ} {θ} → Ld _ m z θ → Ld j m (backO (resO q e) z) θ
Ld-res⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {m ξ} {z : O (repO (res⁻O q e)) ξ} {θ} → Ld _ m z θ → Ld j m (backO (res⁻O q e) z) θ

Ld-tr e lz = lz
Ld-tr e (ls cc F l) = ls cc F (Ld-tr e l)
Ld-tr e (ll cc h) = ll cc (λ n → Ld-tr e (h n))
Ld-tr e (li cc I ej hP hI) = li cc I ej (λ η x l s v → Ld-tr e (hP η x l s v)) (λ η x i → Ld-tr e (hI η x i))
Ld-tr e (lĉ cc K h₀ hk) = lĉ cc K (Ld-tr e h₀) (λ k → Ld-tr e (hk k))
Ld-tr e (lŝ cc I b ob h₀ hg) = lŝ cc I b ob (Ld-tr e h₀) (λ θ Y hY lY nθ lt d → Ld-tr e (hg θ Y hY lY nθ lt d))
Ld-tr e (lclo F cc h₀ hg) = lclo F cc (Ld-tr e h₀) (λ θ Y hY lY nθ lt → Ld-tr e (hg θ Y hY lY nθ lt))
Ld-tr e (lwk l) = lwk (Ld-tr e l)
Ld-tr {b = b} e (lΩ {ps = ps} {y} {ys} {r = q} {h = h} cc I ek f) =
  lΩ {r = ltO (resO q e)} cc I (≅ᴵ-trans (≅ᴵ-sym (eqO (resO q e))) ek)
     (λ {m′} v ξ z θ l → subst (λ w → Ld b m′ (trO e (h ξ (intoU (<→◃ q) (backO (resO q e) w)))) (ps ++ fsT (y ∷ ys) θ))
                               (sym (out-intoU (<→◃ (ltO (resO q e))) z))
                               (Ld-tr e (f v ξ _ θ (intoL (<→◃ q) (Ld-res q e (outL (<→◃ (ltO (resO q e))) l))))))

Ld-tr⁻ e lz = lz
Ld-tr⁻ e (ls cc F l) = ls cc F (Ld-tr⁻ e l)
Ld-tr⁻ e (ll cc h) = ll cc (λ n → Ld-tr⁻ e (h n))
Ld-tr⁻ e (li cc I ej hP hI) = li cc I ej (λ η x l s v → Ld-tr⁻ e (hP η x l s v)) (λ η x i → Ld-tr⁻ e (hI η x i))
Ld-tr⁻ e (lĉ cc K h₀ hk) = lĉ cc K (Ld-tr⁻ e h₀) (λ k → Ld-tr⁻ e (hk k))
Ld-tr⁻ e (lŝ cc I b ob h₀ hg) = lŝ cc I b ob (Ld-tr⁻ e h₀) (λ θ Y hY lY nθ lt d → Ld-tr⁻ e (hg θ Y hY lY nθ lt d))
Ld-tr⁻ e (lclo F cc h₀ hg) = lclo F cc (Ld-tr⁻ e h₀) (λ θ Y hY lY nθ lt → Ld-tr⁻ e (hg θ Y hY lY nθ lt))
Ld-tr⁻ e (lwk l) = lwk (Ld-tr⁻ e l)
Ld-tr⁻ {a = a} e (lΩ {ps = ps} {y} {ys} {r = q} {h = h} cc I ek f) =
  lΩ {r = ltO (res⁻O q e)} cc I (≅ᴵ-trans (≅ᴵ-sym (eqO (res⁻O q e))) ek)
     (λ {m′} v ξ z θ l → subst (λ w → Ld a m′ (tr⁻O e (h ξ (intoU (<→◃ q) (backO (res⁻O q e) w)))) (ps ++ fsT (y ∷ ys) θ))
                               (sym (out-intoU (<→◃ (ltO (res⁻O q e))) z))
                               (Ld-tr⁻ e (f v ξ _ θ (intoL (<→◃ q) (Ld-res⁻ q e (outL (<→◃ (ltO (res⁻O q e))) l))))))

Ld-res zero      (s≅ e) l = Ld-tr⁻ e l
Ld-res (suc q)   (s≅ e) l = Ld-res q e l
Ld-res (lim n q) (l≅ h) l = Ld-res q (h n) l

Ld-res⁻ zero      (s≅ e) l = Ld-tr e l
Ld-res⁻ (suc q)   (s≅ e) l = Ld-res⁻ q e l
Ld-res⁻ (lim n q) (l≅ h) l = Ld-res⁻ q (h n) l
```
