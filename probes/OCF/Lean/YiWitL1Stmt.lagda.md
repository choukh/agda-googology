# 第 1 层的 BTBO 下界: 陈述与归约 (搬到收缩见证的折叠)

验收文件. [YiL1Stmt](YiL1Stmt.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitL1Stmt where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open NA using (_⊴_; ⊴-+ˡ)
open import OCF.Lean.YiWitVOne using (V2; Ψ₀; up≼)
open import OCF.Lean.YiWitShpOne using (σA)
open import OCF.Lean.YiWitShpSq using (s₂; G₂; ψ₁; Bq)
open import OCF.Lean.YiWitShpEps using (fold1; K₁; G₂mono)
open import OCF.Lean.YiWitShpTwo using (σB; ψ₁ᴸ-lim)
open import OCF.Align.YiLvVal2 using (ℓ₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼l)
import OCF.Align.Stage2 as S2
```

## 1 参照与树

```agda
F₁ : ℕ → L.Ordᶜ ℓ₁
F₁ n = proj₁ ψ₁ᴸ-lim n

F₁-form : ∀ n → F₁ n ≡ L.ψ (σB L.zero) (λ q → L.lim n q) (L.Ω (S2.ℓ₀ L.[ n ]ᴵ))
F₁-form n = refl

F₁-self : ∀ n → F₁ n L.≅ F₁ n
F₁-self n = L.ψ-≅ {p = σB L.zero} {σ = λ q → L.lim n q} {p′ = σB L.zero} {σ′ = λ q → L.lim n q}
  (L.≅ᴵ-refl _) (L.Ω-refl (S2.ℓ₀ L.[ n ]ᴵ))

δq : ℕ → R
δq = chain zero (λ ζ → Ψ₀ (G₂ (plus (suc zero) G.top (K₁ ζ))))

node-form : NA.read (Ψ₀ (G₂ (plus (suc zero) G.top (ψ₁ G.top))))
  ≡ L.lim (λ m → NA.read (Ψ₀ (G₂ (plus (suc zero) G.top (K₁ (δq m))))))
node-form = refl
```

## 2 陈述与归约

```agda
Base₁ : Set
Base₁ = ∀ n ζ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (F₁ n)) ≼ NA.read (Ψ₀ (Bq ζ))

Chain₁ : Set
Chain₁ = ∀ n → Σ ℕ (λ m → F₁ n ⊴ K₁ (δq m))

point→base : ∀ n → Σ ℕ (λ m → F₁ n ⊴ K₁ (δq m)) → ∀ ζ →
  L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (F₁ n)) ≼ NA.read (Ψ₀ (Bq ζ))
point→base n (m , h) ζ = ≼-trans (≼l m (fold1 (⊴-+ˡ G.top h) (F₁-self n)))
  (up≼ (G₂mono (add-cp (suc zero) G.lc dnLc G.top
    (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (plus-weak (tw 2) G.top _)))))

chain→base : Chain₁ → Base₁
chain→base h n = point→base n (h n)
```
