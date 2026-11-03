# Correspond (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Correspond](../../Align/Correspond.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Correspond where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst) 
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Uniform using (Good; Good-add; Good-ψ; Good-ψ⁰; Good-Ω; Good→HS; gz; s-inv; l-inv; ≅-reflˡ)
import OCF.Free.Lab.NoCumsum as N
import OCF.Align.EBO as E
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofP; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; natT; fsn; fsT; fsT0; γT; trm; dec)
       renaming (ψ to ψᵗ)
```

## §1 片段 $\mathbb G$ 与链项 $H_\nu$

```agda
data H (ν : T) : T → Set where
  hΩ : H ν (ψᵗ ν [] ∷ [])
  hψ : ∀ {h} → H ν h → H ν (ψᵗ ν h ∷ [])

data 𝔾  : T → Set
data 𝔾ᴾ : PT → Set
data 𝔾 where
  g[] : 𝔾 []
  g∷  : ∀ {x xs} → 𝔾ᴾ x → 𝔾 xs → 𝔾 (x ∷ xs)
data 𝔾ᴾ where
  gψ : ∀ {a} → 𝔾 a → 𝔾ᴾ (ψᵗ [] a)
  gΩ : ∀ {u} → 𝔾 u → 𝔾ᴾ (ψᵗ [] (ψᵗ u [] ∷ []))
  gH : ∀ {ν h} → 𝔾 ν → H ν h → 𝔾ᴾ (ψᵗ [] h)
```

## §2 翻译、证书与层号

```agda
⟦_⟧ᴴ : ∀ {ν h} → H ν h → (L : Ordᴵ) → Ordᶜ L
⟦ hΩ ⟧ᴴ   L = Ω L
⟦ hψ d ⟧ᴴ L = ψ zero (λ r → r) (up zero (⟦ d ⟧ᴴ L))

reflH : ∀ {ν h} (d : H ν h) L → ⟦ d ⟧ᴴ L ≅ ⟦ d ⟧ᴴ L
reflH hΩ     L = Ω-refl L
reflH (hψ d) L = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl L) (reflH d L)

goodH : ∀ {ν h} (d : H ν h) L → Good (⟦ d ⟧ᴴ L)
goodH hΩ     L = Good-Ω L
goodH (hψ d) L = Good-ψ {p = zero} {σ = λ q → suc q} (goodH d L) (reflH d L)
```

```agda
⟦_⟧   : ∀ {t} → 𝔾 t → Ordᶜ zero
⟦_⟧ᴾ  : ∀ {x} → 𝔾ᴾ x → Ordᶜ zero
good  : ∀ {t} (g : 𝔾 t) → Good ⟦ g ⟧
goodᴾ : ∀ {x} (g : 𝔾ᴾ x) → Good ⟦ g ⟧ᴾ
lvl   : ∀ {t} → 𝔾 t → Ordᴵ

⟦ g[] ⟧      = zero
⟦ g∷ x xs ⟧  = ⟦ x ⟧ᴾ + ⟦ xs ⟧
⟦ gψ a ⟧ᴾ    = ψ⁰ ⟦ a ⟧
⟦ gΩ u ⟧ᴾ    = ψ⁰ (Ω (lvl u))
⟦ gH g d ⟧ᴾ  = ψ⁰ (⟦ d ⟧ᴴ (lvl g))
good g[]       = gz
good (g∷ x xs) = Good-add (goodᴾ x) (≅-refl⁰ _) (good xs)
goodᴾ (gψ a)   = Good-ψ⁰ (good a) (≅-refl⁰ _)
goodᴾ (gΩ u)   = Good-ψ⁰ (Good-Ω (lvl u)) (Ω-refl (lvl u))
goodᴾ (gH g d) = Good-ψ⁰ (goodH d (lvl g)) (reflH d (lvl g))
lvl g = toLevel ⟦ g ⟧ (Good→HS (good g))

cert : ∀ {t} (g : 𝔾 t) → HS ⟦ g ⟧
cert g = Good→HS (good g)
```

## §3 纯推导、匹配与形状的陈述

```agda
𝟘 : Ordᶜ zero
𝟘 = zero
```

## §4 记号侧: 规则的裸值形式

```agda
cmp-suc[] : ∀ ν → cmpᵀ (sucT ν) [] ≡ gt
cmp-suc[] []       = refl
cmp-suc[] (x ∷ xs) = refl
```

```agda
cof-ne   : ∀ x xs → cof (x ∷ xs) ≡ c0 → ⊥
cofA-ne  : ∀ u c → cofA u c ≡ c0 → ⊥
cofψ0-ne : ∀ w ws c → cof (w ∷ ws) ≡ c → cofψ0 (w ∷ ws) c ≡ c0 → ⊥
cofψ₊-ne : ∀ u μ m → cofψ₊ u μ m ≡ c0 → ⊥
cof-ne x (y ∷ ys) e               = cof-ne y ys e
cof-ne (ψᵗ u (y ∷ ys)) [] e       = cofA-ne u (cof (y ∷ ys)) e
cof-ne (ψᵗ (w ∷ ws) []) [] e      = cofψ0-ne w ws (cof (w ∷ ws)) refl e
cof-ne (ψᵗ [] []) [] ()
cofA-ne u c0 ()
cofA-ne u c1 ()
cofA-ne u cω ()
cofA-ne u (cΩ μ) e = cofψ₊-ne u μ (cmpᵀ (sucT μ) u) e
cofψ₊-ne u μ lt ()
cofψ₊-ne u μ eq ()
cofψ₊-ne u μ gt ()
cofψ0-ne w ws c0 ce _ = cof-ne w ws ce
cofψ0-ne w ws c1 ce ()
cofψ0-ne w ws cω ce ()
cofψ0-ne w ws (cΩ μ) ce ()
```

```agda
fs-rep : ∀ u y ys → cof (y ∷ ys) ≡ c1 → ∀ n → fsn (ψᵗ u (y ∷ ys) ∷ []) n ≡ replicate n (ψᵗ u (pred (y ∷ ys)))
fs-rep u y ys e n = trans (E.fsn₊-eq u y ys n e) (E.rep-trm u (E.pred-< (y ∷ ys) e) n)

fs-ω : ∀ u y ys → cof (y ∷ ys) ≡ cω → ∀ n → fsn (ψᵗ u (y ∷ ys) ∷ []) n ≡ ψᵗ u (fsn (y ∷ ys) n) ∷ []
fs-ω u y ys e n = E.fsn₊-eq u y ys n e

fsT-c1 : ∀ u c → c ≡ c1 → ∀ η → fsT0 u c η ≡ η
fsT-c1 u .c1 refl η = refl

fsn↓c-gt : ∀ u y ys ν be m → m ≡ gt → ∀ n → trm (E.fsn↓c u y ys ν be m n) ≡ trm (E.fsn↓c u y ys ν be gt n)
fsn↓c-gt u y ys ν be .gt refl n = refl
```

## §7 对角线

```agda
γᴱ : ℕ → T
γᴱ zero    = ψᵗ [] [] ∷ []
γᴱ (suc k) = ψᵗ [] (Ωt (γᴱ k)) ∷ []

gγ : ∀ k → 𝔾 (γᴱ k)
gγ zero    = g∷ (gψ g[]) g[]
gγ (suc k) = g∷ (gΩ (gγ k)) g[]

βᴱ : T
βᴱ = Ωt (Ωt (natT 1))

γT-γᴱ : ∀ k → γT βᴱ [] k ≡ γᴱ k
γT-γᴱ zero    = refl
γT-γᴱ (suc k) = cong (λ z → ψᵗ [] (Ωt z) ∷ []) (γT-γᴱ k)

diag-fs : ∀ n → fsn (E.EBOψ 2) n ≡ γᴱ (suc n)
diag-fs n = cong (λ z → ψᵗ [] z ∷ [])
  (trans (E.fsT↓-trm βᴱ refl (dec (E.γ↓ βᴱ [] refl n))) (cong (fsT βᴱ) (trans (E.γ↓-trm βᴱ [] refl n) (γT-γᴱ n))))

diag-≅ : ∀ k → N.γ k ≅ ⟦ gγ k ⟧
diag-≅ zero    = s≅ z≅
diag-≅ (suc k) = ψ⁰-≅ (Ω-≅ (toLevel-≅ (N.cert k) (cert (gγ k)) (diag-≅ k)))
```

## §8 遗传标签

```agda
data Lab : Ordᶜ zero → T → Set where
  l0 : ∀ {X t} → cof t ≡ c0 → X ≅ 𝟘 → Lab X t
  l1 : ∀ {X Y t} → cof t ≡ c1 → X ≅ suc Y → Lab Y (pred t) → Lab X t
  lω : ∀ {X t} {F : ℕ → Ordᶜ zero} → cof t ≡ cω → X ≅ lim F → (∀ n → Lab (F n) (fsn t n)) → Lab X t

Lab-≅ : ∀ {X X′ t} → X′ ≅ X → Lab X t → Lab X′ t
Lab-≅ d (l0 c e)     = l0 c (≅-trans d e)
Lab-≅ d (l1 c e l)   = l1 c (≅-trans d e) l
Lab-≅ d (lω c e h)   = lω c (≅-trans d e) h
```

```agda
diag-label : (∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))) → Lab N.BTBOᴵ (E.EBOψ 2)
diag-label h = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab (N.γ (suc n))) (sym (diag-fs n)) (h n))
```

## §12 结论与边界
