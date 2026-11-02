# 统一形 (四): 层号 $\Omega+m$ 的记号规则

> 接 [OmegaExpBase](OmegaExpBase.lagda.md). 记号侧. `μ m` $=\Omega+m$, `μ (suc m)` 与 `sucT (μ m)` 定义相等. `HeadRules h`: 头为 $h$ 时 $\psi_h(ps+\cdots)$ 的共尾度与基本列, 四种情形 (后继、$\omega$、穿透 `Pen`、折叠 `gt`), 对 $h$ 一致. 可数 `Idx` 下标对一切 $\mu_t$ 都穿透 (`ltμ`), $\mu_{m+1}$ 对一切可数目标都折叠 (`gtμ`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4Head where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.List.Properties using (++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

import OCF.Align.EBO as E
open E using (T; PT; natT; fsn; fsT; cof; pred; c0; c1; cω; cΩ; Ωt; 𝟏; sucT; cofA; cmpᵀ; lt; eq; gt; Cmp) renaming (ψ to ψᵗ)
open import OCF.Align.SystemOmega using (cmp-CΩ; cmp-ΩC; Ctbl-suc)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Decouple using (Idx; lvI)
open import OCF.Align.OmegaSqBase using (cmpΩ)
open import OCF.Align.OmegaExpBase using (πw; cofW; repW; ωW; γW; gtW; penW; fsnΣ; fsTΣ; predΣ; cofΣ)
open import OCF.Align.Closure using (Pen)
open import OCF.Align.Decouple using (cofP)
open import OCF.Align.GoodLBase using (Idx-Ctbl)
```

## §1 下标 $\mu_m$

```agda
Ωp : PT
Ωp = ψᵗ (𝟏 ∷ []) []

tailμ : ℕ → T
tailμ zero    = []
tailμ (suc m) = tailμ m ++ (𝟏 ∷ [])

μ : ℕ → T
μ m = Ωp ∷ tailμ m

_ : μ 0 ≡ Ωᵗ
_ = refl
_ : ∀ m → μ (suc m) ≡ sucT (μ m)
_ = λ m → refl

tailμ≡ : ∀ m → tailμ m ≡ natT m
tailμ≡ zero = refl
tailμ≡ (suc m) = trans (cong (_++ (𝟏 ∷ [])) (tailμ≡ m)) (snoc m)
  where
  snoc : ∀ n → natT n ++ (𝟏 ∷ []) ≡ natT (suc n)
  snoc zero = refl
  snoc (suc n) = cong (𝟏 ∷_) (snoc n)

gtμ : ∀ {w} m → Idx w → cmpᵀ (μ (suc m)) w ≡ gt
gtμ m Iw = cmp-ΩC (Idx-Ctbl Iw) (tailμ (suc m))

ltμ : ∀ {ν} t → Idx ν → cmpᵀ (sucT ν) (μ t) ≡ lt
ltμ t I = cmp-CΩ (Ctbl-suc (Idx-Ctbl I)) (tailμ t)
```

## §2 头 $h$ 上的规则

```agda
module HeadRules (h : T) {ps : T} {y : PT} {ys : T} where
  c1h : cof (y ∷ ys) ≡ c1 → cof (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) ≡ cω
  c1h c = trans (cofW h ps y ys) (cong (cofA h) c)

  cωh : cof (y ∷ ys) ≡ cω → cof (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) ≡ cω
  cωh c = trans (cofW h ps y ys) (cong (cofA h) c)

  cΩh : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → Pen (cmpᵀ (sucT ν) h) → cof (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) ≡ cΩ ν
  cΩh {ν} c p = trans (cofW h ps y ys) (trans (cong (cofA h) c) (cofP {w = h} {ν = ν} p))

  penh : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → Pen (cmpᵀ (sucT ν) h) → ∀ η → fsT (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) η ≡ ψᵗ h (ps ++ fsT (y ∷ ys) η) ∷ []
  penh {ν} c p η = penW h ps y ys ν c p η

  cgth : ∀ {ν} → cof (y ∷ ys) ≡ cΩ ν → cmpᵀ (sucT ν) h ≡ gt → cof (ψᵗ h (ps ++ (y ∷ ys)) ∷ []) ≡ cω
  cgth {ν} c e = trans (cofW h ps y ys) (trans (cong (cofA h) c) (cong (E.cofψ₊ h ν) e))
```
