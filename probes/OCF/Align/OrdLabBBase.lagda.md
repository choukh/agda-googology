> **机械改写, 验收用.** 由 [OrdLabBase](OrdLabBase.lagda.md) 经 `Survey/scripts/ordlab/mk_b.py` 生成: 只把 `HtS`, `PxS`, `LadderInf*` 换成 `HtB`, `PxB`, `LadderOrd*`. 见 [OrdLab](OrdLab.lagda.md).

# OrdLabBBase

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabBBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.EBO as E
open E using (T; natT; fsn; fsT; cof; pred; cω; cΩ; sucT; cmpᵀ; lt; gt) renaming (ψ to ψᵗ)
open import OCF.Align.LadderOrdBase
open import OCF.Align.LadderLabZStandardOmega using (Ω₁)
open import OCF.Align.LadderLabZSystemOmega using (Occ; TailOf)
open import OCF.Align.OrdLabZDecouple using (Idx)

module _ (𝕊 : HtB) where
  open HtB 𝕊

  -- 第 0 行的三种写法各自要的记号事实
  data Row₀ (P : Ht → T → T) : (m : Ht) → View _<ᴸ_ h₀ m → Set where
    rb : P h₀ [] ≡ Ω₁ ∷ [] → Row₀ P h₀ base
    rc : ∀ {m n} (q : n <ᴸ m) → cof (P m []) ≡ cΩ [] → (∀ θ → fsT (P m []) θ ≡ P n θ) → Row₀ P m (clos q)
    rl : ∀ {m} (F : ℕ → Ht) (qs : ∀ i → F i <ᴸ m) → cof (P m []) ≡ cω → fsn (P m []) 0 ≡ [] → (∀ i → fsn (P m []) (suc i) ≡ P (F i) []) → Row₀ P m (chain F qs)

  record PxB : Set where
    field
      P       : Ht → T → T
      P-cof   : ∀ m w ws → cof (P m (w ∷ ws)) ≡ cof (w ∷ ws)
      P-pred  : ∀ m w ws → pred (P m (w ∷ ws)) ≡ P m (pred (w ∷ ws))
      P-fsn   : ∀ m w ws k → fsn (P m (w ∷ ws)) k ≡ P m (fsn (w ∷ ws) k)
      P-tail  : ∀ m τ → TailOf τ (P m τ)
      P-occ   : ∀ m τ → Occ (natT 1) (P m τ)
      -- 可数对前缀恒 lt, 反之恒 gt
      P-lt    : ∀ m τ {ν} → Idx ν → cmpᵀ (sucT ν) (P m τ) ≡ lt
      P-gt    : ∀ m ν {w} → Idx w → cmpᵀ (sucT (P m ν)) w ≡ gt
      -- 同高度比较尾巴, 不同高度由高度定
      P-cmp≡  : ∀ m ν τ → cmpᵀ (sucT (P m ν)) (P m τ) ≡ cmpᵀ (sucT ν) τ
      P-cmp-lt : ∀ {n H ν} τ → n <ᴸ H → Idx ν → cmpᵀ (sucT (P n ν)) (P H τ) ≡ lt
      P-cmp-gt : ∀ {n H} ν {τ} → H <ᴸ n → Idx τ → cmpᵀ (sucT (P n ν)) (P H τ) ≡ gt
      -- 第 0 行
      P-row   : ∀ m → Row₀ P m (view m)
```
