> **机械改写, 验收用.** 由 `OrdLabBBase` 经 `Survey/scripts/embvv/mk_world.py`: `Row₀` 多一种去头的链行 `rh`. 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVBBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.EBO as E
open E using (T; natT; fsn; fsT; cof; pred; cω; cΩ; sucT; cmpᵀ; lt; gt) renaming (ψ to ψᵗ)
open import OCF.Align.LadderOrdBase
import OCF.Align.EmbVVMode
open import OCF.Align.EmbVVLZStandardOmega using (Ω₁)
open import OCF.Align.LadderLabZSystemOmega using (Occ; TailOf)
open import OCF.Align.EmbVVOZDecouple using (Idx)

module _ (𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) where
  open OCF.Align.EmbVVMode 𝕊 using (HdM; keep; drop; repl)
  open HtB 𝕊

  -- 第 0 行的三种写法各自要的记号事实
  data Row₀ (P : Ht → T → T) : (m : Ht) → View _<ᴸ_ h₀ m → HdM m → Set where
    rb : ∀ {b} → P h₀ [] ≡ Ω₁ ∷ [] → Row₀ P h₀ base b
    rc : ∀ {m n b} (q : n <ᴸ m) → cof (P m []) ≡ cΩ [] → (∀ θ → fsT (P m []) θ ≡ P n θ) → Row₀ P m (clos q) b
    rl : ∀ {m} (F : ℕ → Ht) (qs : ∀ i → F i <ᴸ m) → cof (P m []) ≡ cω → fsn (P m []) 0 ≡ [] → (∀ i → fsn (P m []) (suc i) ≡ P (F i) []) → Row₀ P m (chain F qs) keep
    rh : ∀ {m} (F : ℕ → Ht) (qs : ∀ i → F i <ᴸ m) → cof (P m []) ≡ cω → (∀ i → fsn (P m []) i ≡ P (F i) []) → Row₀ P m (chain F qs) drop
    rr : ∀ {m n} (q : n <ᴸ m) (F : ℕ → Ht) (qs : ∀ i → F i <ᴸ m) → cof (P m []) ≡ cω → fsn (P m []) 0 ≡ P n [] → (∀ i → fsn (P m []) (suc i) ≡ P (F i) []) → Row₀ P m (chain F qs) (repl n q)

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
      P-row   : ∀ m → Row₀ P m (view m) (dr m)
```
