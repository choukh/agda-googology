# 任意前缀下最低Ω的完整旧参照下界

源的最低Ω是实际Source的base组件，不是替代常值节点。对任意β/B及
支持前缀，完整Old.TΩ1的坐标、输出和部分和同时送入新真实对角。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumeLowest where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans; mul-≤)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.HigherIndexFoldIf using (Source)
open import OCF.Lean.HigherIndexSupportSource using (Supported)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.HigherIndexConsumeRun using (run)
open import OCF.Lean.HigherIndexConsumePositive
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1 as Old

oldF : Wd (step S⊥) → Cd → Cd
oldF W d = F.Φ (hs hz) tt hz (hsuc hself) W (up d)
act-positive : ∀ d → hs hz ≤ᵛ old-act d
act-positive hz = s≤s z≤
act-positive (hs d) = ≤l 0 (act-positive d)
act-positive (hl f) = ≤l 0 (act-positive (f 0))
act-positive (hΩ () f)
old-compare : ∀ W {a b} → a ≤ᵛ b → oldF W a ≤ᵛ old-act b
old-compare W {b = b} z≤ = act-positive b
old-compare W (s≤s p) = l≤ (λ n → ≤l n (mul-≤ (old-compare W p) n))
old-compare W (≤s p) = ≤l 0 (old-compare W p)
old-compare W (l≤ p) = l≤ (λ n → old-compare W (p n))
old-compare W (≤l n p) = ≤l n (old-compare W p)

encode : Cd → HB Source
encode d = ι (inj₂ hz) (ι (inj₂ hz) (up (pure S⊥ d)))
encoded-pure : ∀ d → Pure d (encode d)
encoded-pure hz = pz
encoded-pure (hs d) = ps (encoded-pure d)
encoded-pure (hl f) = pl (λ n → encoded-pure (f n))
encoded-pure (hΩ () f)
lowest : HB Source
lowest = ι (inj₂ hz) (ι (inj₂ hz) (hΩ (inj₂ tt) up))

module Lower (β : Cd) (lb : LgB β) (B : _) (lB : LgB B)
  (A : HB Source) (p : Supported β B (A ⊞ lowest)) where
  branch : Cd → Cd
  branch d = run β lb B lB (A ⊞ encode (leg d)) (proj₂ p (pure S⊥ (leg d)) tt)
  action : ∀ d → old-act d ≤ᵛ branch d
  action d = ≤-trans (old-compare (tt , hz) (inflation d))
    (pure-suffix (encoded-pure (leg d)) β lb B lB A (proj₂ p (pure S⊥ (leg d)) tt))

  module Original = F.Col _⊞_ _⊞_ (tt , hz) hz (λ W e → proj₁ W , e) oldF oldF
  coordinates : ∀ n → Original.ce n ≤ᵛ chain branch n
  coordinates zero = z≤
  coordinates (suc n) = add-mono (coordinates n)
    (≤-trans (old-compare (Original.cw n) (coordinates n)) (action (chain branch n)))
  outputs : ∀ n → Original.oo n ≤ᵛ branch (chain branch n)
  outputs n = ≤-trans (old-compare (Original.cw n) (coordinates n)) (action (chain branch n))
  sums : ∀ n → Original.oO n ≤ᵛ Ops.partial S⊥ (λ j → branch (chain branch j)) n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))

  whole : Old.TΩ1 ≤ᵛ run β lb B lB (A ⊞ lowest) p
  whole = l≤ (λ n → ≤l n (sums n))
```

whole是全部旧输出覆盖，并保留任意真实前缀。还需把这一路最低组件
定位进本轮原完整高floor的实际输出；不将局部whole冒充闭项结论。
