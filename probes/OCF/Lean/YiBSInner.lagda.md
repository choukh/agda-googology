# 换基候选的变量整行
候选；g、feed、out 与迭代的组织搬自 YiE4Inner，折叠改成 YiBSFold。
整行用 YiRWCheck.kp-z，不重证零层槽位消去；函数在出生处封装，未增加值前提。
入口：YiBSClean；本件不涉及记号或值验收。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSInner where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; kp; node⁺)
open import OCF.Lean.YiRWCheck using (kp-z)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as F
module Inner (k : L) (a : Tr k → L) (o : Ok (nd (sΩ k) a))
  (r : Rb (nd (sΩ k) a)) (B : Base (nd (sΩ k) a)) (β : Tr⁺ zero) where
  ℓ : L
  ℓ = nd (sΩ k) a
  -- perf: S-1，实际函数与规格一起封装。
  opaque
    g : Tr k → Tr ℓ
    g d = proj₁ (upz {s = sΩ k} {h = a} d (Ωt (a d)))
    g-eq : ∀ d → g d ≡ proj₁ (upz {s = sΩ k} {h = a} d (Ωt (a d)))
    g-eq d = refl
    feed : Tr k → Tr k
    feed d = proj₁ (F.ψ ℓ o r B k (ink self) (B k (ink self)) (g d))
    feed-eq : ∀ d → feed d ≡ proj₁ (F.ψ ℓ o r B k (ink self) (B k (ink self)) (g d))
    feed-eq d = refl
    out : Tr k → Tr⁺ zero
    out d = F.ψ ℓ o r B zero (z≤ ℓ) β (g d)
    out-eq : ∀ d → out d ≡ F.ψ ℓ o r B zero (z≤ ℓ) β (g d)
    out-eq d = refl
  chain : ℕ → Tr k
  chain = iter feed zero
  two : chain 2 ≡ feed (feed zero)
  two = refl
  opaque
    unfolding g feed out
    row : F.ψ ℓ o r B zero (z≤ ℓ) β (proj₁ (Ωt ℓ)) ≡ limc⁺ (λ n → out (chain n))
    row = cong (λ m → node⁺ m (λ d → F.ψ ℓ o r B zero (z≤ ℓ) β (g d)) feed)
      (kp-z ℓ o (inj₁ (inj₁ tt)) (z≤ ℓ))
```
