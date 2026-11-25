# 剥后继在树侧模拟关系中的出口
不读记号；编译定理：同一实际上下文的第一位置证据可逐次接在 Le 推导后。
来源：YiOGPeel 的第 1 累计支、YiKAMono.le◃；right-add 按 Le 推导递归。
不提供两套更新底之间的单调；具体比较在 YiOGBaseAll。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGRelPeel where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiVRRel
open import OCF.Lean.YiVRFold using (_⊴_)
open import OCF.Lean.YiKAMono using (le◃)
import OCF.Lean.YiOGFold as Fold
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT

right-add : ∀ {a x y} → Le a x y → (p : Tr a) → Le a x (p + y)
right-add z≼ p = z≼
right-add (s≼s d) p = s≼s (right-add d p)
right-add (≼s d) p = ≼s (right-add d p)
right-add (≼l n d) p = ≼l n (right-add d p)
right-add (l≼ h) p = l≼ (λ n → right-add (h n) p)
right-add (≼w d) p = ≼w (right-add d p)
right-add (w≼w h) p = w≼w (λ z z′ r → right-add (h z z′ r) p)
right-add (≼u d) p = ≼u (right-add d p)
right-add (u≼u dx dy) p = u≼u (right-add dx p) dy

module At (a : L) (ν : NoΩ a) (o : Ok (nd sS (λ _ → a)))
  (bs : Base (nd sS (λ _ → a))) (j : L) (w : j ≤ a) (β : Tr⁺ j) where
  ℓ = nd sS (λ _ → a)
  oa = proj₂ o tt
  child-base : Base a
  child-base i u = bs i (inc tt u)
  b = bs a (inc tt self)
  fold = Fold.ψ a oa child-base j w β
  low = fold (proj₁ (Ωt a))
  high₀ = fold (suc zero)
  high₁ = fold (suc (proj₁ (next⁺ b)))
  high = Fold.ψ ℓ o bs j (inu (λ _ → w)) β (proj₁ (Ωt ℓ))
  Anchor = a ⊢ proj₁ (Ωt a) ◃ suc (proj₁ (next⁺ b))
  peel : child-base ⊴ child-base → Can j (proj₁ β) → Anchor → Le j (proj₁ low) (proj₁ high)
  peel hb hβ d = ≼l 1 (right-add
    (Fold.fl a ν oa child-base child-base hb j w β β hβ (le◃ (Ωt≼ a ν) d)) (proj₁ high₀))

  peel-from : ∀ {x : Tr j} → Le j x (proj₁ low) → Anchor → Le j x (proj₁ high)
  peel-from e d = ≼l 1 (right-add (le◃ e (TB.mono a oa (MT.rbᶻ a) child-base j w β d)) (proj₁ high₀))
```
