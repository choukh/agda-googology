# 保留更新上下文的后继层出口
不读记号；编译条件定理：在同一拉回底与起点下，Anchor 推出后继层 Ω 折叠值界。
来源：YiTNRow.At.predecessor-low；标准底替换为显式实际底，Anchor 不省略。
没有跨底或一般跨层单调结论；实际实例见 YiOGActual。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGPeel where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTMInner as I
module At (a : B.L) (o : P.Ok (B.nd B.sS (λ _ → a)))
  (bs : F.Base (B.nd B.sS (λ _ → a)))
  (β : O.Tr⁺ B.zero) (w : P._≤_ B.zero a) where
  ℓ = B.nd B.sS (λ _ → a)
  oa = proj₂ o tt
  child-base : F.Base a
  child-base i u = bs i (P.inc tt u)
  b = bs a (P.inc tt P.self)
  fold = TB.ψ a oa (MT.rbᶻ a) child-base B.zero w β
  low = fold (proj₁ (O.Ωt a))
  high₀ = fold (B.suc B.zero)
  high₁ = fold (B.suc (proj₁ (O.next⁺ b)))
  high = TB.ψ ℓ o (MT.rbᶻ ℓ) bs B.zero (P.inu (λ _ → w)) β (proj₁ (O.Ωt ℓ))
  Anchor : Set
  Anchor = B._⊢_◃_ a (proj₁ (O.Ωt a)) (B.suc (proj₁ (O.next⁺ b)))
  peel : Anchor → V.val B.zero (proj₁ low) V.≼ V.val B.zero (proj₁ high)
  peel d = V.≼l 1 (V.≼-trans
    (V.◁→≼ (V.val-mono B.zero (TB.mono a oa (MT.rbᶻ a) child-base B.zero w β d)))
    (V.≼-trans (I.right-⊹ (V.val B.zero (proj₁ high₀)) (V.val B.zero (proj₁ high₁)))
      (proj₂ (V.val-+ (proj₁ high₀) (proj₁ high₁)))))
```
