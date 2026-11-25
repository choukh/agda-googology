# 从首个正询问取出正层指数的全体有限迭代

第四层。两份 Ω₂ 的第 1 枝在其首次回灌中已容纳一整列正层指数。所取上界保持同一 Ω₂ 起始前缀和相同的两次折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadCapPositive where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l; ≅→≼)
open import OCF.Lean.YiRefTw2 using (Rt)
open import WVOne using (T₀; 𝟏)
open import WVTwo using (T₁)
open import WSLevel using (Ω₁ᴸ)
open import YiLAB7Replay using (Ω₂ᴸ)
import B12Omega3Ref as R
import B13Target as P
import B14RefFixed as F
import B15RefAlgebra as A
import B17RefAllSource as Src
import B24RRows as Q
import Survey.W4PTOFirstQuery as First
import Survey.W4OriginalIteratedBound as Name

fold = λ y → L.ψ⁰ (Q.T y)
cong : ∀ {u v} → u L.≅ v → fold u L.≅ fold v
cong d = L.ψ⁰-≅ (Q.respects d)

branch : Rt Name.next-h L.≅ Q.node 1
branch = L.≅-trans (proj₂ Name.next-at) (Src.part (Src.part First.query-address 2) 1)

first : Q.gain 1 𝟏 ≼ Rt Name.next-h
first = ≼-trans {b = Q.node 1}
  (≼-trans (≼l 0 (≼-refl (Q.gain 1 𝟏))) (≅→≼ (L.≅-sym (Q.shape 1))))
  (≅→≼ (L.≅-sym branch))

picked : fold (A.H 𝟏 Ω₁ᴸ) ≼ Q.gain 1 𝟏
picked = ≼-trans {b = fold (F.collapse (P.co₀ 𝟏))} (≅→≼ (cong (L.≅-sym (A.true-coeff 𝟏))))
  (≼-trans {b = fold (F.collapse (P.pass Ω₂ᴸ))}
    (≼l 0 (≼l 0 (≼-refl (fold (F.collapse (P.co₀ 𝟏))))))
    (≼l 1 (≼-refl (fold (F.collapse (P.pass Ω₂ᴸ))))))

stage = R.S.iter (A.E Ω₁ᴸ) Ω₁ᴸ
stages : ∀ n → fold (stage (suc n)) ≼ Q.gain 1 𝟏
stages n = ≼-trans {b = fold (A.Γ Ω₁ᴸ)} (≼l n (≼-refl _))
  (≼-trans {b = fold (A.H 𝟏 Ω₁ᴸ)} (≼l 1 (≼-refl (fold (A.Γ Ω₁ᴸ)))) picked)
```
