# 在原 ψ₀ 的前缀右端加一份 Ω₁

第四层，Agda 无条件。给定原前缀的正可数读值 d，以及加一份 Ω₁ 后的遗传基本列证书，新值恰为严格大于 d 的首个 ε 数。基本列的第一个输入为 1，每步把输入 x 变为 d·ωˣ。[可数尾乘法](Reports-2026-11-19/attachments/B26PSuffix.agda.txt)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4OriginalEpsilonStep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Align.EboLeanDef using (T; ψ; Ωt; natT; HC; h0; h1; γT; cof; cω; fsn)
open import OCF.Lean.YiMENote using (cofψΩ; fsnψΩ)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; s≼s; +-mono)
open import WVOne using (T₀; 𝟏)
import B18Product as P
import B19IdealArithmetic as A
import B19IdealPowers as Pow
import B19IdealProduct as Eq
import B22MovingIndex as E
import B26PSuffix as Low
import B27SOriginal as Product
import B30UCut as Cut

unit = Ωt (natT 1)

module Step (p : T) (a : HC (Low.φ p)) (pos : 𝟏 ≼ Rt a)
            (end : HC (Low.φ (p ++ unit))) where
  d = Rt a
  arg = p ++ unit
  γ = γT arg []
  count = cof++Ω p unit refl
  limit-cof : cof (Low.φ arg) ≡ cω
  limit-cof = cofψΩ [] arg count
  expand : ∀ n → γ (suc n) ≡ Low.φ (p ++ γ n)
  expand n = cong Low.φ (fsT++ p unit (γ n) refl)
  branch : ∀ n → fsn (Low.φ arg) n ≡ γ (suc n)
  branch n = fsnψΩ [] arg n count
  proof : ∀ n → HC (γ n)
  proof zero = h1 refl (h0 refl)
  proof (suc n) = subst HC (branch n) (hω-inv end limit-cof n)
  x : ℕ → T₀
  x n = Rt (proof n)
  row : ∀ n → x (suc n) ≈ᵛ (d P.· A.norm (x n))
  row n = let b = subst HC (expand n) (proof (suc n)) in
    Eq._∙_ (Low.same (expand n) (proof (suc n)) b) (Low.Low.val p a (γ n) (proof n) b)
  shape : Rt end ≈ᵛ L.lim (λ n → x (suc n))
  shape = Low.limit end limit-cof (λ n → x (suc n))
    (λ n → Low.same (branch n) (hω-inv end limit-cof n) (proof (suc n)))

  start : L.suc d ≼ x 1
  start = ≼-trans {b = d P.· L.natᶜ 2} (+-mono (P.one-right d) pos)
    (≼-trans {b = d P.· A.norm 𝟏}
      (P.mono (≼-refl d) (≼l 2 (P.one-left (L.natᶜ 2)))) (proj₂ (row 0)))
  lower : ∀ n → E.steps d n ≼ x (suc n)
  lower zero = start
  lower (suc n) = ≼-trans {b = A.norm (x (suc n))} (Pow.expo Pow.omega-pos (lower n))
    (≼-trans {b = d P.· A.norm (x (suc n))} (P.pad pos _) (proj₂ (row (suc n))))

  module K = Cut.At d
  upper : ∀ n → K.Small (x n)
  upper zero = K.down {𝟏} {d} pos (E.strict d)
  upper (suc n) with K.common {d} {x n} (E.strict d) (upper n)
  ... | q , left , right , small = K.down {x (suc n)} {d P.· A.norm (x n)} (proj₁ (row n))
    (≼-trans {b = E.above q} (Product.local-bound q d (x n) left right)
      (E.least q (E.above d) small (proj₁ (E.fix d))))

  exact : Rt end ≈ᵛ E.above d
  exact = ≼-trans (proj₁ shape) (l≼ λ n → ≼-trans (≼-suc (≼-refl _)) (upper (suc n))) ,
    ≼-trans (l≼ λ n → ≼l n (lower n)) (proj₂ shape)
```
