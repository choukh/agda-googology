# YiXVReadOmegaInput
> 验收文件。档位：编译定理。Ω 极限构造的逐支接口，有限层列给原 ω 层的完整实例。
> 复用原 h₁/lvl 与 YiXVLvlLiteral，源模拟从 YiXVSourceFamily/Basics 推广；未交一般源世界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadOmegaInput where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
record Branches (f : ℕ → S.Tr S.zero) (C : ∀ n → L.Ordᶜ (T.lvl (f n))) : Set where
  field
    good : ∀ n → A.Gd (C n)
    cover : ∀ n → U.UR (f n) (O.Ωt (J.ℓ (f n))) (C n)
nat : ℕ → S.Tr S.zero
nat zero = S.zero
nat (suc n) = S.suc (nat n)
ω : S.Tr S.zero
ω = S.lim nat (λ n → S.◃s)
cap : ∀ n → L.Ordᶜ (T.lvl (nat n))
cap zero = L.Ω L.zero
cap (suc n) = L.Ω (T.lvl (nat (suc n))) L.+ L.Ω (T.lvl (nat (suc n)))
model : Branches nat cap
Branches.good model zero = proj₁ (Ω.model L.zero)
Branches.good model (suc n) = Add.good {σ = λ q → q}
  (proj₁ (Ω.model (T.lvl (nat (suc n))))) (proj₁ (Ω.model (T.lvl (nat (suc n)))))
Branches.cover model zero = ≼-refl _
Branches.cover model (suc n) = B.Ωsuc (nat n)
```
