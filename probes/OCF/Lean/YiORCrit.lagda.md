# 原行审查：封闭判据与比较表实例
验收文件（读记号）；编译定理：比较表行对一切有限 n 满足封闭判据，给出前提实例。
来源：`table-crit` 直接复用 `YiTBCrit.fiñᴰ` 的对角情形；不改树、折叠或合法性。
入口：`CritAtˆ`、`table-crit`；原行的判决见 `YiORBound`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiORCrit where
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (proj₁)
open import OCF.Lean.YiRWBlock using (Tr; zero)
open import OCF.Lean.YiRWOps using (Tr⁺)
open import OCF.Lean.YiRBCrit using (two)
open import OCF.Lean.YiCLFam using (M; nat)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiMHRel using (M̂)
import OCF.Lean.YiTBCrit as T

CritAtˆ : (Tr zero → Tr⁺ two) → ℕ → Set
CritAtˆ g n = M̂ (M 2) (ψᴺ 2 (Ωᴺ n)) (proj₁ (g (nat n)))

table-crit : ∀ n → CritAtˆ T.gᴰ n
table-crit n = T.fiñᴰ n n ≤-refl

pre-instance : CritAtˆ T.gᴰ 2
pre-instance = table-crit 2
```
