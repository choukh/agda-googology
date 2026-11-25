# 龙骨表的先验观察检查
验收文件，不读记号；表的有无不分离零与其余孩子，非零对角可为空。
来源：YiMTObs/YiTBObs 的表侧观察测试；全表否定直接引用 no-total。
这些定理只谈表数据；不把它们当作折叠头部的 Hand 或 branch→wdec 的否定。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWCheck where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Maybe using (nothing)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCWTable
open import OCF.Lean.YiTBObs using (isJ; no-total)
common : ∀ n c → hᵗ n c ≤ tw (suc n)
common n c = inc c self
empty-diagonal : ∀ n (c c′ : Tr (tw n)) → tbᵗ n (suc c) (suc c′) ≡ nothing
empty-diagonal n c c′ = refl
on-zero : ∀ n → isJ (tbᵗ n zero zero) ≡ true
on-zero n = refl
off-fails : ∀ n → ((c : Tr (tw n)) → (zero ≡ c → ⊥) → isJ (tbᵗ n c zero) ≡ false) → ⊥
off-fails n off with off (suc zero) (λ ())
... | ()
not-reflexive : ∀ n → ((c : Tr (tw n)) → isJ (tbᵗ n c c) ≡ true) → ⊥
not-reflexive n on with on (suc zero)
... | ()
no-full : ((c c′ : Tr zero) → (hᵗ 0 c′ ≤ hᵗ 0 c) ⊎ (hᵗ 0 c ≤ hᵗ 0 c′)) → ⊥
no-full = no-total
```
