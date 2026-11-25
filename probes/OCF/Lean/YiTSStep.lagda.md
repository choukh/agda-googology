# 后继层的回灌展开

不读记号；编译定理。`TreeStep` 是后继层 Ω 树折到第 0 层的精确树等式，`branch` 给它的部分和分支。
对任意第 0 层树、证据、比较表、底与孩子路径成立；不提供回灌链对记号 γ 链的保持。
来源：展开 `YiTBRow.ψ` 的结点、`inu` 嵌入、后继三行及 `YiRWFold.node⁺`，不改定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTSStep where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow

module Step (x : Tr zero) (o : Ok (h₁ (suc x))) (r : Rb (h₁ (suc x)))
            (B : Base (h₁ (suc x))) (w : zero ≤ h₁ x) (β : Tr⁺ zero) where
  childBase : Base (h₁ x)
  childBase i u = B i (inc tt u)
  feed : Tr (h₁ x) → Tr (h₁ x)
  feed z = proj₁ (next⁺ (ψ (h₁ x) (proj₂ o tt) (proj₂ r tt) childBase (h₁ x) self (childBase (h₁ x) self) z))
  chain : ℕ → Tr (h₁ x)
  chain = iter feed zero
  parts : ℕ → Tr⁺ zero
  parts k = next⁺ (ψ (h₁ x) (proj₂ o tt) (proj₂ r tt) childBase zero w β (chain k))
  TreeStep : Set
  TreeStep = proj₁ (ψ (h₁ (suc x)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc x))))) ≡ proj₁ (limc⁺ parts)

  tree-step : TreeStep
  tree-step = refl

  branch : (k : ℕ) → zero ⊢ cum (λ n → proj₁ (parts n)) k ◃ proj₁ (ψ (h₁ (suc x)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc x)))))
  branch k = subst (λ z → zero ⊢ cum (λ n → proj₁ (parts n)) k ◃ z) (sym tree-step) (◃l k)

  part-zero : proj₁ (parts 0) ≡ proj₁ (next⁺ β)
  part-zero = refl

  feed-zero : chain 1 ≡ proj₁ (next⁺ (childBase (h₁ x) self))
  feed-zero = refl

ωᶜ : Tr zero
ωᶜ = lim nat (λ n → ◃s)

fin : (n : ℕ) → Step.TreeStep (nat n) (proj₂ (Ok-tw 1) (suc (nat n))) (rb-no (h₁ (suc (nat n)))) (B₀ (h₁ (suc (nat n)))) (z≤ (h₁ (nat n))) (Ωt zero)
fin n = refl

om : Step.TreeStep ωᶜ (proj₂ (Ok-tw 1) (suc ωᶜ)) (rb-no (h₁ (suc ωᶜ))) (B₀ (h₁ (suc ωᶜ))) (z≤ (h₁ ωᶜ)) (Ωt zero)
om = refl
```
