# 阶段无关的规范层号域
不读记号；`Cn` 按零、后继、带相邻路径的 ℕ 极限与统一的 Ω 构造生成。
编译定理：`cn-tw` 覆盖全部塔层号，`cn-ok` 给出原合法性，Ω 形状的孩子沿第一位置序单调。
域不要求 Ω 构造的每个孩子也有 `Cn` 证据；孩子仍取原块的全体树。此域的 Leaf 在验收侧另行陈述。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCNDomain where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWPath as P

Ωc : L → L
Ωc k = nd (sΩ k) (λ c → k ⊕ ↑ k c)

data Cn : L → Set where
  cz : Cn zero
  cs : ∀ {h} → Cn (h tt) → Cn (nd sS h)
  cl : ∀ {h} → (∀ n → Cn (h n)) → (∀ n → h n P.≤ h (suc n)) → Cn (nd sL h)
  cw : ∀ {k} → Cn k → Cn (Ωc k)

cn-tw : ∀ n → Cn (tw n)
cn-tw zero = cz
cn-tw (suc n) = cw (cn-tw n)

cn-ok : ∀ {ℓ} → Cn ℓ → P.Ok ℓ
cn-ok cz = tt
cn-ok (cs q) = tt , λ _ → cn-ok q
cn-ok (cl q r) = r , λ n → cn-ok (q n)
cn-ok (cw {k} q) = (cn-ok q , λ c → P.lift k (↑ k c)) , λ c →
  P.Ok⊕ k (↑ k c) (cn-ok q) (P.OkO↑ k k (cn-ok q) P.self c)

cn-mono : ∀ {k h} → Cn (nd (sΩ k) h) → ∀ {x y} → k ⊢ x ◃ y → h x P.⊑ h y
cn-mono (cw {k} q) d = P.⊕⊑ k (P.◃→⊑ k d)
```
