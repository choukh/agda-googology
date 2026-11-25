# YiXVReadFinitePathInput
> 验收文件。档位：编译定理。有限原结构路径的证据，含零、一层与自然极限的完整实例。
> 跟踪 YiLegPath 的原计算；不改树、折叠、UR、比较器。未交完整极限／节点世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadFinitePathInput where
open import Data.Nat using (ℕ)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadOmegaInput as Ω
data Finite : ∀ {a b} → a P.⊑ b → Set where
  self : ∀ {a : S.L} → Finite (P.self {ℓ = a})
  ins : ∀ {a b : S.L} {v : a P.⊑ b} → Finite v → Finite (P.ins v)
  inl : ∀ {a : S.L} {f : ℕ → S.L} n {v : a P.⊑ f n} → Finite v → Finite (P.inl {g = f} n v)
model₀ : Finite (P.self {ℓ = S.zero})
model₀ = self
model₁ : Finite (P.ins (P.self {ℓ = S.zero}))
model₁ = ins self
model-ω : Finite (P.inl {g = λ n → J.ℓ (Ω.nat n)} 0 P.self)
model-ω = inl {f = λ n → J.ℓ (Ω.nat n)} 0 self
```
