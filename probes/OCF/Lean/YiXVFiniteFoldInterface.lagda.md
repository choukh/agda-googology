# YiXVFiniteFoldInterface
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFoldInterface where
open import Data.Nat using (ℕ; zero; suc)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteGroundFold as G

record Ops (n : ℕ) : Set₁ where
  field
    good : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ (L.natᴵ n) a) (X : I.T n) → A.Gd n X → A.Gd j (L.ψ p σ X)
    mono : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ n) a) (τ : L.Simᴵ (L.natᴵ n) b) (X Y : I.T n) →
      A.Le n X Y → A.Le j (L.ψ p σ X) (L.ψ p′ τ Y)
    node-plus : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ n) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b)
      {i} (q : i L.<ᴵ L.natᴵ n) (f : L.U i (L.<→◃ q) → I.T n) → A.Gd n (L.limᵢ q f) →
      A.Le j (L.ψ p σ (L.limᵢ q f)) (L.ψ p′ τ (L.limᵢ (L.suc q) (λ u → L.up L.zero (f u))))
    node-minus : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (p′ : L.natᴵ j L.<ᴵ b)
      (σ : L.Simᴵ (L.natᴵ n) a) (τ : L.Simᴵ (L.natᴵ (suc n)) b)
      {i} (q : i L.<ᴵ L.natᴵ n) (f : L.U i (L.<→◃ q) → I.T n) → A.Gd n (L.limᵢ q f) →
      A.Le j (L.ψ p′ τ (L.limᵢ (L.suc q) (λ u → L.up L.zero (f u)))) (L.ψ p σ (L.limᵢ q f))

ops₀ : Ops 0
Ops.good ops₀ j p σ X gx = G.good j p σ X
Ops.mono ops₀ j p p′ σ τ X Y t = G.mono j p p′ σ τ t
Ops.node-plus ops₀ j p p′ σ τ () f gx
Ops.node-minus ops₀ j p p′ σ τ () f gx
```
