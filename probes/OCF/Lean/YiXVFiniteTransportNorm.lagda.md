# YiXVFiniteTransportNorm
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteTransportNorm where
open import Data.Nat using (ℕ; zero; suc)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteTransportShape as S

module At (n : ℕ) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  uS : ∀ d {X : I.T n} → A.Gd n (S.τ d n X) → D.Step (S.τ d (suc n) (L.suc (L.up L.zero X))) (S.τ d (suc n) (L.up L.zero (L.suc X)))
  uS S.fwd gd = D.uS gd
  uS S.bwd gd = D.uS gd
  uS⁻ : ∀ d {X : I.T n} → A.Gd n (S.τ d n X) → D.Step (S.τ d (suc n) (L.up L.zero (L.suc X))) (S.τ d (suc n) (L.suc (L.up L.zero X)))
  uS⁻ S.fwd gd = D.uS⁻ gd
  uS⁻ S.bwd gd = D.uS⁻ gd
  uZ : ∀ d → D.Step (S.τ d (suc n) (L.up L.zero (L.zero {ℓ = L.natᴵ n}))) (S.τ d (suc n) L.zero)
  uZ S.fwd = D.uZ
  uZ S.bwd = D.uZ
  uZ⁻ : ∀ d → D.Step (S.τ d (suc n) L.zero) (S.τ d (suc n) (L.up L.zero (L.zero {ℓ = L.natᴵ n})))
  uZ⁻ S.fwd = D.uZ⁻
  uZ⁻ S.bwd = D.uZ⁻
  uL : ∀ d {a : ℕ → I.T n} → (∀ k → A.Gd n (S.τ d n (a k))) →
    D.Step (S.τ d (suc n) (L.up L.zero (L.lim a))) (S.τ d (suc n) (L.lim (λ k → L.up L.zero (a k))))
  uL S.fwd gd = D.uL gd
  uL S.bwd gd = D.uL gd
  uL⁻ : ∀ d {a : ℕ → I.T n} → (∀ k → A.Gd n (S.τ d n (a k))) →
    D.Step (S.τ d (suc n) (L.lim (λ k → L.up L.zero (a k)))) (S.τ d (suc n) (L.up L.zero (L.lim a)))
  uL⁻ S.fwd gd = D.uL⁻ gd
  uL⁻ S.bwd gd = D.uL⁻ gd
  uN : ∀ d {i} {q : i L.<ᴵ L.natᴵ n} {a : L.U i (L.<→◃ q) → I.T n} → A.Gd n (S.τ d n (L.limᵢ q a)) →
    D.Step (S.τ d (suc n) (L.up L.zero (L.limᵢ q a))) (S.τ d (suc n) (L.limᵢ (L.suc q) (λ u → L.up L.zero (a u))))
  uN S.fwd {q = q} {a = a} gd rewrite S.node S.fwd n q a | S.node S.fwd (suc n) (L.suc q) (λ u → L.up L.zero (a u)) = D.uN gd
  uN S.bwd {q = q} {a = a} gd rewrite S.node S.bwd n q a | S.node S.bwd (suc n) (L.suc q) (λ u → L.up L.zero (a u)) = D.uN gd
  uN⁻ : ∀ d {i} {q : i L.<ᴵ L.natᴵ n} {a : L.U i (L.<→◃ q) → I.T n} → A.Gd n (S.τ d n (L.limᵢ q a)) →
    D.Step (S.τ d (suc n) (L.limᵢ (L.suc q) (λ u → L.up L.zero (a u)))) (S.τ d (suc n) (L.up L.zero (L.limᵢ q a)))
  uN⁻ S.fwd {q = q} {a = a} gd rewrite S.node S.fwd n q a | S.node S.fwd (suc n) (L.suc q) (λ u → L.up L.zero (a u)) = D.uN⁻ gd
  uN⁻ S.bwd {q = q} {a = a} gd rewrite S.node S.bwd n q a | S.node S.bwd (suc n) (L.suc q) (λ u → L.up L.zero (a u)) = D.uN⁻ gd
```
