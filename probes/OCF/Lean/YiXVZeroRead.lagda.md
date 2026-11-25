# YiXVZeroRead
> 验收文件。编译定理：目标 0 的 ψ 与 ψ⁰ 对任意原始层及输入结构互模拟；有限 Le 经 ψ⁰ 保持。
> 按 Level.ψ 的目标 0 子句与 YiXVRef2.ψ₀≈ 推广；不需输入自模拟或 Funext。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVZeroRead where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≅→≼; ≼-trans)
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteFold as Fold

same : ∀ {k a} (p : L.zero L.<ᴵ a) (σ : L.Simᴵ k a) (X : L.Ordᶜ k) → L.ψ p σ X L.≅ L.ψ⁰ X
same p σ L.zero = L.s≅ L.z≅
same p σ (L.suc X) = L.l≅ (L.iter-R L._≅_ (λ e → L.add-≅ (same p σ X) e) L.z≅)
same p σ (L.lim f) = L.l≅ (λ n → same p σ (f n))
same p σ (L.limᵢ {i} q f) with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via e ())
... | injᵇ w = L.l≅ (λ n → same p σ (f (L.into (L.<→◃ q) (iter (λ X → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) X))) (L.Ω i) n))))
... | injᶜ e = L.l≅ (λ n → same p σ (f (L.into (L.<→◃ q) (iter (λ X → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) X))) (L.Ω i) n))))
same p σ (L.up L.zero X) = same p (λ q → σ (L.suc q)) X
same p σ (L.up (L.self n) X) = same p (λ q → σ (L.lim n q)) X
approx : ∀ {k a} (p : L.zero L.<ᴵ a) (σ : L.Simᴵ k a) (X : L.Ordᶜ k) →
  (L.ψ p σ X ≼ L.ψ⁰ X) × (L.ψ⁰ X ≼ L.ψ p σ X)
approx p σ X = ≅→≼ (same p σ X) , ≅→≼ (L.≅-sym (same p σ X))
zero-bound : ∀ k → L.zero L.<ᴵ L.natᴵ (suc k)
zero-bound zero = L.zero
zero-bound (suc k) = L.suc (zero-bound k)
mono : ∀ k {X Y} → A.Le k X Y → L.ψ⁰ X ≼ L.ψ⁰ Y
mono k {X} {Y} t = ≼-trans (≅→≼ (L.≅-sym (same (zero-bound k) (λ q → L.suc q) X)))
  (≼-trans (Q.Ops.mono (Fold.ops k) 0 (zero-bound k) (zero-bound k) (λ q → L.suc q) (λ q → L.suc q) X Y t)
    (≅→≼ (same (zero-bound k) (λ q → L.suc q) Y)))
```
