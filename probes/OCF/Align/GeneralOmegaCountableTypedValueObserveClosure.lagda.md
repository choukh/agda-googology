# 固定ambient的加法与完整后继列闭包

验收专用。右加数允许自己的源层，η把它嵌入左加数源层；实际右树
仍留在同一HB(F B)。这使原up递归不丢观察界。所有分支强制使用
原into/out坐标，逐点以out-into消掉嵌入往返，不使用函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveClosure where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; leftMul)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedFloor using (self)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

add : ∀ {B lB ℓ j} {σ : L.Simᴵ ℓ (height B lB)} (η : L.Simᴵ j ℓ) {a b c d} →
  Read B lB σ a b → Read B lB (λ q → σ (η q)) c d →
  Read B lB σ (L.add a η c) (b ⊞ d)
add η p rz = p
add η p (rs q) = rs (add η p q)
add η p (rl q) = rl (λ n → add η p (q n))
add {B} {lB} {σ = σ} η {a} {b} p (ro κ q {f} {g} e sc r) =
  ro κ (η q) e (L.add-≅ {σ = η} {σ′ = η} (self p) sc) branches
  where
  branches : ∀ x c → Coord B lB κ x c →
    Read B lB σ (L.add a η (f (L.coe (L.<→◃ (η q)) (L.<→◃ q) (L.into (L.<→◃ (η q)) x))))
      (b ⊞ g c)
  branches x c z rewrite L.out-into (L.<→◃ (η q)) x = add η p (r x c z)
add η p (ru-s q) = add (λ r → η (L.suc r)) p q
add η p (ru-l {i = i} q) = add (λ r → η (L.lim i r)) p q
add η p (rc e q) = rc (L.add-≅ {σ = η} {σ′ = η} (self p) e) (add η p q)

mul : ∀ {B lB ℓ} {σ : L.Simᴵ ℓ (height B lB)} {a b} → Read B lB σ a b → ∀ n →
  Read B lB σ (iter (a L.+_) L.zero n) (leftMul b n)
mul p zero = rz
mul p (suc n) = add (λ q → q) p (mul p n)
```
