# 精确Read域上的单Ω观察模拟

验收专用。Ω处联立比较两个真实无累加轨道，初值均为1。
原内部ψ先经ψ⁰≅ψ连接递归观察，不把它定义性地当成ψ⁰。
Read.ro的相关坐标域是所有分支调用的依据，没有任意g的同余假设。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteTypedObserveRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
import OCF.Lean.GeneralOmegaOneObserveIf as O
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
open import OCF.Align.GeneralOmegaFiniteTypedIf using (Read; rz; rs; rl; ro; ru)
open import OCF.Align.GeneralOmegaFiniteTypedRun using (sound)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

read-add : ∀ (a b : Cd) → B.read (a ⊞ b) L.≅ (B.read a L.+ B.read b)
read-add a hz = L.≅-refl⁰ (B.read a)
read-add a (hs b) = L.s≅ (read-add a b)
read-add a (hl f) = L.l≅ (λ n → read-add a (f n))

left : ∀ {a : L.Ordᶜ L.zero} {b} → a L.≅ B.read b → ∀ n →
  iter (a L.+_) L.zero n L.≅ B.read (O.leftMul b n)
left p zero = L.z≅
left {b = b} p (suc n) = L.≅-trans (L.add-≅ p (left p n))
  (L.≅-sym (read-add b (O.leftMul b n)))

pure : ∀ {c} {x : L.Ordᶜ L.zero} → B.read c L.≅ x →
  L.ψ⁰ x L.≅ B.read (O.observe (up c))
pure {c = hz} L.z≅ = L.s≅ L.z≅
pure {c = hs c} (L.s≅ p) = L.l≅ (left (pure p))
pure {c = hl f} (L.l≅ p) = L.l≅ (λ n → pure (p n))

self : ∀ {a b} → Read a b → a L.≅ a
self p = L.≅-trans (sound p) (L.≅-sym (sound p))

observe : ∀ {a b} → Read a b → L.ψ⁰ a L.≅ B.read (O.observe b)
observe rz = L.s≅ L.z≅
observe (rs p) = L.l≅ (left (observe p))
observe (rl p) = L.l≅ (λ n → observe (p n))
observe (ro {f} {g} p) = L.l≅ outputs
  where
  Q : L.Ordᶜ L.zero → L.Ordᶜ L.zero
  Q x = L.ψ L.zero (λ q → q) (f x)
  old : ℕ → L.Ordᶜ L.zero
  old = iter Q (L.suc L.zero)
  new : ℕ → Cd
  new = O.iterate (λ c → O.observe (g c)) (hs hz)
  coordinates : ∀ n → B.read (new n) L.≅ old n
  coordinates zero = L.s≅ L.z≅
  coordinates (suc n) = L.≅-trans
    (L.≅-sym (observe (p (old n) (new n) (coordinates n))))
    (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → q}
      (self (p (old n) (new n) (coordinates n))))
  outputs : ∀ n → L.ψ⁰ (f (old n)) L.≅ B.read (O.observe (g (new n)))
  outputs n = observe (p (old n) (new n) (coordinates n))
observe (ru p) = pure p
```

结论在已有Read域上，不声称原观察器对任意高层值序单调。
零、后继、ℕ极限及Ω整条链均保留原定义，全部自然数输出同步。
