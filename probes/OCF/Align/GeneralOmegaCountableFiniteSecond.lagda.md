# 可数高度运行器在真实数值高度2的完整值桥

验收专用。Ω处联立比较两个真实无累加轨道，初值均为1。
原内部ψ先经ψ⁰≅ψ连接递归观察，不把它定义性地当成ψ⁰。
Read.ro的相关坐标域是所有分支调用的依据，没有任意g的同余假设。
T和G分别是原可数高度观察器在真实num 2公共界、真实up输入上取目标1和0。
此处所有分类直接由原cl/dcl沿给定数值路径归约，不先假设路径无关性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteSecond where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
import OCF.Lean.GeneralOmegaCountableObserveIf as I
import OCF.Lean.GeneralOmegaCountableObserveRun as R
import OCF.Lean.GeneralOmegaCountableObserveClosed as C
import OCF.Lean.GeneralOmegaCountableObserveClass as N
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
open import OCF.Align.GeneralOmegaFiniteTypedIf using (Read; rz; rs; rl; ro; ru; U; Ωtree; stepᴵ; old-chain; floor)
open import OCF.Align.GeneralOmegaFiniteTypedRun using (sound; add)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

T : HB U → HB U
T b = R.observe (N.num 2) (N.num-legal 2) (N.num 1) (hsuc hself) (up b)
G : HB U → Cd
G b = R.observe (N.num 2) (N.num-legal 2) hz (hsuc (hsuc hself)) (up b)

read-add : ∀ (a b : Cd) → B.read (a ⊞ b) L.≅ (B.read a L.+ B.read b)
read-add a hz = L.≅-refl⁰ (B.read a)
read-add a (hs b) = L.s≅ (read-add a b)
read-add a (hl f) = L.l≅ (λ n → read-add a (f n))

left : ∀ {a : L.Ordᶜ L.zero} {b} → a L.≅ B.read b → ∀ n →
  iter (a L.+_) L.zero n L.≅ B.read (I.leftMul b n)
left p zero = L.z≅
left {b = b} p (suc n) = L.≅-trans (L.add-≅ p (left p n))
  (L.≅-sym (read-add b (I.leftMul b n)))

pure : ∀ {c} {x : L.Ordᶜ L.zero} → B.read c L.≅ x →
  L.ψ⁰ x L.≅ B.read (G (up c))
pure {c = hz} L.z≅ = L.s≅ L.z≅
pure {c = hs c} (L.s≅ p) = L.l≅ (left (pure p))
pure {c = hl f} (L.l≅ p) = L.l≅ (λ n → pure (p n))

self : ∀ {a b} → Read a b → a L.≅ a
self p = L.≅-trans (sound p) (L.≅-sym (sound p))

observe : ∀ {a b} → Read a b → L.ψ⁰ a L.≅ B.read (G b)
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
  new = I.iterate (λ c → G (g c)) (hs hz)
  coordinates : ∀ n → B.read (new n) L.≅ old n
  coordinates zero = L.s≅ L.z≅
  coordinates (suc n) = L.≅-trans
    (L.≅-sym (observe (p (old n) (new n) (coordinates n))))
    (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → q}
      (self (p (old n) (new n) (coordinates n))))
  outputs : ∀ n → L.ψ⁰ (f (old n)) L.≅ B.read (G (g (new n)))
  outputs n = observe (p (old n) (new n) (coordinates n))
observe (ru p) = pure p

mul : ∀ {a b} → Read a b → ∀ n →
  Read (iter (a L.+_) L.zero n) (I.leftMul b n)
mul p zero = rz
mul p (suc n) = add p (mul p n)

low-T : ∀ {c} {x : L.Ordᶜ L.zero} → B.read c L.≅ x →
  Read (L.ψ {i = L.suc L.zero} {ℓ = L.suc (L.suc L.zero)} L.zero (λ q → L.suc (L.suc q)) x) (T (up c))
low-T {c = hz} L.z≅ = floor
low-T {c = hs c} (L.s≅ p) = rl (mul (low-T p))
low-T {c = hl f} (L.l≅ p) = rl (λ n → low-T (p n))

typed-up : ∀ {a b} → Read a b → Read (stepᴵ a) (T b)
typed-up rz = floor
typed-up (rs p) = rl (mul (typed-up p))
typed-up (rl p) = rl (λ n → typed-up (p n))
typed-up (ro p) = ro (λ x c q → typed-up (p (L.tr⁻ L.z≅ x) c
  (L.≅-sym (L.tr⁻-≅ L.z≅ (L.≅-sym q)))))
typed-up (ru p) = low-T p

coordinates : ∀ n → Read (old-chain n) (I.iterate T Ωtree n)
coordinates zero = floor
coordinates (suc n) = typed-up (coordinates n)

whole : L.ψ⁰ (L.Ω (L.suc (L.suc L.zero))) L.≅ B.read (C.rawΓ (N.num 2))
whole = L.l≅ (λ n → observe (coordinates n))
```

whole核对的是新可数高度候选实际rawΓ(num 2)的完整原反馈。leg num 2、
Lg-leg和z⊲均按原定义归约到所用的真实路径；并未使用一般路径无关。
这里只给数值高度2，尚未声称全n有限一致性，更未声称Γ迭代已访问此输入。
