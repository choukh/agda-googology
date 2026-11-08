# 原γ₁全部分量与真实零层观察轨道

验收专用。所有逐树对应仅在可数零层建立；不把Same传入任意高层
Ω函数。内部ψ与ψ⁰通过原结构定理耦合，保持原G的初值及全部迭代。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableNextValueOrbit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaSeededIf using (module Prototype)
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
import OCF.Lean.GeneralOmegaCountableSuccessorIf as S
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.NoCumsum as N
import OCF.Align.GeneralOmegaGammaActual as G
open import OCF.Align.GeneralOmegaFiniteTypedObserveRun using (read-add)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.GeneralOmegaCountableObserveIf as C
module Z = Prototype S⊥ (hs hz)

leftZ : ∀ {a : L.Ordᶜ L.zero} {b} → a L.≅ B.read b → ∀ n →
  iter (a L.+_) L.zero n L.≅ B.read (Z.leftMul b n)
leftZ p zero = L.z≅
leftZ {b = b} p (suc n) = L.≅-trans (L.add-≅ p (leftZ p n))
  (L.≅-sym (read-add b (Z.leftMul b n)))
leftC : ∀ {a : L.Ordᶜ L.zero} {b : Cd} → a L.≅ B.read b → ∀ n →
  iter (a L.+_) L.zero n L.≅ B.read (C.leftMul b n)
leftC p zero = L.z≅
leftC {b = b} p (suc n) = L.≅-trans (L.add-≅ p (leftC p n))
  (L.≅-sym (read-add b (C.leftMul b n)))

typed-sound : ∀ c → L.ψ⁰ (B.read c) L.≅ B.read (Z.Typed c)
typed-sound hz = L.s≅ L.z≅
typed-sound (hs c) = L.l≅ (leftZ {b = Z.Typed c} (typed-sound c))
typed-sound (hl f) = L.l≅ (λ n → typed-sound (f n))
typed-sound (hΩ () g)

observe-sound : ∀ c → L.ψ⁰ (B.read c) L.≅ B.read (observe hz tt hz hself c)
observe-sound hz = L.s≅ L.z≅
observe-sound (hs c) = L.l≅ (leftC {b = observe hz tt hz hself c} (observe-sound c))
observe-sound (hl f) = L.l≅ (λ n → observe-sound (f n))
observe-sound (hΩ () g)

coordinates : ∀ n → B.read (Z.NoSum n) L.≅ N.D.G n
coordinates zero = L.s≅ L.z≅
coordinates (suc n) = L.≅-trans (L.≅-sym (typed-sound (Z.NoSum n)))
  (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → q} (L.upʳ {r = L.zero} {y = N.D.G n} (coordinates n)))

component-sound : ∀ n → G.component n L.≅ B.read (S.At.read-orbit hz tt n)
component-sound n = L.≅-trans (L.ψ⁰-≅ (L.≅-sym (coordinates n)))
  (observe-sound (Z.NoSum n))

forget-read : ∀ {a : L.Ordᶜ L.zero} {b : Cd} → a L.≅ B.read b → Same (B.forget a) b
forget-read {b = hz} L.z≅ = zz
forget-read {b = hs b} (L.s≅ p) = ss (forget-read p)
forget-read {b = hl f} (L.l≅ p) = ll (λ n → forget-read (p n))

component-shape : ∀ n → Same (B.forget (G.component n)) (S.At.read-orbit hz tt n)
component-shape n = forget-read (component-sound n)
whole-shape : Same (B.forget (N.γ 1)) (hl (S.At.read-orbit hz tt))
whole-shape = ll component-shape
```

component-shape是全n的原基本列结构关系，不是仅有值界；其右侧
就是SuccessorIf原read-orbit。尚未将这些分量再经Γ送入较后stage，
也未证明原reference-branch n的全部非有限高度观察模拟。
