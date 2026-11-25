# YiXVSourceWorldInput
> 验收文件。档位：编译定理。有限层基底世界与输出接口；标准基底的全部前提已填。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceWorldInput where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegFold as Fold
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss)
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; 1≼ψ⁰)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteFold as FinFold
import OCF.Lean.YiXVFiniteFoldOmega as Omega
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Model

up : ∀ {n k} → P.Path n k → P.Path (suc n) (suc k)
up P.top = P.top
up (P.down p) = P.down (up p)
below : ∀ {n j} → Sbᶠ n j → L.natᴵ j L.<ᴵ L.natᴵ (suc n)
below s0 = L.zero
below (ss s) = L.suc (below s)
pc : ∀ {n H j} → P.Path H n → Sbᶠ n j → L.natᴵ j L.<ᴵ L.natᴵ (suc H)
pc p s0 = P.σ (up p) L.zero
pc p (ss s) = L.suc (P.σ p (below s))
φ : ∀ {n H j} → P.Path H n → Sbᶠ n j → I.T H → I.T j
φ p s = L.ψ (pc p s) (λ q → L.suc q)
φ-good : ∀ {n H j} (p : P.Path H n) (s : Sbᶠ n j) {Z} → A.Gd H Z → A.Gd j (φ p s Z)
φ-good {H = H} {j} p s {Z} gz = Q.Ops.good (FinFold.ops H) j (pc p s) (λ q → L.suc q) Z gz
φ-mix : ∀ {n n′ H j} (p : P.Path H n) (s : Sbᶠ n j) (p′ : P.Path H n′) (s′ : Sbᶠ n′ j) {Z Z′} →
  A.Le H Z Z′ → A.Le j (φ p s Z) (φ p′ s′ Z′)
φ-mix {H = H} {j} p s p′ s′ {Z} {Z′} t = Q.Ops.mono (FinFold.ops H) j (pc p s) (pc p′ s′)
  (λ q → L.suc q) (λ q → L.suc q) Z Z′ t

record World (n H : ℕ) (p : P.Path H n) (SrcB : Fold.Base (J.nat n)) (Z : I.T H) : Set where
  field
    good : A.Gd H Z
    bot : read (Fold.b⊥ SrcB) ≼ L.ψ⁰ Z
    slots : ∀ j (s : Sbᶠ n j) → U.U j (Fold.bs SrcB (J.nat j) (Slots.pth s)) (φ p s Z)

record Out (n H : ℕ) (p : P.Path H n) (SrcB : Fold.Base (J.nat n)) (Z : I.T H) (x : J.Tr n) (X : I.T n) : Set where
  cap : I.T H
  cap = L.add Z (P.σ p) X
  field
    bot : read (Fold.ψ⊥ (J.nat n) (Model.ev n) (Model.rt n) SrcB x) ≼ L.ψ⁰ cap
    slots : ∀ j (s : Sbᶠ n j) →
      U.U j (Fold.ψs (J.nat n) (Model.ev n) (Model.rt n) SrcB (J.nat j) (Slots.pth s)
        (Fold.bs SrcB (J.nat j) (Slots.pth s)) (Fold.ns SrcB (J.nat j) (Slots.pth s)) x) (φ p s cap)

model : ∀ n H (p : P.Path H n) → World n H p (Fold.B₀ (J.nat n)) (L.Ω (L.natᴵ H))
World.good (model n H p) = proj₁ (B.Ω-model H F.zero)
World.bot (model n H p) = 1≼ψ⁰ (L.Ω (L.natᴵ H))
World.slots (model n H p) j s = UB.weakU j (UB.ΩU j) (Omega.two j H (pc p s) (λ q → L.suc q))
```
