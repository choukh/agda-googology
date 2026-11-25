# YiXVSourceGrowthInput
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceGrowthInput where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (proj₁; proj₂)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
open import OCF.Align.YiLvValBase using (Ψ)
open import OCF.Align.Value using (≼-refl; ≼-trans; ≼-suc; 1≼ψ⁰)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVFiniteFloor as Floor
import OCF.Lean.YiXVFiniteGamma as Gamma
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourceSelf as Self
import OCF.Lean.YiXVSourceWorldGround as Ground
import OCF.Lean.YiXVZeroRead as Z

Ω : ∀ m → I.T m
Ω m = L.Ω (L.natᴵ m)
ω : ∀ {m} → I.T m → I.T m
ω X = L.lim (iter (L._+_ X) L.zero)
record Growth (m : ℕ) (P : I.T m → I.T m) : Set where
  field
    good : ∀ X → A.Gd m X → A.Le m (Ω m) X → A.Gd m (P X)
    floor : ∀ X → A.Gd m X → A.Le m (Ω m) X → A.Le m (Ω m) (P X)
    mono : ∀ X Y → A.Gd m X → A.Gd m Y → A.Le m (Ω m) X → A.Le m X Y → A.Le m (P X) (P Y)
    db : ∀ X → A.Gd m X → A.Le m (Ω m) X → A.Le m (ω (P X)) (P (L.suc X))
    initial : A.Le m (L.suc (Ω m)) (P (Ω m))
record Output (m j : ℕ) (ν : I.T m → I.T j) : Set where
  field
    good : ∀ X → A.Gd m X → A.Le m (Ω m) X → A.Gd j (ν X)
    mono : ∀ X Y → A.Gd m X → A.Gd m Y → A.Le m (Ω m) X → A.Le m X Y → A.Le j (ν X) (ν Y)
    db : ∀ X → A.Gd m X → A.Le m (Ω m) X → A.Le j (ω (ν X)) (ν (L.suc X))
record SourceStep (m : ℕ) (P : I.T m → I.T m) (g : J.Tr m → J.Tr m) : Set where
  field
    step : ∀ a X Y → A.Gd m X → A.Gd m Y → A.Le m (Ω m) Y → U.U m a X → A.Le m (L.suc X) Y → U.U m (g a) (P Y)

P : ∀ m → I.T m → I.T m
P m X = Ψ m (Ω m L.+ X)
gP : ∀ m X → A.Gd m X → A.Gd m (P m X)
gP m X gx = Gamma.At.ψ-good m (Add.plus-good m {X = Ω m} {Y = X} (proj₁ (B.Ω-model m F.zero)) gx)
mP : ∀ m X Y → A.Le m X Y → A.Le m (P m X) (P m Y)
mP m X Y t = Gamma.At.ψ-mono m (Add.plus m {X = Ω m} {X′ = Ω m} {Y = X} {Y′ = Y}
  (B.rfl m F.zero {X = Ω m} (proj₁ (B.Ω-model m F.zero))) t)
model : ∀ m → Growth m (P m)
Growth.good (model m) X gx o = gP m X gx
Growth.floor (model m) X gx o = Floor.floor m L.zero (λ q → L.suc q) (Ω m L.+ X) (gP m X gx)
Growth.mono (model m) X Y gx gy o t = mP m X Y t
Growth.db (model m) X gx o = B.rfl m F.zero {X = ω (P m X)} (B.gl m F.zero {a = iter (L._+_ (P m X)) L.zero} (It.good m (P m X) (gP m X gx)))
Growth.initial (model m) = B.trans m F.zero {X = L.suc (Ω m)} {Y = Ψ m (Ω m)} {Z = P m (Ω m)}
  (Gamma.At.inv-Ω m) (Gamma.At.ψ-mono m (Right.right m m (B.rfl m F.zero {X = Ω m} (proj₁ (B.Ω-model m F.zero)))
    (λ q → q) (Ω m) (proj₁ (B.Ω-model m F.zero))))
output-model : ∀ m → Output m m (P m)
Output.good (output-model m) = Growth.good (model m)
Output.mono (output-model m) = Growth.mono (model m)
Output.db (output-model m) = Growth.db (model m)

χ : ∀ m → J.Tr m → J.Tr m
χ zero = Fold.ψs S.zero tt tt (Fold.B₀ S.zero) S.zero Path.self (S.suc S.zero) S.◃s
χ (suc n) = Self.Actual.χ n
source-model : ∀ m → SourceStep m (P m) (χ m)
SourceStep.step (source-model zero) a X Y gx gy o ha t = ≼-trans
  (proj₂ (World.upper (≼-trans ha (≼-trans (≼-suc (≼-refl X)) t))))
  (proj₂ (Z.approx L.zero (λ q → L.suc q) (Ω 0 L.+ Y)))
  where
  module World = Ground.World 0 (Ω 0) tt (λ q → q) (Fold.B₀ S.zero) (1≼ψ⁰ (Ω 0)) (1≼ψ⁰ (Ω 0))
SourceStep.step (source-model (suc n)) a X Y gx gy o ha t = UB.weakU (suc n) (Self.Actual.result n gx ha)
  (mP (suc n) X Y (B.trans (suc n) F.zero {X = X} {Y = L.suc X} {Z = Y}
    (B.w≤ (suc n) F.zero {X = X} {Y = X} (B.rfl (suc n) F.zero {X = X} gx)) t))

record Orbit (m : ℕ) (g : J.Tr m → J.Tr m) : Set where
  field
    points : ℕ → J.Tr m
    start : points zero ≡ S.zero
    next : ∀ n → points (suc n) ≡ g (points n)
iter-orbit : ∀ m g → Orbit m g
Orbit.points (iter-orbit m g) = O.iter g S.zero
Orbit.start (iter-orbit m g) = refl
Orbit.next (iter-orbit m g) n = refl
```
