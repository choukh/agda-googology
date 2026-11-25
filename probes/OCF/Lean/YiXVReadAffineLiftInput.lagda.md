# YiXVReadAffineLiftInput
> 验收文件。档位：编译定理。实际孩子下降时的参照嵌入与提升行接口；零、一层全部前提先实填。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadAffineLiftInput where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOutInput as Out
import OCF.Lean.YiXVReadDown as Down
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadAffineGround as G

module Frame {root top} (within : top P.≤ᵀ root) where
  module C = Phi.Frame within
  σ : ∀ {cur} → Down.Down top cur → L.Simᴵ (T.lvl cur) (T.lvl root)
  σ Down.here = Out.σ within
  σ (Down.down-suc {r = r} d) q = σ d (J.σchild (S.suc r) tt q)
  σ (Down.down-lim {f = f} {d = a} d n) q = σ d (J.σchild (S.lim f a) n q)
  child : ∀ cur → Down.Down top cur → (c : S.Ch (J.ℓ cur)) →
    Down.Down top (J.slot cur (J.child-slot cur c))
  child S.zero d ()
  child (S.suc r) d c = Down.down-suc d
  child (S.lim f a) d n = Down.down-lim d n
  child (S.Ω () g) d c
  child (S.up r () y ny) d c
  σ-child : ∀ cur d c → _≡_ {A = L.Simᴵ (T.lvl (J.slot cur (J.child-slot cur c))) (T.lvl root)}
    (σ (child cur d c)) (λ q → σ d (J.σchild cur c q))
  σ-child S.zero d ()
  σ-child (S.suc r) d c = refl
  σ-child (S.lim f a) d n = refl
  σ-child (S.Ω () g) d c
  σ-child (S.up r () y ny) d c
  Lower : S.Tr S.zero → Set
  Lower cur = ∀ (d : Down.Down top cur) {x X a Y} (nx : J.ℓ top S.⊢ S.zero ◃ x) →
    A.Gd X → U.UR top x (C.φ X) → ∀ (c : S.Ch (J.ℓ cur)) {b Z nb} → A.Gd Y →
    U.UR top (O.Up (J.ℓ cur) (Down.src d) x nx a) (C.φ (L.add X (σ d) Y)) →
    A.Gd Z → U.Fam cur (J.child-slot cur c) (J.ctoB cur c b) Z →
    U.UR top (O.Up (J.ℓ cur) (Down.src d) x nx (S.up a c b nb))
      (C.φ (L.add (L.add X (σ d) Y) (λ q → σ d (J.σchild cur c q)) Z))
  zero : Lower S.zero
  zero d nx gx hx () gy ha gZ hZ
  one : Lower (S.suc S.zero)
  one d {x} {X} {a} {Y} nx gx hx tt gy ha gZ hZ = G.Ground.bound within
    (Down.down-suc d) (O.Up-nz (J.ℓ (S.suc S.zero)) (Down.src d) x nx a)
    (Add.good gx gy) ha (λ q → σ d (J.σchild (S.suc S.zero) tt q)) hZ
```
