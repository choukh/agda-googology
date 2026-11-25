# YiXVReadGrowth
> 验收文件。档位：编译定理。增长链的余量、源回灌界与部分和吸收，复用 RefAlgebra.sum-ω 与 CountableChain 的合法性。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadGrowth where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableAddFrame as Plus
import OCF.Lean.YiXVCountableIter as It
import OCF.Lean.YiXVCountableChain as Chain
import OCF.Lean.YiXVRefAlgebra as Ref
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPlus as ReadPlus
import OCF.Lean.YiXVReadGrowthInput as Q

two≤ω : ∀ {κ} {X : L.Ordᶜ κ} → A.Gd X → A.Le (X L.+ X) (Q.ω X)
two≤ω {κ} gx = Ref.sum-ω (A.Layer.rfl κ A.Gd< A.Le< gx)
  (A.Layer.rfl κ A.Gd< A.Le< gx)

module Run {κ} (P : L.Ordᶜ κ → L.Ordᶜ κ) (growth : Q.Growth P) where
  module D = A.Layer κ A.Gd< A.Le<
  open Q.Growth growth
  module C = Chain.Chain P input
  open C public renaming (good to gd; floor to fl)
  dbl : ∀ n → A.Le (L.suc (d n)) (d (suc n)) → A.Le (d (suc n) L.+ d (suc n)) (d (suc (suc n)))
  dbl n t = D.trans (two≤ω (gd (suc n))) (D.trans (db (d n) (gd n) (fl n))
    (mono (L.suc (d n)) (d (suc n)) (D.gs (gd n)) (gd (suc n))
      (D.pack (D.left (fl n)) (D.gs (gd n)) (D.ws (fl n))) t))
  incr : ∀ n → A.Le (L.suc (d n)) (d (suc n))
  incr zero = initial
  incr (suc n) = D.trans
    (Plus.mixed {σ = λ q → q} {τ = λ q → q} (D.rfl (gd (suc n)))
      (D.trans (proj₂ (Ω.model κ)) (fl (suc n)))) (dbl n (incr n))
  le : ∀ n → A.Le (d n) (d (suc n))
  le n = D.trans (D.pack (gd n) (D.gs (gd n)) (D.ws (D.rfl (gd n)))) (incr n)
  idx : ℕ → ℕ
  idx zero = 1
  idx (suc n) = suc (suc (idx n))
  module Rows {ν} (η : L.Ordᶜ κ → L.Ordᶜ ν) (out : Q.Output η) where
    module E = A.Layer ν A.Gd< A.Le<
    gη : ∀ n → A.Gd (η (d n))
    gη n = Q.Output.good out (d n) (gd n) (fl n)
    leη : ∀ n → A.Le (η (d n)) (η (d (suc n)))
    leη n = Q.Output.mono out (d n) (d (suc n)) (gd n) (gd (suc n)) (fl n) (le n)
    dblη : ∀ n → A.Le (η (d n) L.+ η (d n)) (η (d (suc n)))
    dblη n = E.trans (two≤ω (gη n)) (E.trans (Q.Output.db out (d n) (gd n) (fl n))
      (Q.Output.mono out (L.suc (d n)) (d (suc n)) (D.gs (gd n)) (gd (suc n))
        (D.pack (D.left (fl n)) (D.gs (gd n)) (D.ws (fl n))) (incr n)))

module Source (r : S.Tr S.zero) (P : L.Ordᶜ (T.lvl r) → L.Ordᶜ (T.lvl r))
  (growth : Q.Growth P) (g : S.Tr (J.ℓ r) → S.Tr (J.ℓ r))
  (step : Q.SourceStep r P g) (orbit : Q.Orbit r g) where
  module Rn = Run P growth
  open Rn
  c = Q.Orbit.points orbit
  Bounds : ℕ → Set
  Bounds n = Σ (L.Ordᶜ (T.lvl r)) λ X → A.Gd X × U.UR r (c n) X × A.Le (L.suc X) (d (idx n))
  bounds : ∀ n → Bounds n
  bounds zero = L.Ω (T.lvl r) , proj₁ (Ω.model (T.lvl r)) ,
    subst (λ a → U.UR r a (L.Ω (T.lvl r))) (sym (Q.Orbit.start orbit)) (B.zero r) , incr zero
  bounds (suc n) with bounds n
  ... | X , gx , ha , t = d (suc (idx n)) , gd (suc (idx n)) ,
    subst (λ a → U.UR r a (d (suc (idx n)))) (sym (Q.Orbit.next orbit n))
      (Q.SourceStep.step step (c n) X (d (idx n)) gx (gd (idx n)) (fl (idx n)) ha t) , incr (suc (idx n))
  module Slot (y : S.Tr S.zero) (η : L.Ordᶜ (T.lvl r) → L.Ordᶜ (T.lvl y))
    (out : Q.Output η) (F : ℕ → S.Tr (J.ℓ y))
    (hm : ∀ n X Y → A.Gd X → A.Gd Y → A.Le (L.Ω (T.lvl r)) Y →
      U.UR r (c n) X → A.Le (L.suc X) Y → U.UR y (F n) (η Y)) where
    open Rows η out
    rows : ∀ n → U.UR y (F n) (η (d (idx n)))
    rows n with bounds n
    ... | X , gx , ha , t = hm n X (d (idx n)) gx (gd (idx n)) (fl (idx n)) ha t
    sums : ∀ n → U.UR y (O.cum F n) (η (d (suc (idx n))))
    sums zero = B.weak y (rows zero) (leη 1)
    sums (suc n) = B.weak y
      (ReadPlus.plus y (gη (idx (suc n))) (B.weak y (sums n) (leη (suc (idx n))))
        (gη (idx (suc n))) (rows (suc n))) (dblη (idx (suc n)))
    result : ∀ nz → U.UR y (O.limc F nz) (L.lim (λ n → η (d n)))
    result nz = B.limU y (λ n → B.weak y (sums n)
      (E.pack (gη (suc (idx n))) (E.gl gη) (E.lr (suc (idx n)) (E.rfl (gη (suc (idx n)))))))

module Model (r : S.Tr S.zero) where
  module M = Q.Model r
  module C = Source r M.P M.growth M.g M.source M.orbit
  module Slt = C.Slot r M.P M.output M.F (λ n → M.row n (C.c n))
  actual : U.UR r (O.limc M.F M.nz) (L.lim (λ n → M.P (C.Rn.d n)))
  actual = Slt.result M.nz
```
