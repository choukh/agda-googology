# YiXVSourceGrowth
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceGrowth where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePlus as Plus
import OCF.Lean.YiXVSourceSelf as Self
import OCF.Lean.YiXVSourceGrowthInput as Q

module Run (m : ℕ) (P : I.T m → I.T m) (growth : Q.Growth m P) where
  open Q.Growth growth
  d : ℕ → I.T m
  d = iter P (Q.Ω m)
  mutual
    gd : ∀ n → A.Gd m (d n)
    gd zero = proj₁ (B.Ω-model m F.zero)
    gd (suc n) = good (d n) (gd n) (fl n)
    fl : ∀ n → A.Le m (Q.Ω m) (d n)
    fl zero = B.rfl m F.zero {X = Q.Ω m} (proj₁ (B.Ω-model m F.zero))
    fl (suc n) = floor (d n) (gd n) (fl n)
  dbl : ∀ n → A.Le m (L.suc (d n)) (d (suc n)) → A.Le m (d (suc n) L.+ d (suc n)) (d (suc (suc n)))
  dbl n t = B.trans m F.zero {X = d (suc n) L.+ d (suc n)} {Y = Q.ω (d (suc n))} {Z = d (suc (suc n))}
    (B.lr m F.zero {X = d (suc n) L.+ d (suc n)} {a = iter (L._+_ (d (suc n))) L.zero}
      (Add.plus-good m {X = d (suc n)} {Y = d (suc n)} (gd (suc n)) (gd (suc n)))
      (It.good m (d (suc n)) (gd (suc n))) 2
      (B.rfl m F.zero {X = d (suc n) L.+ d (suc n)} (Add.plus-good m {X = d (suc n)} {Y = d (suc n)} (gd (suc n)) (gd (suc n)))))
    (B.trans m F.zero {X = Q.ω (d (suc n))} {Y = P (L.suc (d n))} {Z = d (suc (suc n))}
      (db (d n) (gd n) (fl n))
      (mono (L.suc (d n)) (d (suc n)) (B.gs m F.zero {X = d n} (gd n)) (gd (suc n))
        (B.w≤ m F.zero {X = Q.Ω m} {Y = d n} (fl n)) t))
  incr : ∀ n → A.Le m (L.suc (d n)) (d (suc n))
  incr zero = initial
  incr (suc n) = B.trans m F.zero {X = L.suc (d (suc n))} {Y = d (suc n) L.+ d (suc n)} {Z = d (suc (suc n))}
    (Add.plus m {X = d (suc n)} {X′ = d (suc n)} {Y = L.suc L.zero} {Y′ = d (suc n)}
      (B.rfl m F.zero {X = d (suc n)} (gd (suc n)))
      (B.trans m F.zero {X = L.suc L.zero} {Y = Q.Ω m} {Z = d (suc n)} (Data.Product.proj₂ (B.Ω-model m F.zero)) (fl (suc n)))) (dbl n (incr n))
  le : ∀ n → A.Le m (d n) (d (suc n))
  le n = B.trans m F.zero {X = d n} {Y = L.suc (d n)} {Z = d (suc n)}
    (B.w≤ m F.zero {X = d n} {Y = d n} (B.rfl m F.zero {X = d n} (gd n))) (incr n)
  idx : ℕ → ℕ
  idx zero = 1
  idx (suc n) = suc (suc (idx n))

  module Rows (j : ℕ) (ν : I.T m → I.T j) (out : Q.Output m j ν) where
    gν : ∀ n → A.Gd j (ν (d n))
    gν n = Q.Output.good out (d n) (gd n) (fl n)
    leν : ∀ n → A.Le j (ν (d n)) (ν (d (suc n)))
    leν n = Q.Output.mono out (d n) (d (suc n)) (gd n) (gd (suc n)) (fl n) (le n)
    dblν : ∀ n → A.Le j (ν (d n) L.+ ν (d n)) (ν (d (suc n)))
    dblν n = B.trans j F.zero {X = ν (d n) L.+ ν (d n)} {Y = Q.ω (ν (d n))} {Z = ν (d (suc n))}
      (B.lr j F.zero {X = ν (d n) L.+ ν (d n)} {a = iter (L._+_ (ν (d n))) L.zero}
        (Add.plus-good j {X = ν (d n)} {Y = ν (d n)} (gν n) (gν n)) (It.good j (ν (d n)) (gν n)) 2
        (B.rfl j F.zero {X = ν (d n) L.+ ν (d n)} (Add.plus-good j {X = ν (d n)} {Y = ν (d n)} (gν n) (gν n))))
      (B.trans j F.zero {X = Q.ω (ν (d n))} {Y = ν (L.suc (d n))} {Z = ν (d (suc n))}
        (Q.Output.db out (d n) (gd n) (fl n))
        (Q.Output.mono out (L.suc (d n)) (d (suc n)) (B.gs m F.zero {X = d n} (gd n)) (gd (suc n))
          (B.w≤ m F.zero {X = Q.Ω m} {Y = d n} (fl n)) (incr n)))

module Chain (m : ℕ) (P : I.T m → I.T m) (growth : Q.Growth m P)
  (gk : J.Tr m → J.Tr m) (step : Q.SourceStep m P gk) (orbit : Q.Orbit m gk) where
  open Run m P growth
  c : ℕ → J.Tr m
  c = Q.Orbit.points orbit
  Bounds : ℕ → Set
  Bounds n = Σ (I.T m) λ X → A.Gd m X × U.U m (c n) X × A.Le m (L.suc X) (d (idx n))
  bounds : ∀ n → Bounds n
  bounds zero = Q.Ω m , proj₁ (B.Ω-model m F.zero) , subst (λ a → U.U m a (Q.Ω m)) (sym (Q.Orbit.start orbit)) (UB.zeroU m) , incr zero
  bounds (suc n) with bounds n
  ... | X , gx , h , t = d (suc (idx n)) , gd (suc (idx n)) ,
    subst (λ a → U.U m a (d (suc (idx n)))) (sym (Q.Orbit.next orbit n))
      (Q.SourceStep.step step (c n) X (d (idx n)) gx (gd (idx n)) (fl (idx n)) h t) , incr (suc (idx n))

  module Slot (j : ℕ) (ν : I.T m → I.T j) (out : Q.Output m j ν) (F : ℕ → J.Tr j)
    (hm : ∀ n X Y → A.Gd m X → A.Gd m Y → A.Le m (Q.Ω m) Y → U.U m (c n) X → A.Le m (L.suc X) Y → U.U j (F n) (ν Y)) where
    open Rows j ν out
    rows : ∀ n → U.U j (F n) (ν (d (idx n)))
    rows n with bounds n
    ... | X , gx , h , t = hm n X (d (idx n)) gx (gd (idx n)) (fl (idx n)) h t
    sums : ∀ n → U.U j (O.cum F n) (ν (d (suc (idx n))))
    sums zero = UB.weakU j (rows zero) (leν 1)
    sums (suc n) = UB.weakU j (Plus.plus j (gν (idx (suc n)))
      (UB.weakU j (sums n) (leν (suc (idx n)))) (gν (idx (suc n))) (rows (suc n))) (dblν (idx (suc n)))
    result : ∀ nz → U.U j (O.limc F nz) (L.lim (λ n → ν (d n)))
    result nz = UB.limU j (λ n → UB.weakU j (sums n)
      (B.lr j F.zero {X = ν (d (suc (idx n)))} {a = λ n → ν (d n)} (gν (suc (idx n))) gν (suc (idx n))
        (B.rfl j F.zero {X = ν (d (suc (idx n)))} (gν (suc (idx n))))))

module Model (m : ℕ) where
  module C = Chain m (Q.P m) (Q.model m) (Q.χ m) (Q.source-model m) (Q.iter-orbit m (Q.χ m))
  module R = C.Slot m (Q.P m) (Q.output-model m) (λ n → Q.χ m (C.c n)) (λ n → Q.SourceStep.step (Q.source-model m) (C.c n))

χ-nz : ∀ m x → J.nat m S.⊢ S.zero ◃ Q.χ m x
χ-nz zero = Fold.nzs S.zero _ _ (Fold.B₀ S.zero) S.zero Path.self (S.suc S.zero) S.◃s
χ-nz (suc n) = Self.Actual.nχ n
actual : ∀ m → U.U m
  (O.limc (λ n → Q.χ m (O.iter (Q.χ m) S.zero n)) (λ n → χ-nz m (O.iter (Q.χ m) S.zero n)))
  (L.lim (λ n → Q.P m (iter (Q.P m) (Q.Ω m) n)))
actual m = Model.R.result m (λ n → χ-nz m (O.iter (Q.χ m) S.zero n))
```
