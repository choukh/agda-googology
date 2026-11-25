# YiXVFiniteTransportInputs
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteTransportInputs where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst; subst₂)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVCanTau as T
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteBridge as E
import OCF.Lean.YiXVFiniteInputs as In
import OCF.Lean.YiXVFiniteTransportShape as S

record Ops (n : ℕ) : Set where
  field
    good : ∀ d i (X : I.T (I.rank n i)) → A.GoFam n i X → A.GoFam n i (S.τ d (I.rank n i) X)
    mono : ∀ d i (X Y : I.T (I.rank n i)) → A.LeFam n i X Y → A.LeFam n i (S.τ d (I.rank n i) X) (S.τ d (I.rank n i) Y)
    pair : ∀ d i (X : I.T (I.rank n i)) → A.GoFam n i X →
      A.LeFam n i X (S.τ d (I.rank n i) X) × A.LeFam n i (S.τ d (I.rank n i) X) X

ops₀ : Ops 0
Ops.good ops₀ d F.zero X gx = tt
Ops.good ops₀ d (F.suc ()) X gx
Ops.mono ops₀ S.fwd F.zero X Y p = ≼-trans (proj₁ (T.plus≈ X)) (≼-trans p (proj₂ (T.plus≈ Y)))
Ops.mono ops₀ S.bwd F.zero X Y p = ≼-trans (proj₁ (O.tr⁻≈ X)) (≼-trans p (proj₂ (O.tr⁻≈ Y)))
Ops.mono ops₀ d (F.suc ()) X Y p
Ops.pair ops₀ S.fwd F.zero X gx = proj₂ (T.plus≈ X) , proj₁ (T.plus≈ X)
Ops.pair ops₀ S.bwd F.zero X gx = proj₂ (O.tr⁻≈ X) , proj₁ (O.tr⁻≈ X)
Ops.pair ops₀ d (F.suc ()) X gx

module Inputs (n : ℕ) (old : Ops n) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  good-pull : ∀ d {i} (q : i L.<ᴵ L.natᴵ (suc n)) u → D.GU q u → D.GU q (S.pull d q u)
  good-pull d q u gu = subst (A.GoFam n (E.idx n q)) (sym (S.ref-pull d n q u))
    (Ops.good old (S.op d) (E.idx n q) (I.Uref n q u) gu)
  rel-pull : ∀ d {i} (q : i L.<ᴵ L.natᴵ (suc n)) u v → D.RU q u v → D.RU q (S.pull d q u) (S.pull d q v)
  rel-pull d q u v p = subst₂ (A.LeFam n (E.idx n q)) (sym (S.ref-pull d n q u)) (sym (S.ref-pull d n q v))
    (Ops.mono old (S.op d) (E.idx n q) (I.Uref n q u) (I.Uref n q v) p)
  floor-pull : ∀ d {i} (q : i L.<ᴵ L.natᴵ (suc n)) u → D.Floor q u → D.Floor q (S.pull d q u)
  floor-pull d q u p = subst (A.LeFam n (E.idx n q) (E.Ω (E.num n q))) (sym (S.ref-pull d n q u))
    (B.trans n (E.idx n q) {X = E.Ω (E.num n q)} {Y = S.τ (S.op d) (E.num n q) (E.Ω (E.num n q))}
      {Z = S.τ (S.op d) (E.num n q) (I.Uref n q u)}
      (proj₁ (Ops.pair old (S.op d) (E.idx n q) (E.Ω (E.num n q)) (proj₁ (B.Ω-model n (E.idx n q)))))
      (Ops.mono old (S.op d) (E.idx n q) (E.Ω (E.num n q)) (I.Uref n q u) p))
  start-rel : ∀ d {i} (q : i L.<ᴵ L.natᴵ (suc n)) → D.RU q (C.start q) (S.pull d q (C.start q))
  start-rel d q = subst (λ x → A.LeFam n (E.idx n q) x (I.Uref n q (S.pull d q (C.start q))))
    (sym (In.At.ref-start n q)) (floor-pull d q (C.start q) (In.At.floor-start n q))
  pair-pull : ∀ d {i} (q : i L.<ᴵ L.natᴵ (suc n)) u → D.GU q u →
    D.RU q u (S.pull d q u) × D.RU q (S.pull d q u) u
  pair-pull d q u gu =
    subst (A.LeFam n (E.idx n q) (I.Uref n q u)) (sym (S.ref-pull d n q u))
      (proj₁ (Ops.pair old (S.op d) (E.idx n q) (I.Uref n q u) gu)) ,
    subst (λ x → A.LeFam n (E.idx n q) x (I.Uref n q u)) (sym (S.ref-pull d n q u))
      (proj₂ (Ops.pair old (S.op d) (E.idx n q) (I.Uref n q u) gu))
  floor-right : ∀ {i} (q : i L.<ᴵ L.natᴵ (suc n)) u v → D.Floor q u → D.RU q u v → D.Floor q v
  floor-right q u v o p = B.trans n (E.idx n q) {X = E.Ω (E.num n q)} {Y = I.Uref n q u} {Z = I.Uref n q v} o p
  u≤pull-v : ∀ d {i} (q : i L.<ᴵ L.natᴵ (suc n)) u v → D.GU q v → D.RU q u v → D.RU q u (S.pull d q v)
  u≤pull-v d q u v gv p = B.trans n (E.idx n q) {X = I.Uref n q u} {Y = I.Uref n q v} {Z = I.Uref n q (S.pull d q v)}
    p (proj₁ (pair-pull d q v gv))
  pull-u≤v : ∀ d {i} (q : i L.<ᴵ L.natᴵ (suc n)) u v → D.GU q u → D.RU q u v → D.RU q (S.pull d q u) v
  pull-u≤v d q u v gu p = B.trans n (E.idx n q) {X = I.Uref n q (S.pull d q u)} {Y = I.Uref n q u} {Z = I.Uref n q v}
    (proj₂ (pair-pull d q u gu)) p

module Input₀ = Inputs 0 ops₀
actual : A.LeFam 0 F.zero (L.Ω L.zero) (I.Uref 0 L.zero (S.pull S.fwd L.zero (C.start L.zero)))
actual = Input₀.floor-pull S.fwd L.zero (C.start L.zero) (In.At.floor-start 0 L.zero)
```
