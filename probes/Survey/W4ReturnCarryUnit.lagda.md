# 每一外询问的完整单位返回含有内层反馈预算

第四层，无条件。对每个 Λ 外询问 j，第二层及更高塔上的实际单位返回均可从本塔标准值启动同时更新。第二层可取任意非零正询问的动态高度，第三层取下一个 h 不动点，第四层取该运算所有有限次迭代的上确界。塔号可任意上移。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnCarryUnit where

open import Data.Nat.Base using (ℕ; zero; suc; s≤s)
import Data.Nat.Properties as NP
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst; sym)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; l≼; ≼l; ≼-trans; ≼-refl; ≼-suc; s≼s)
import W4Block as W
import W4Path as P
open import WVOne using (T₀; read)
import B12Terminal as T
import B14Tower as View
import B15ReadPaths as Path
import B15FixedWitness as Ok
import B12EboRows as Rows
import B17CellPrefix as Cells
import B18Product as Mul
import B19Coefficient as Product
import B19OldSlots as Stage
import B20Room as Room
import B20StandardInside as Std
import B20Towers as Gen
import B20TowerValues as Real
import B27Joint as J
import Survey.W4RoomDiagonal as G
import Survey.W4RoomDerivative as D
import Survey.W4PTOSeededQuery as Seed
import Survey.W4ReturnCarry as C
import Survey.W4ReturnCarryFirst as First
import Survey.W4ReturnCarryValue as Values
open T.Run

above : ℕ → ℕ → ℕ
above p zero = p
above p (suc d) = suc (above p d)

down : ∀ p d → Path.Reach (W.tw (suc p)) (W.tw (suc (above p d)))
down p zero = Path.here
down p (suc d) = Path.via (down p d) Path.omega
standard : ∀ p d → Ok.pull (down p d) (P.Ok-tw (suc (above p d))) ≡ P.Ok-tw (suc p)
standard p zero = refl
standard p (suc d) = standard p d

module Host (p d j : ℕ) where
  k = suc (above p d)
  z = Gen.At.index k j
  module I = Std.At (above p d) z
  path = Path.via (down p d) I.basepath
  r = Room.sub path I.r
  cv = Room.cover path I.r I.cr
  okay : ok r ≡ P.Ok-tw (suc p)
  okay = trans (Room.cert path I.r)
    (trans (cong (Ok.pull (down p d)) (Std.root-ok (W.tw k) (W.↑ (W.tw k) z) (P.Ok-tw k) _)) (standard p d))
  x = Std.std k
  high : Room.Room r x
  high = Room.room path I.r (Std.append _ (suc k) k (s≤s NP.≤-refl))
  into : read (T.value r) ≼ J.f k j
  into = subst (read (T.value r) ≼_) (sym (Real.At.fresh k j)) (Room.below path I.r I.cr)

module Two (d j : ℕ) where
  module Q = Host 1 d j
  module A = C.At.Actual 0 Q.r Q.okay Q.cv Q.x Q.high
  module K = First.Stage A.A.found A.A.cert (Room.cover A.A.path A.A.one A.A.oc) Q.x A.room
  reserve = A.Use.reserve
  witness = λ n → W.iter D.next Q.x (suc n)

  module Inner (n u : ℕ) where
    module S = A.Use.Selected n (suc u)
    module Z = D.At S.state (A.Use.M.cover n) (witness n) (K.stages n)
    height = D.chain (witness n) u
    z = S.Trace.ix (suc u)
    slots : Room.Room S.child (reserve n)
    slots = A.Use.carry n z
    budget : G.H.cut height ≼ read z
    budget = Z.budget u
    paid : G.H.at height (reserve n) ≼ read (T.value S.child)
    paid = G.H.apply height z budget S.child S.cv (reserve n) slots (P.z≤ _)
    into : read (T.value S.child) ≼ J.f Q.k j
    into = ≼-trans (S.Trace.lift-value (suc u)) (≼-trans (Stage.bound (proj₂ (A.Use.J.child n)))
      (≼-trans (Room.below A.A.path A.A.one A.A.oc) (≼-trans (A.A.D.C.lift-value 1) Q.into)))
    dynamic : G.H.at height (reserve n) ≼ J.f Q.k j
    dynamic = ≼-trans paid into
    strict : L.suc (reserve n) ≼ J.f Q.k j
    strict = ≼-trans (s≼s (≼l 0 (≼-trans (≼-suc (≼-refl _)) (Seed.above (reserve n)))))
      (≼-trans (G.H.apply L.zero z (≼-trans (G.H.three height) budget) S.child S.cv (reserve n) slots (P.z≤ _)) into)

  whole : L.lim (λ n → L.suc (reserve n)) ≼ J.f Q.k j
  whole = l≼ (λ n → Inner.strict n 0)
  all : L.lim (λ n → L.lim (λ u → G.H.at (Inner.height n u) (reserve n))) ≼ J.f Q.k j
  all = l≼ (λ n → l≼ (Inner.dynamic n))

  -- 同一个返回容纳全部有限次取不动点；用真实起点时旧塔作左乘因子。
  iterates : D.block Q.x ≼ J.f Q.k j
  iterates = l≼ λ n → ≼-trans {a = witness n} {b = reserve n} {c = J.f Q.k j} (K.refill n)
    (≼-trans {a = reserve n} {b = L.suc (reserve n)} {c = J.f Q.k j} (≼-suc (≼-refl (reserve n))) (Inner.strict n 0))

  actual-cell : (Rows.child Q.k Mul.· D.block Q.x) ≼ Cells.cell Q.k j
  actual-cell = ≼-trans {a = Rows.child Q.k Mul.· D.block Q.x} {b = Rows.child Q.k Mul.· J.f Q.k j}
    {c = Cells.cell Q.k j} (Mul.mono {a = Rows.child Q.k} {b = Rows.child Q.k} {x = D.block Q.x} {y = J.f Q.k j}
      (≼-refl (Rows.child Q.k)) iterates) (proj₂ (Product.Cell.exact-cell Q.k j))

module Three (d j : ℕ) where
  module Q = Host 2 d j
  module V = Values.First Q.r Q.okay Q.cv Q.x Q.high
  paid : ∀ n u → D.next (V.reserve n) ≼ J.f Q.k j
  paid n u = ≼-trans (V.selected n u) Q.into
  all : L.lim (λ n → D.next (V.reserve n)) ≼ J.f Q.k j
  all = ≼-trans V.all Q.into

module Four (d j : ℕ) where
  module Q = Host 3 d j
  module V = Values.Second Q.r Q.okay Q.cv Q.x Q.high
  paid : ∀ n u → D.block (V.reserve n) ≼ J.f Q.k j
  paid n u = ≼-trans (V.selected n u) (≼-trans (V.A.into n u) Q.into)
  all : L.lim (λ n → D.block (V.reserve n)) ≼ J.f Q.k j
  all = ≼-trans V.all Q.into
```
