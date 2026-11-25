# 正塔的所有反馈重置值能同时进入下一次运行的零槽

第四层，无条件。在实际后继运行的每个更新时刻，取当时正槽所产生的整条反馈轨道。把原槽下界加在每个被问到的独立重置值之前，所得有限和的上确界可传给下一阶段任一被选正分支的全部零槽。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnCarry where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; l≼; ≼l; +-mono; s≼s; z≼)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
open import WVOne using (read; T₀; read-+)
open import WVTwo using (◃→≼)
import B12Terminal as T
import B12ActualSlots as C
import B12Strict as Strict
import B13FiniteLift as U
import B15Spine as S
import B15ReadPaths as Path
import B15FixedWitness as Witness
import B17CellPrefix as Sum
import B19RowSecondParent as Add
import B19OldSlots as Stage
import B20Room as Room
import B20StandardInside as Std
import B21TowerPorts as Port
import B21TowerSeed as Entry
open T.Run

module At (m : ℕ) where
  k = W.tw m
  mid = W.tw (suc m)
  h = S.branch k

  module Orbit (B : F.Base mid) (x : T₀) where
    module A = Port.At m B (O.Ωt W.zero)
    unit = λ j → read (proj₁ (A.independent (A.index j)))
    total : ℕ → T₀
    total zero = x L.+ unit 0
    total (suc n) = total n L.+ (x L.+ unit (suc n))
    budget : T₀
    budget = L.lim total
    strict : L.suc (x L.+ Std.std m) ≼ budget
    strict = ≼l 1 (+-mono {a = total 0} {a′ = total 0} {b = WVOne.𝟏} {b′ = x L.+ unit 1}
      (≼-refl _) (≼-trans (Strict.strict (proj₂ (A.independent (A.index 1)))) (WVOne.≼-+ˡ x (unit 1))))

    module Directed (v : O.Tr⁺ W.zero) (vx : x ≼ read (proj₁ v))
                    (c : W.Tr k) (w : W.zero W.≤ h c) where
      module R = Port.At m B v
      summand : ∀ j → x L.+ unit j ≼ read (R.copies j)
      summand j = ≼-trans (+-mono vx (Add.copy (proj₁ (A.independent (A.index j)))))
        (read-+ (proj₁ v) (O.ι W.zero (proj₁ (A.independent (A.index j)))))
      prefix : ∀ n → total n ≼ read (O.cum R.copies n)
      prefix zero = summand 0
      prefix (suc n) = ≼-trans (+-mono (prefix n) (summand (suc n))) (read-+ (O.cum R.copies n) (R.copies (suc n)))
      shape : read (R.result (W.inc c w)) ≡ L.lim (λ n → read (O.cum R.copies n))
      shape = Sum.lookup (F.kp mid R.o R.pos (W.inc c w)) (R.branch (W.inc c w)) R.action
      paid : budget ≼ read (R.result (W.inc c w))
      paid = subst (budget ≼_) (sym shape) (l≼ λ n → ≼l n (prefix n))

    paid : ∀ {o : P.Ok mid} → o ≡ P.Ok-tw (suc m) → ∀ v → x ≼ read (proj₁ v) → ∀ t →
      C._⊴_ (proj₁ (O.Ωt mid)) t → ∀ c w → budget ≼ read (proj₁ (F.ψ mid o B W.zero (W.inc c w) v t))
    paid refl v vx t (inj₁ refl) c w = Directed.paid v vx c w
    paid refl v vx t (inj₂ d) c w = ≼-trans (Directed.paid v vx c w) (◃→≼ (F.mono mid (P.Ok-tw _) B W.zero (W.inc c w) v d))

  module Carry (r : T.Run (U.sc mid)) (o : proj₂ (ok r) tt ≡ P.Ok-tw (suc m)) (cr : C.Covered r)
               (x : T₀) (initial : Room.Room r x) where
    module E = Entry.Layer.Inside m r o cr
    module J = E.J
    module M = E.M
    initialB = bs M.r₀
    reserve : ℕ → T₀
    reserve zero = Orbit.budget initialB x
    reserve (suc n) = Orbit.budget (M.S n) (reserve n)

    carry : ∀ n c (w : W.zero W.≤ h c) → reserve n ≼ read (proj₁ (M.S n W.zero (W.inc c w)))
    carry zero c w = Orbit.paid initialB x o _ (initial (W.inc tt (W.inc c w))) M.c (cr mid (W.inc tt W.self)) c w
    carry (suc n) c w = Orbit.paid (M.S n) (reserve n) o _ (carry n c w) M.c (cr mid (W.inc tt W.self)) c w

    module Selected (n u : ℕ) where
      state = J.F.snap n
      module Trace = S.Cardinal k h state
      child = Trace.child u
      cv = Trace.cover (M.cover n) u
      path = Path.base k (W.↑ k (Trace.ix u))
      target = Room.sub path child
      covered = Room.cover path child cv
      standard : ok target ≡ P.Ok-tw m
      standard = trans (Room.cert path child) (base-ok (ok state) o (Trace.ix u))
        where
        base-ok : ∀ (a : P.Ok mid) → a ≡ P.Ok-tw (suc m) → ∀ c →
          Witness.pull (Path.base k (W.↑ k c)) (proj₂ a c) ≡ P.Ok-tw m
        base-ok a refl c = Std.root-ok k (W.↑ k c) (P.Ok-tw m) _
      common : Room.Room target (reserve n)
      common = Room.room path child (carry n (Trace.ix u))
      below : read (T.value target) ≼ read (T.value r)
      below = ≼-trans (Room.below path child cv) (≼-trans (Trace.lift-value u) (Stage.bound (proj₂ (J.child n))))

  module Actual (r : T.Run (W.tw (suc (suc m)))) (o : ok r ≡ P.Ok-tw (suc (suc m))) (cr : C.Covered r)
                (x : T₀) (high : Room.Room r x) where
    module A = Entry.Layer.At m r o cr
    room : Room.Room A.found x
    room = Room.room A.path A.one (λ w → high (W.inc (A.D.C.ix 1) w))
    module Use = Carry A.found A.cert (Room.cover A.path A.one A.oc) x room
    into : ∀ n u → read (T.value (Use.Selected.target n u)) ≼ read (T.value r)
    into n u = ≼-trans (Use.Selected.below n u) (≼-trans (Room.below A.path A.one A.oc) (A.D.C.lift-value 1))
```
