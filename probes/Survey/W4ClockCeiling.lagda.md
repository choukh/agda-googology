# 反复更新时钟仍在首询问的一个固定分支以内

第四层，无条件。以首询问的第 k 个参照值为界的任一起点，反复取上方首个 ε 数作时钟，全部有限轮共用下一份前缀里的同一个上界。任意相邻两份参照值满足 ζ⁺(aₖ) < aₖ₊₁，其中 ζ⁺ 的命名用经典标定。从原起点出发所得上确界严格小于三份前缀的值 a₂。[真实塔给出的下界](W4ClockClosure.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ClockCeiling where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-suc; ≼-trans; ≼l; l≼; s≼s; ≅→≼)
open import OCF.Align.TightValBase using (s≼-irrefl)
import OCF.Align.BTBOValUp as U
import OCF.Align.BTBOValDn as Dn
open import WVOne using (T₀; 𝟏)
open import YiLAB7Replay using (Ω₂ᴸ)
import YiLAB10Src as Y
import B12LimitSrc as A
import B12Omega3Ref as R
import B12Omega3Cuts as Cut
import B13Target as P
import B14RefFixed as Fix
import B15RefSource as One
import B17RefAllSource as Src
import B19OldSource as Old
import B19RowSecond as Coeff
import B21TowerGrowth as Tower
import B22RowSource as Tail
import B22MovingIndex as E
import B22TowerCut as K
import B24RRows as Rows
import B24RCompare as Compare
import B24RExit as Exit
import B24AQueries as Q
import B24ROrbit as Seed
import B25ACap as Base
import Survey.W4PTOClock as C
import Survey.W4PTOFirstQuery as Ref
import Survey.W4RouteTests as Test
import Survey.W4ClockClosure as Stage

module At (k : ℕ) where
  base = A.aligned (Y.up-rel k) (Y.dn-rel k) (Y.regular k)
  module Row = Rows.At (Y.ll k) (Y.regular k)
  module M = Compare.Model (Y.regular k) (Y.ss k) base
  raw = M.inject
  q = λ j → P.pass (raw j)
  v = λ j → L.ψ⁰ (q j)
  prefix : ∀ j → A.Aligned (Src.pass (M.prefix j)) (q j)
  prefix j = Exit.passed (A.aligned (M.base-up (≼-refl j))
    (M.base-down j) (L.add-≅ {σ = λ r → L.suc (L.suc r)}
      {σ′ = λ r → L.suc (L.suc r)} (Y.regular k) (L.≅-refl⁰ j)))
  rq = λ j → A.Aligned.regular (prefix j)
  copies : ∀ j → U.Mh Y.a (raw j)
  copies j = U.M-add-r {σ = λ r → L.suc (L.suc r)} j (Ref.copies k)
  select : ∀ j → Fix.Select (q L.zero) (q j)
  select L.zero = Fix.here
  select (L.suc j) = Fix.branch 1 (select j)
  select (L.lim f) = Fix.branch 0 (select (f 0))

  module Step (j : T₀) where
    p = q j
    right = λ a → p L.+ L.up L.zero (Fix.collapse a)
    reg : ∀ {a : A.Lev₂} → a L.≅ a → right a L.≅ right a
    reg d = L.add-≅ {σ = L.suc} {σ′ = L.suc} (rq j) (Fix.pres d)
    coefficient : L.ψ⁰ (Tower.add p) ≼ L.ψ⁰ (right p)
    coefficient = Cut.sandwich {s = Src.pass (M.prefix j) Src.S.+ Src.S.↑ Src.B.zero
        (Src.S.ψ< {i = One.one} Src.B.zero Old.src-prefix)}
      (Dn.Dn-add {σ = L.suc} (A.Aligned.dn (prefix j)) (Dn.Dn-↑ Src.B.zero
        (Dn.Dn-ψ {i = One.one} (L.≅ᴵ-refl _) L.zero R.idσ Src.B.zero (A.Aligned.dn Old.prefix))))
      (U.M-add {σ = L.suc} (A.Aligned.up (prefix j)) (U.M-↑ Src.B.zero
        (U.M-ψ {i = One.one} (L.≅ᴵ-refl _) L.zero R.idσ Src.B.zero (Src.pass-up 1 (copies j)))))
      (reg {a = Coeff.p} (A.Aligned.regular Old.prefix)) (reg {a = p} (rq j))

    next : L.ψ⁰ (Tower.add p) ≼ v (L.suc j)
    next = ≼-trans {b = L.ψ⁰ (right p)} coefficient
      (≼-trans {b = L.ψ⁰ (p L.+ Ω₂ᴸ)} (≼l 1 (≼l 0 (≼l 1 (≼-refl _))))
        (≼-trans {b = Tail.Tail.row p (rq j)} (≼l 1 (≼-refl _))
          (≼-trans {b = L.ψ⁰ (p L.+ Coeff.p)} (Tail.Tail.lower p (rq j))
            (≼-trans {b = L.ψ⁰ (p L.+ q L.zero)} (Q.lead k p)
              (≼-trans {b = L.ψ⁰ (p L.+ p)}
                (Fix.value (Fix.map-select (λ a → L.ψ⁰ (p L.+ a)) (λ _ → refl) (select j)))
                (≼l 2 (≼-refl _)))))))

    module Clock = C.Clocks p (rq j)
    endpoint : ∀ x → x ≼ v j → C.run x (E.above (v j)) ≼ L.ψ⁰ (Tower.add p)
    endpoint x h = l≼ λ n → Clock.P.collect x h (E.steps (v j) n)
      (Clock.room (E.steps (v j) n) (Clock.H.point n))
    update : ∀ x → x ≼ v j → Stage.jump x ≼ v (L.suc j)
    update x h = ≼-trans {b = C.run x (E.above (v j))}
      (Stage.both {x} {x} {E.above x} {E.above (v j)} (≼-refl x) (K.advance {x} {v j} h))
      (≼-trans {b = L.ψ⁰ (Tower.add p)} (endpoint x h) next)

  module Start = Step L.zero
  omega : L.suc L.ωᶜ ≼ v 𝟏
  omega = ≼-trans {b = E.above (v L.zero)} (Start.Clock.H.finite {L.ωᶜ} Start.Clock.omega)
      (≼-trans {b = Stage.jump (v L.zero)} (Test.clock-below (v L.zero) (E.above (v L.zero)))
        (Start.update (v L.zero) (≼-refl _)))

  common : ∀ j → v (L.natᶜ j) ≼ v L.ωᶜ
  common j = M.monotone 0 {L.natᶜ j} {L.ωᶜ} (≼l j (≼-refl _))

  strict : L.suc (v L.ωᶜ) ≼ Row.iterate 0 2
  strict = ≼-trans {b = Stage.jump (v L.ωᶜ)} (Stage.rises (v L.ωᶜ))
    (≼-trans {b = v (L.suc L.ωᶜ)} (Step.update L.ωᶜ (v L.ωᶜ) (≼-refl _))
      (M.monotone 0 {L.suc L.ωᶜ} {v 𝟏} omega))

  in-next : Row.iterate 0 2 ≼ Q.recorded (suc k)
  in-next = ≼-trans {b = L.lim (λ j → Row.iterate 0 (suc j))} (≼l 1 (≼-refl _))
    (≼-trans {b = Row.node 0} (≅→≼ (L.≅-sym (Row.shape 0))) (R.at-below (Q.recorded (suc k)) 0))

  orbit : ∀ (f : ℕ → T₀) → f 0 ≼ Q.recorded k → (∀ j → f (suc j) ≼ Stage.jump (f j)) →
    L.lim f ≼ v L.ωᶜ
  orbit f h step = l≼ λ j → ≼-trans {b = v (L.natᶜ j)} (go j) (common j)
    where
    go : ∀ j → f j ≼ v (L.natᶜ j)
    go zero = h
    go (suc j) = ≼-trans {b = Stage.jump (f j)} (step j) (Step.update (L.natᶜ j) (f j) (go j))

  bound : ∀ z → z ≼ Q.recorded k → L.suc (Stage.hull z) ≼ Q.recorded (suc k)
  bound z h = ≼-trans {b = Row.iterate 0 2} (≼-trans {b = L.suc (v L.ωᶜ)}
    (s≼s (orbit (Stage.stages-from z) h (λ j → ≼-refl _))) strict) in-next

prefix-gap : ∀ k → L.suc (Stage.hull (Q.recorded k)) ≼ Q.recorded (suc k)
prefix-gap k = At.bound k (Q.recorded k) (≼-refl _)

ceiling : L.suc Stage.front ≼ Q.recorded 2
ceiling = At.bound 1 Seed.D Base.start

miss : Q.recorded 2 ≼ Stage.front → ⊥
miss h = s≼-irrefl Stage.front (≼-trans {b = Q.recorded 2} ceiling h)

miss-epsilon : E.above (Q.recorded 2) ≼ Stage.front → ⊥
miss-epsilon h = miss (≼-trans {b = E.above (Q.recorded 2)}
  (≼-trans {b = L.suc (Q.recorded 2)} (≼-suc (≼-refl _)) (E.strict (Q.recorded 2))) h)
```
