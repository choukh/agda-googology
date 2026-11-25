# 实际单位 (1,0) 的自槽与较低层询问给出上界

第四层，无条件。在该地址的首塔折叠内，只记录实际自槽和所有查询下降到后继层后的一层更低的单位询问（到零层取零层单位）。设这些值的上确界为 Q，完整单位落在 [Q, ε⁺(Q)]。[同一地址的两个严格下界](W4ReturnRendezvous.lagda.md#L92)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnCap where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import WVOne using (T₀; 𝟏; read; h₁)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
import OCF.Align.Level as L
open import OCF.Align.Value using (_≈ᵛ_; _≼_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; s≼s; z≼)
import B8FreezeMain as Add
import B12Terminal as T
import B12ActualSlots as Cov
import B14Tower as TW
import B14Height as Height
import B14PathHeight as Path
import B18Product as M
import B19PathValue as Scale
import B19IdealProduct as Law
import B19IdealPowers as Power
import B19IdealArithmetic as Ar
import B22HeightValue as HV
import B22MovingIndex as E
import B27UEpsilon as Hull
import B28BHead as Real
import B28BValues as Sum
import B31Front as Front
import B31Cost as Cost
import Survey.W4ReturnRendezvous as Goal

module At (s : T.Run (W.tw 1)) (standard : T.Run.ok s ≡ P.Ok-tw 1) (covered : Cov.Covered s) where
  r = TW.reset s (O.Ωt W.zero) (≼-refl 𝟏)
  module A = TW.At r
  d = read (proj₁ A.slot)
  x = λ j → read (A.idx j)
  u = λ j → read (T.value (A.point j))
  whole = read (T.value r)

  paths : ∀ z → Path.All (A.path z)
  paths z = help (T.Run.ok r) standard z
    where
    help : ∀ (o : P.Ok (W.tw 1)) → o ≡ P.Ok-tw 1 → ∀ y → Path.All (W.self W.∙ proj₂ (proj₁ o) y)
    help o refl y = Path.through (W.↑ W.zero y)

  feedback : ∀ j → x (suc j) ≈ᵛ (d M.· u j)
  feedback j = Scale.At.scale (h₁ z) (T.Run.ok t) (T.Run.bs t) (proj₁ (O.Ωt (h₁ z))) (paths z) A.slot
    where z = A.idx j; t = A.point j

  parts : ℕ → T₀
  parts zero = d
  parts (suc j) = Cost.cost (A.idx j) (A.point j)
  Q : T₀
  Q = L.lim parts
  module H = Hull.At Q
  here : ∀ j → parts j ≼ Q
  here j = ≼l {f = parts} j (≼-refl _)

  positive : 𝟏 ≼ Q
  positive = ≼-trans {b = d} (T.Run.oneB r (W.ink W.self)) (here 0)

  old : H.In d
  old = H.down {x = d} {y = Q} (here 0) H.seed
  module Bound (q : T₀) (one-q : 𝟏 ≼ q) (old-in : Hull.At.In q d)
               (cap : ∀ j → parts (suc j) ≼ q) where
    module Budget = Hull.At q
    ω-in : Budget.In L.ωᶜ
    ω-in = Budget.down {x = L.ωᶜ} {y = Ar.norm 𝟏} (M.one-left L.ωᶜ)
      (Budget.expC {x = 𝟏} (Budget.down {x = 𝟏} {y = q} one-q Budget.seed))
    width = Cost.width q
    width-in : Budget.In width
    width-in = Budget.mulC {x = q M.· L.ωᶜ} {y = L.ωᶜ} (Budget.mulC {x = q} {y = L.ωᶜ} Budget.seed ω-in) ω-in
    width-positive : 𝟏 ≼ width
    width-positive = ≼-trans {b = q} one-q (≼-trans {b = q M.· L.ωᶜ} (Cost.keep q) (Cost.keep (q M.· L.ωᶜ)))

    round : ∀ j → Budget.In (x j) → Budget.In (u j)
    round j h = Budget.down {x = u j} {y = size} (≼-trans {b = 𝟏 M.· size}
      (Front.Bound.run width width-positive (A.idx j) (A.point j) (Cost.cover q (A.idx j) (A.point j) (cap j)))
      (proj₁ (Law.left-one size))) (Budget.powC {x = width} {y = Ar.norm (x j)} width-positive width-in (Budget.expC {x = x j} h))
      where size = Law.power width (Ar.norm (x j))

    live : ∀ j → Budget.In (x j)
    live zero = Budget.down {x = L.zero} {y = q} z≼ Budget.seed
    live (suc j) = Budget.down {x = x (suc j)} {y = d M.· u j} (proj₁ (feedback j))
      (Budget.mulC {x = d} {y = u j} old-in (round j (live j)))

    sum-in : ∀ n → Budget.In (read (O.cum (λ j → T.value (A.point j)) n))
    sum-in zero = round 0 (live 0)
    sum-in (suc n) = Budget.down {x = read (O.cum raw (suc n))} {y = read (O.cum raw n) L.+ u (suc n)}
      (Add.read-+′ (O.cum raw n) (raw (suc n))) (Budget.sumC {x = read (O.cum raw n)} {y = u (suc n)}
        (sum-in n) (round (suc n) (live (suc n))))
      where raw = λ j → T.value (A.point j)

    upper : whole ≼ E.above q
    upper = subst (_≼ E.above q) (sym (Sum.Shape.law W.zero h₁ r)) (l≼ λ n →
      ≼-trans {b = L.suc (read (O.cum (λ j → T.value (A.point j)) n))} (≼-suc (≼-refl _)) (Budget.finite (sum-in n)))

  upper : whole ≼ E.above Q
  upper = Bound.upper Q positive old (λ j → here (suc j))

  queried : ∀ j → x j ≼ u j
  queried j = ≼-trans {b = Ar.norm (x j)} (Ar.up (x j)) (≼-trans {b = Ar.norm (Ar.norm (x j))}
    (Ar.up (Ar.norm (x j))) (≼-trans {b = 𝟏 M.· Ar.norm (Ar.norm (x j))} (M.one-left _)
      (≼-trans {b = Height.act (x j) 𝟏} (proj₂ (HV.exact (x j) 𝟏))
        (Height.law (A.idx j) (A.point j) (Cov.enter (W.sΩ W.zero) h₁ r (A.idx j) W.zero covered) 𝟏 (≼-refl _)))))

  lower : Q ≼ whole
  lower = l≼ λ
    { zero → ≼-trans {b = x 1}
        (T.inflate0 (h₁ W.zero) (T.Run.ok (A.chain W.zero)) (T.Run.bs (A.chain W.zero)) (A.path W.zero) A.slot (proj₁ (O.Ωt (h₁ W.zero))))
        (≼-trans {b = u 1} (queried 1) (A.out 1))
    ; (suc j) → ≼-trans {b = Front.front (A.idx j) (A.point j)} (Cost.inside (A.idx j) (A.point j))
        (≼-trans {b = u j} (Front.inside (A.idx j) (A.point j)) (A.out j)) }

module U = Real.At 0
module Actual = At (U.enter W.zero) refl (U.covered W.zero)

same : Actual.whole ≡ Goal.unit 1 0
same = U.real 0

upper : Goal.unit 1 0 ≼ E.above Actual.Q
upper = subst (_≼ E.above Actual.Q) same Actual.upper

lower : Actual.Q ≼ Goal.unit 1 0
lower = subst (Actual.Q ≼_) same Actual.lower
```
