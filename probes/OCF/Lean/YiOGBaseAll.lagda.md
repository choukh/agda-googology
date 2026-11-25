# 实际第 1 前缀的全部底路径
不读记号；编译定理：BaseTransferOne 的全部非 self 路径已实填。
来源：YiOGRelPeel 的两次出口；实际更新依 YiOFLimit 展开，保留 inc/inu。
不把这个单前缀定理当作全部前缀保持；值出口见 YiOGFirst。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGBaseAll where
open import Data.Unit using (⊤; tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiVRRel as R
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiTNShape as H
import OCF.Lean.YiOGState as S
import OCF.Lean.YiOGFold as Fold
import OCF.Lean.YiOGTransfer as X
import OCF.Lean.YiOGRelPeel as RP
import OCF.Lean.YiVRFold as VF
one = C.g 0
three = C.h 0
left : (i : B.L) → P._≤_ i one → O.Tr⁺ i
left i v = Fold.ψ one (proj₂ C.og 0) (F.B₀ one) i v (O.Ωt i) (proj₁ (O.Ωt one))
right : (i : B.L) → P._≤_ i one → O.Tr⁺ i
right i v = Fold.ψ one (proj₂ (proj₂ (proj₂ S.oh 0) tt) tt) (F.B₀ one) i v (O.Ωt i) (proj₁ (O.Ωt one))
low-related : (i : B.L) (v : P._≤_ i one) → R.Le i (proj₁ (left i v)) (proj₁ (right i v))
low-related .one P.self = Fold.fl one tt (proj₂ C.og 0) (F.B₀ one) (F.B₀ one) (VF.B₀⊴-noΩ one tt)
  one P.self (O.Ωt one) (O.Ωt one) (R.Ωt≼ one tt) (R.Ωt≼ one tt)
low-related .B.zero (P.inc tt P.self) = R.refl₀ _
low-related i (P.inu vs) with vs tt
... | P.self = R.refl₀ _

module Lift (i : B.L) (u : P._≤_ i (C.g 1)) (v : P._≤_ i one) where
  module A₂ = RP.At one tt (proj₂ (proj₂ S.oh 0) tt) (F.B₀ (C.g 1)) i v (O.Ωt i)
  module A₃ = RP.At (C.g 1) tt (proj₂ S.oh 0) (F.B₀ three) i u (O.Ωt i)
  advance : proj₁ A₂.high ≡ proj₁ A₃.low → R.Le i (proj₁ (left i v)) (proj₁ A₃.high)
  advance e = A₃.peel-from
    (subst (λ y → R.Le i (proj₁ (left i v)) y) e (A₂.peel-from (low-related i v) (B.◃t (B.◃l 0) B.◃s)))
    (B.◃t (B.◃l 0) B.◃s)

opaque
  unfolding S.G.base-at S.G.previous S.G.prefix S.G.part
  source-inc-form : (i : B.L) (v : P._≤_ i one) → X.source-base i (P.inc tt v) ≡ left i v
  source-inc-form i v = refl
  source-inu-form : (i : B.L) (vs : ⊤ → P._≤_ i one) → X.source-base i (P.inu vs) ≡ left i (vs tt)
  source-inu-form i vs = refl
opaque
  unfolding S.T.base-at S.T.previous S.T.prefix S.T.part H.first H.curve H.line
  target-inc-form : (i : B.L) (v : P._≤_ i one) → X.target-base i (P.inc tt v) ≡
    Fold.ψ three (proj₂ S.oh 0) (F.B₀ three) i (P.inc tt (P.inc tt v)) (O.Ωt i) (proj₁ (O.Ωt three))
  target-inc-form i v = refl
  target-inu-form : (i : B.L) (vs : ⊤ → P._≤_ i one) → X.target-base i (P.inu vs) ≡
    Fold.ψ three (proj₂ S.oh 0) (F.B₀ three) i (P.inc tt (P.inu vs)) (O.Ωt i) (proj₁ (O.Ωt three))
  target-inu-form i vs = refl

base-transfer-one : X.BaseTransferOne
base-transfer-one i P.self ()
base-transfer-one i (P.inc tt v) pr = subst₂ (λ x y → R.Le i (proj₁ x) (proj₁ y))
  (sym (source-inc-form i v)) (sym (target-inc-form i v)) (Lift.advance i (P.inc tt v) v refl)
base-transfer-one i (P.inu vs) pr = subst₂ (λ x y → R.Le i (proj₁ x) (proj₁ y))
  (sym (source-inu-form i vs)) (sym (target-inu-form i vs)) (Lift.advance i (P.inu vs) (vs tt) refl)
```
