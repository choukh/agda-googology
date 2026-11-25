# 原 Offset 的逐前缀义务
不读记号；编译定理：首个前缀已覆盖；实际逐前缀 Cover 推出原 Offset 与第二链点比较。
ActualMissing 尚无居民；未填原 Offset、全链 Cover 或末端验收。
来源：YiOFLimit 的状态分解、YiTNLocal 的原出口；层号相等用 YiTNShape.first 消去。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOFLocal where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; trans)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTYLocal as Y
import OCF.Lean.YiTQChain as Q
import OCF.Lean.YiTNRow as R
import OCF.Lean.YiTNShift as S
import OCF.Lean.YiTNShape as H
import OCF.Lean.YiTNLocal as N
import OCF.Lean.YiTQSmall as Small
import OCF.Lean.YiOFLimit as L
seed : O.Tr⁺ B.zero
seed = O.Ωt B.zero
f : ℕ → B.Tr B.zero
f = O.iter (proj₁ seed O.+_) (proj₁ seed)
g h : ℕ → B.L
g n = T.source-child (f n)
h n = R.shift (f n)
og : P.Ok (B.nd B.sL g)
og = proj₂ (P.Ok-tw 1) Q.omega
wg : (n : ℕ) → P._≤_ B.zero (g n)
wg n = P.self P.∙ P.lift B.zero (B.↑ B.zero (f n))
wh : (n : ℕ) → P._≤_ B.zero (h n)
wh n = P.self P.∙ P.z≤ (h n)
Raw : (d : B.Tr B.zero) → P.Ok (R.shift d) → O.Tr⁺ B.zero
Raw d o = TB.ψ (R.shift d) o (MT.rbᶻ (R.shift d)) (F.B₀ (R.shift d)) B.zero
  (P.self P.∙ P.z≤ (R.shift d)) (O.Ωt B.zero) (proj₁ (O.Ωt (R.shift d)))
module At (oh : P.Ok (R.shift Q.omega)) where
  module A = L.Pair g h og oh wg wh
  opaque
    unfolding A.Source.output A.Source.fold Y.source-fold
    source-wire : proj₁ A.Source.output ≡ Y.source-fold Q.omega
    source-wire = refl
  opaque
    unfolding A.Target.output A.Target.fold
    target-wire : proj₁ A.Target.output ≡ proj₁
      (TB.ψ (R.shift Q.omega) oh (MT.rbᶻ (R.shift Q.omega)) (F.B₀ (R.shift Q.omega))
        B.zero (P.self P.∙ P.z≤ (R.shift Q.omega)) (O.Ωt B.zero)
        (proj₁ (O.Ωt (R.shift Q.omega))))
    target-wire = refl
  module Z = R.Actual B.zero
  opaque
    unfolding A.Source.piece A.Source.fold A.Source.prefix A.Source.part
      A.Target.piece A.Target.fold A.Target.prefix A.Target.part Small.low Small.high
    first : V.val B.zero (proj₁ (A.Source.piece 0)) V.≼
      V.val B.zero (proj₁ (A.Target.piece 0))
    first = V.≼-trans Small.one-two Z.A.predecessor-low
  first-cover : Σ ℕ λ m → V.val B.zero (proj₁ (A.Source.piece 0)) V.≼
    V.val B.zero (proj₁ (A.Target.piece m))
  first-cover = 0 , first
  Goal : Set
  Goal = V.val B.zero (Y.source-fold Q.omega) V.≼ V.val B.zero (proj₁ (Raw Q.omega oh))
  from-prefix : A.PrefixCover → Goal
  from-prefix p = subst₂ (λ x y → V.val B.zero x V.≼ V.val B.zero y)
    source-wire target-wire (A.from-prefix p)

PrefixAt : (d : B.Tr B.zero) → d ≡ Q.omega → P.Ok (R.shift d) → Set
PrefixAt .Q.omega refl o = At.A.PrefixCover o
from-at : (d : B.Tr B.zero) (e : d ≡ Q.omega) (o : P.Ok (R.shift d)) → PrefixAt d e o →
  V.val B.zero (Y.source-fold Q.omega) V.≼ V.val B.zero (proj₁ (Raw d o))
from-at .Q.omega refl o p = At.from-prefix o p
ActualMissing : Set
ActualMissing = PrefixAt (H.curve 0) H.first S.Actual.oc
from-actual : ActualMissing → N.Offset
from-actual p = from-at (H.curve 0) H.first S.Actual.oc p
second-from-prefix : ActualMissing → Y.Canonical.ChainAt 2 2
second-from-prefix p = N.second-from-offset (from-actual p)
advance-from-prefix : ActualMissing → Y.Canonical.ChainAdvance 1
advance-from-prefix p = N.advance-from-offset (from-actual p)
```
