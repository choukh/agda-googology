# 比较表参数框架的规范前提
验收文件；除作者允许保留的困难值界外，环境、等式与HC前提均有规范实例。
实例对任意r成立，另列原表与空表；不声称困难值界可满足或已实填。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Instances where
open import Data.Nat using (suc)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Param as R
module Canonical (r : TB.Rb B.Λ) where
  module D = R.At r
  environment : (Q.level D.ctx , Q.okay D.ctx , Q.table D.ctx , Q.base D.ctx) ≡ D.make D.c₁
  environment = D.ctx-eq
  chain : D.c₁ ≡ D.c₁
  chain = refl
  beta : D.β ≡ D.β
  beta = refl
  hc : SI.E.HC A.target
  hc = A.hc
  child-table : ∀ n c → D.Step.child-table n c ≡ proj₂ (proj₂ r (suc n)) c
  child-table n c = refl
module Original = Canonical (MT.rbᶻ B.Λ)
module Empty = Canonical (TB.rb-no B.Λ)
```
