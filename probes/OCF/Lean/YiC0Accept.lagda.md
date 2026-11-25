# 干净对象的第 0 项已实填
验收文件；编译定理：公共 FirstRow 成立，见证为 1，干净标准底输出不低于 ψ₀(Ω_Ω)。
本件不证明整个 ψ₀(Ω_{Ω₂}) 里程碑或其基本列第 1 项。
来源：YiC0Connect.neck-low 经 YiC0Reduce 的固定对象出口。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC0Accept where
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiC0Connect as C
import OCF.Lean.YiC0Reduce as R
open import OCF.Align.Value using (_≼_)
first-row : UL.FirstRow
first-row = R.first-row C.neck-low
witness : proj₁ first-row ≡ 1
witness = refl
first-value : (h : SI.E.HC (AL.S 1)) → SI.E.tree h ≼ K.readRW (proj₁ U.output)
first-value = R.first-value C.neck-low
```
