# 新表固定 q1 的最小检查
验收文件；表取 YiCWTable.rbΛ，复用 YiE4 整表参数框架。
编译目标前两项展开、闭 HC 与完整内层整行接线；没有逐项值支配。
来源：YiE4ParamFrame、YiE4ParamInner；HC 复用 YiRefTw2.hω-inv。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiATStart where
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiLBStart as LS
import OCF.Lean.YiCWTable as CW
import OCF.Lean.YiE4Param as R
import OCF.Lean.YiE4ParamFrame as V
import OCF.Lean.YiE4ParamInner as J
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Align.Value using (_≼_)
module D = R.At CW.rbΛ
module U = V.For CW.rbΛ
module I = J.At CW.rbΛ
Missing-check : U.Missing ≡ ((h : SI.E.HC A.target) → A.reference h ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β)))
Missing-check = refl
output-wire : D.output ≡ D.Step.out 2 (D.Step.chain 2 1)
output-wire = U.output-chain
first-row : D.output ≡ O.limc⁺ (λ n → I.Inner.out (I.Inner.chain n))
first-row = I.first-row
ρ : E.T → E.T
ρ x = E.ψ [] (E.Ωt x) ∷ []
T₀ : E.fsn LS.target 0 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (E.natT 1)))) ∷ []
T₀ = refl
T₁ : E.fsn LS.target 1 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (ρ (E.natT 1))))) ∷ []
T₁ = refl
inner0 : I.Inner.chain 0 ≡ B.zero
inner0 = refl
inner1 : I.Inner.chain 1 ≡ I.Inner.feed B.zero
inner1 = refl

import OCF.Lean.YiExInst as XI
import OCF.Lean.YiRefTw2 as RT
opaque
  hc₀ : SI.E.HC (E.fsn LS.target 0)
  hc₀ = SI.conv (RT.hω-inv (XI.back LS.hc-target) refl 0)
  hc₁ : SI.E.HC (E.fsn LS.target 1)
  hc₁ = SI.conv (RT.hω-inv (XI.back LS.hc-target) refl 1)
```
