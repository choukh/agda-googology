# 固定表的封装对象
验收文件；实际环境、起点、目标与全 HC 参照族已封装。
来源：YiE3Objects、YiLBStart.hc-target；入口见 YiE4Use。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Objects where
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiLBStart as LS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.EboLeanDef as E
import OCF.Align.Level as L
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Cut19 as C
-- perf: S-1，固定环境、起点与输出在出生处封装。
opaque
  ctx : Q.Ctx
  ctx = Q.make C.c₁
  ctx-eq : ctx ≡ Q.make C.c₁
  ctx-eq = refl
  β : O.Tr⁺ B.zero
  β = GI.betaᴱ 3
  β-eq : β ≡ GI.betaᴱ 3
  β-eq = refl
-- perf: S-1，构造与规格同封，调用点使用导出等式。
opaque
  output : O.Tr⁺ B.zero
  output = Q.collapse ctx β
  output-eq : output ≡ Q.collapse ctx β
  output-eq = refl
-- perf: S-1/S-3，目标与参照族封装，HC 对所有证书保留。
opaque
  target : E.T
  target = LS.target
  target-eq : target ≡ LS.target
  target-eq = refl
-- perf: S-1，构造与规格同封，调用点使用导出等式。
opaque
  hc : SI.E.HC target
  hc = subst SI.E.HC (sym target-eq) LS.hc-target
  reference : SI.E.HC target → L.Ordᶜ L.zero
  reference h = SI.E.tree h
  reference-eq : ∀ h → reference h ≡ SI.E.tree h
  reference-eq h = refl
```
