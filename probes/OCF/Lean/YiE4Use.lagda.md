# 固定表的唯一调用点
验收文件；条件定理 Use.first-at-one 接回原 FirstMissing，见证1。
困难值界未实填，量化保留所有 HC 证书；入口见 YiE4Default。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Use where
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiLBStart as LS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Frame as V
import OCF.Lean.YiE4Cut19 as C
open import OCF.Align.Value using (_≼_; ≼-trans)
-- perf: C-9，先检查任意孩子的原计算律，不展开固定链点。
collapse-wire : ∀ c → Q.collapse (Q.make c) (GI.betaᴱ 3) ≡ FR.Step.out 2 c
collapse-wire c = trans
  (Q.collapse-eq (FR.Step.child 2 c) (proj₂ (P.Ok-tw 3) c) (MT.rbᶻ (FR.Step.child 2 c))
    (λ i u → GI.baseᴱ 3 i (P.inc c u)) (GI.betaᴱ 3)) refl
-- perf: S-1，接回旧 FirstMissing 的具体输出只在本调用点出现。
opaque
  output-actual : A.output ≡ FR.Step.out 2 (FR.Step.chain 2 1)
  output-actual = trans A.output-eq (trans (cong₂ Q.collapse A.ctx-eq A.β-eq)
    (trans (collapse-wire C.c₁) (cong (FR.Step.out 2) C.c₁-actual)))
Missing : Set
Missing = (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse A.ctx A.β))

module Use (low : Missing) where
  -- perf: C-9，层号、合法性、表和底由同一个规范环境给出，Σ 的 η 不展开折叠。
  module Inst = V.Frame C.c₁ refl (Q.level A.ctx) (Q.okay A.ctx) (Q.table A.ctx) (Q.base A.ctx)
    A.ctx-eq A.β refl low
  target-low : (e : SI.E.HC LS.target) → SI.E.tree e ≼ K.readRW (proj₁ A.output)
  target-low e = ≼-trans (FR.tree-transport (sym A.target-eq) e)
    (Inst.raw-low (subst SI.E.HC (sym A.target-eq) e))
  first-at-one : FR.FirstMissing
  first-at-one = V.at-one LS.target (λ q → FR.Step.out 2 (FR.Step.chain 2 q)) A.output output-actual target-low
```
