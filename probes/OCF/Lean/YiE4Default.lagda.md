# 原比较表的接线与固定缺口
验收文件；默认表处接回原 FirstMissing，条件是固定q1、全HC的原值界。
from-original/to-original 双向转换原值界与封装参数；值界未填，不增加强度。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Default where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiLBStart as LS
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Param as R
import OCF.Lean.YiE4ParamFrame as V
import OCF.Lean.YiE4Frame as W
open import OCF.Align.Value using (_≼_)
module D = R.At (MT.rbᶻ B.Λ)
module U = V.For (MT.rbᶻ B.Λ)
-- perf: C-24，旧定义接线在变量 n、c 上一次检查；不比较两条具体递推。
opaque
  unfolding D.FΛ D.pre D.baseᴱ D.betaᴱ D.Step.g D.Step.feed D.Step.out
  pre-eq : ∀ n → D.pre n ≡ GI.pre n
  pre-eq zero = refl
  pre-eq (suc n) = refl
  base-eq : ∀ n → D.baseᴱ n ≡ GI.baseᴱ n
  base-eq n = cong (λ x → λ i u → TB.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) i (P.inc n u) (O.Ωt i) x) (pre-eq n)
  beta-eq : ∀ n → D.betaᴱ n ≡ GI.betaᴱ n
  beta-eq n = cong (λ x → TB.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) x) (pre-eq n)
  g-eq : ∀ n → D.Step.g n ≡ FR.Step.g n
  g-eq n = refl
  feed-eq : ∀ n → D.Step.feed n ≡ FR.Step.feed n
  feed-eq n = refl
  out-eq : ∀ n → D.Step.out n ≡ FR.Step.out n
  out-eq n = refl
chain-eq : ∀ n q → D.Step.chain n q ≡ FR.Step.chain n q
chain-eq n q = cong (λ f → O.iter f B.zero q) (feed-eq n)
-- perf: S-1，旧目标接回仅在这个封装调用点；困难参数保持全 HC、固定 q1。
opaque
  output-old : D.output ≡ FR.Step.out 2 (FR.Step.chain 2 1)
  output-old = trans U.output-chain (trans (cong (λ f → f (D.Step.chain 2 1)) (out-eq 2))
    (cong (FR.Step.out 2) (chain-eq 2 1)))
module Use (low : U.Missing) where
  module Inst = U.Use low
  first-at-one : FR.FirstMissing
  -- perf: C-9，出口用变量 at-one，不在闭输出上展开读回。
  first-at-one = W.at-one LS.target (λ q → FR.Step.out 2 (FR.Step.chain 2 q)) D.output output-old Inst.target-low

-- perf: C-9，等式输运先对目标与输出变量证明，所有 HC 证书均保留。
Bound : E.T → O.Tr⁺ B.zero → Set
Bound t x = (h : SI.E.HC t) → SI.E.tree h ≼ K.readRW (proj₁ x)
move-bound : ∀ {s t u v} → s ≡ t → u ≡ v → Bound s u → Bound t v
move-bound refl refl p = p
OriginalAtOne : Set
OriginalAtOne = Bound LS.target (FR.Step.out 2 (FR.Step.chain 2 1))
from-original : OriginalAtOne → U.Missing
from-original low h = subst (λ x → x ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β)))
  (sym (A.reference-eq h))
  (move-bound (sym A.target-eq) (trans (sym output-old) D.output-eq) low h)
to-original : U.Missing → OriginalAtOne
to-original low = move-bound A.target-eq (trans (sym D.output-eq) output-old)
  (λ h → subst (λ x → x ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β))) (A.reference-eq h) (low h))
module FromOriginal (low : OriginalAtOne) where
  module Inst = Use (from-original low)
  first-at-one : FR.FirstMissing
  first-at-one = Inst.first-at-one
```
