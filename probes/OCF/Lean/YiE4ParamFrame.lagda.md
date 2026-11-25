# 比较表参数下的变量框架
验收文件；For.Frame 与规范调用点对整张表参数化，困难值界未填。
来源：YiE4Frame；FirstAt 为该表下固定目标的存在链点结论；入口见 YiE4Default。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4ParamFrame where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiLBStart as LS
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Frame as V
import OCF.Lean.YiE4Param as R
open import OCF.Align.Value using (_≼_; ≼-trans)
module For (r : TB.Rb B.Λ) where
  module D = R.At r
  -- perf: C-9，实际对象约束均依赖参数 r，不引入固定的孩子表。
  module Frame (c : B.Tr (B.tw 2)) (c-eq : c ≡ D.c₁)
    (h : B.L) (o : P.Ok h) (rr : TB.Rb h) (bs : F.Base h)
    (env-eq : (h , o , rr , bs) ≡ D.make c)
    (β : O.Tr⁺ B.zero) (β-eq : β ≡ D.β)
    (low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse (h , o , rr , bs) β))) where
    context-eq : (h , o , rr , bs) ≡ D.ctx
    context-eq = trans env-eq (trans (cong D.make c-eq) (sym D.ctx-eq))
    sealed-low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ D.output)
    sealed-low e = subst (λ x → A.reference e ≼ K.readRW (proj₁ x))
      (trans (cong₂ Q.collapse context-eq β-eq) (sym D.output-eq)) (low e)
    raw-low : (e : SI.E.HC A.target) → SI.E.tree e ≼ K.readRW (proj₁ D.output)
    raw-low e = subst (λ x → x ≼ K.readRW (proj₁ D.output)) (A.reference-eq e) (sealed-low e)
  -- perf: C-24，接线先在孩子变量上证明，复用出生处的 out-child。
  opaque
    unfolding Q.collapse D.restricted
    collapse-wire : ∀ c → Q.collapse (D.make c) (D.betaᴱ 3) ≡ D.Step.out 2 c
    collapse-wire c = sym (D.Step.out-child 2 c)
  -- perf: S-1，构造与规格同封，调用点使用导出等式。
  opaque
    output-chain : D.output ≡ D.Step.out 2 (D.Step.chain 2 1)
    output-chain = trans D.output-eq (trans (cong₂ Q.collapse D.ctx-eq D.β-eq)
      (trans (collapse-wire D.c₁) (cong (D.Step.out 2) D.c₁-eq)))
  Missing : Set
  Missing = (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β))
  FirstAt : Set
  FirstAt = Σ ℕ λ q → (e : SI.E.HC LS.target) → SI.E.tree e ≼ K.readRW (proj₁ (D.Step.out 2 (D.Step.chain 2 q)))
  module Use (low : Missing) where
    -- perf: C-9，唯一规范实例，所有环境等式由定义规格实填。
    module Inst = Frame D.c₁ refl (Q.level D.ctx) (Q.okay D.ctx) (Q.table D.ctx) (Q.base D.ctx) D.ctx-eq D.β refl low
    target-low : (e : SI.E.HC LS.target) → SI.E.tree e ≼ K.readRW (proj₁ D.output)
    target-low e = ≼-trans (FR.tree-transport (sym A.target-eq) e)
      (Inst.raw-low (subst SI.E.HC (sym A.target-eq) e))
    first-at-one : FirstAt
    first-at-one = V.at-one LS.target (λ q → D.Step.out 2 (D.Step.chain 2 q)) D.output output-chain target-low
```
