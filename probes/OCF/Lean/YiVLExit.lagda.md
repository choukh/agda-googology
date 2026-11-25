# 实际孩子保持的零层义务与出口
验收文件；初项证书与实际整行出口归约已编译；Rows、FirstPreservation 未实填。
Rows 仅量化实际内链点，允许目标编号与链编号错位，不含全域保持律。
来源：YiIRTarget.initial-low、YiKCSem.sem→M⁰、YiOLMilestone 的 mL/m-cum 拼接；无新增强度。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVLExit where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiVLActual as V
import OCF.Lean.YiVLChild as C
import OCF.Lean.YiAZStart as A
import OCF.Lean.YiAZLocal as Z
import OCF.Lean.YiM2Local as M
import OCF.Lean.YiIRTarget as IR
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiHCCheck as HC
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_; ≼-trans)

At : ℕ → ℕ → Set
At n q = K.M⁰ (E.fsn (Z.S 2) n) (proj₁ (C.Child.collapse q))
Source : ℕ → ℕ → Set
Source n q = GR.R (C.Child.ℓ q) (E.fsT M.arg (M.γ n)) (proj₁ (O.Ωt (C.Child.ℓ q)))
Preservation : ℕ → ℕ → Set
Preservation n q = Source n q → At n q
Rows : Set
Rows = ∀ n → Σ ℕ λ q → Preservation n q
FirstPreservation : Set
FirstPreservation = Σ ℕ λ q → Preservation 1 q

zero-low : ∀ q (h : SI.E.HC (E.fsn (Z.S 2) 0)) → SI.E.tree h ≼ K.readRW (proj₁ (C.Child.collapse q))
zero-low q h = subst (λ x → SI.E.tree h ≼ K.readRW (proj₁ x)) (C.Child.row-eq q)
  (IR.initial-low (C.Child.d q) h)
zero : ∀ q → At 0 q
zero q = CS.sem→M⁰ (XI.back (M.hc-row 0)) (proj₁ (C.Child.collapse q))
  (≼-trans (SI.toL-tree (XI.back (M.hc-row 0))) (zero-low q (SI.conv (XI.back (M.hc-row 0)))))
zero-keep : ∀ q → Preservation 0 q
zero-keep q _ = zero q
first-source : ∀ q → Source 1 q
first-source q = C.Child.source q 1
first-hc : SI.E.HC (E.fsn (Z.S 2) 1)
first-hc = M.hc-row 1

-- perf: C-9，行证书先在可变目标编号和链编号上输运。
row : ∀ n q → Preservation n q → K.M⁰ (E.fsn (Z.S 2) n) (proj₁ (A.N.Inner.out (C.Child.d q)))
row n q keep = subst (λ x → K.M⁰ (E.fsn (Z.S 2) n) (proj₁ x)) (sym (C.Child.row-eq q))
  (keep (C.Child.source q n))
-- perf: S-1，最终关系证书不在下游反复展开实际折叠。
opaque
  assembled : Rows → K.M⁰ (Z.S 2) (proj₁ A.D.output)
  assembled rows = subst (λ x → K.M⁰ (Z.S 2) (proj₁ x)) (sym A.whole-row)
    (K.mL refl (λ n → K.G⁰.m-cum A.G (proj₁ (rows n))
      (row n (proj₁ (rows n)) (proj₂ (rows n)))))
keep-actual : Rows → V.KeepActual
keep-actual rows _ = HC.of⁰ (assembled rows) , HC.ex-of⁰ (assembled rows)
value : Rows → (h : SI.E.HC (Z.S 2)) → SI.E.tree h ≼ K.readRW (proj₁ A.D.output)
value rows h = ≼-trans (XI.tree-back h) (K.lower⁰ (assembled rows) (XI.back h))
```
