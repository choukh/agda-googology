# 实际链点的文献参数关系
验收文件；ActualInv 含 NF/G 与原链点、原 g 的非零层 R；一步保持为编译定理。
它不包含零层输出的值支配，不推出 FirstMissing；值不变量见 YiLBInv。
来源：γ 的界取 EboLeanView.γ<，NF/G 取 tow；树侧接线复用 YiNLTop2/YiNLRaise。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLBActual where
open import OCF.Lean.YiLBStart
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanView as V
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiNLTop2 as N
import OCF.Lean.YiNLRaise as NR
open import OCF.Lean.YiNLCtx using (prefix)
open import OCF.Lean.YiLLCheck using (rdΩ)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiGTGen using (weakenᴿ)
open import OCF.Align.EboLeanBase using (NF; GB)

rd-gamma : ∀ q → GR.Rd (B.tw 2) (V.γ w q)
rd-gamma q = GR.cc (inj₁ (V.γ< w q)) (GR.rd-child (B.sΩ (B.tw 1)) (FR.Step.child 1) B.zero rdΩ)
leaf-gamma : ∀ q → GR.R (B.tw 2) (E.Ωt (V.γ w q)) (proj₁ (O.Ωt (B.tw 2)))
leaf-gamma q = N.leaf-tw2 (rd-gamma q)

slot-gamma : ∀ q → GR.R (B.tw 2) (E.Ωt (V.γ w q)) (proj₁ (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)))
slot-gamma q = weakenᴿ (B.tw 2) (leaf-gamma q)
  (ψ-⊵ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) (B.tw 2) (P.inc 3 (P.ink P.self)) (O.Ωt (B.tw 2)) (GI.pre 3))

chain-gamma : ∀ q r → GR.R (B.tw 2) (E.Ωt (V.γ w r)) (FR.Step.chain 2 (suc q))
chain-gamma q r = weakenᴿ (B.tw 2) (slot-gamma r)
  (ψ-⊵ (B.tw 3) (P.Ok-tw 3) (MT.rbᶻ (B.tw 3)) (GI.baseᴱ 3)
    (B.tw 2) (P.ink P.self) (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)) (FR.Step.g 2 (FR.Step.chain 2 q)))

child-gamma : ∀ q r → GR.R (FR.Step.child 2 (FR.Step.chain 2 (suc q)))
  (V.fΩ w (V.γ w r)) (proj₁ (O.Ωt (FR.Step.child 2 (FR.Step.chain 2 (suc q)))))
child-gamma q r = NR.raiseR (B.tw 2) (prefix (B.tw 2)) [] (GR.c0 refl)
  (N.leaf-tw2 (GR.c0 refl)) (chain-gamma q r)

g-gamma : ∀ q r → GR.R (B.tw 3) (V.fΩ w (V.γ w r)) (FR.Step.g 2 (FR.Step.chain 2 (suc q)))
g-gamma q r = H.mU H.mz (child-gamma q r)

out-child : ∀ q → FR.Step.out 2 (FR.Step.chain 2 q)
  ≡ TB.ψ (FR.Step.child 2 (FR.Step.chain 2 q))
    (proj₂ (P.Ok-tw 3) (FR.Step.chain 2 q)) (MT.rbᶻ (FR.Step.child 2 (FR.Step.chain 2 q)))
    (λ i u → GI.baseᴱ 3 i (P.inc (FR.Step.chain 2 q) u))
    B.zero (P.z≤ (FR.Step.child 2 (FR.Step.chain 2 q))) (GI.betaᴱ 3)
    (proj₁ (O.Ωt (FR.Step.child 2 (FR.Step.chain 2 q))))
out-child q = refl

ActualInv : ℕ → Set
ActualInv q = NF (V.γ w q) × GB [] (V.γ w q) (V.fΩ w (V.γ w q))
  × GR.R (B.tw 2) (E.Ωt (V.γ w q)) (FR.Step.chain 2 (suc q))
  × GR.R (B.tw 3) (V.fΩ w (V.γ w q)) (FR.Step.g 2 (FR.Step.chain 2 (suc q)))

actual : ∀ q → ActualInv q
actual q = proj₁ (gamma-NF-G q) , proj₂ (gamma-NF-G q) , chain-gamma q q , g-gamma q q

actual-step : ∀ q → ActualInv q → ActualInv (suc q)
actual-step q _ = actual (suc q)
```
