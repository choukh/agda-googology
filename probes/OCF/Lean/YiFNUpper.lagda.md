# 实际链点的界与第 0 点的下界
验收文件；编译定理：每个实际输出严格低于实际第 3 支，第 0 点严格高于实际第 2 支。
第 2 支作第 0 点上界的候选被否定；没有得到各输出的独立记号上界，FirstMissing 未判定。
来源：实际展开照 YiTBRow；弱上界复用 YiFRStep.branch-upper，严格界复用 YiKDStep.◃s≼、YiKSDesc.cumᴿ 与两读回桥。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFNUpper where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as T
import OCF.Lean.YiMTTab as M
import OCF.Lean.YiFRStep as S
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKQSuff as Q
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiKDStep as KD
import OCF.Lean.YiKSDesc as DS
import OCF.Lean.YiNFO as NF
import OCF.Align.Level as L
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ; baseᴱ; betaᴱ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
open import OCF.Align.Value using (_≼_; ≼-trans; s≼s; ≼-refl; ≼l)

childBase : F.Base (B.tw 2)
childBase i u = baseᴱ 3 i (P.inc B.zero u)

beta3 : betaᴱ 3 ≡ (Keel⁻.twc keelᴱ 2 , proj₂ (betaᴱ 3))
beta3 = refl

out0 : S.Step.out 2 (S.Step.chain 2 0) ≡
  T.ψ (B.tw 2) (P.Ok-tw 2) (M.rbᶻ (B.tw 2)) childBase B.zero
    (P.z≤ (B.tw 2)) (betaᴱ 3) (proj₁ (O.Ωt (B.tw 2)))
out0 = refl

branch-form : Keel⁻.twc keelᴱ 3 ≡
  proj₁ (O.limc⁺ (λ q → S.Step.out 2 (S.Step.chain 2 q)))
branch-form = refl

upper0 : K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 0))) ≼ K.readRW (Keel⁻.twc keelᴱ 3)
upper0 = S.Step.branch-upper 2 0
upper1 : K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 1))) ≼ K.readRW (Keel⁻.twc keelᴱ 3)
upper1 = S.Step.branch-upper 2 1
upper2 : K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 2))) ≼ K.readRW (Keel⁻.twc keelᴱ 3)
upper2 = S.Step.branch-upper 2 2

prior-strict : L.suc (K.readRW (Keel⁻.twc keelᴱ 2))
  ≼ K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 0)))
prior-strict = ≼-trans (s≼s (Q.read≤ (Keel⁻.twc keelᴱ 2)))
  (≼-trans (KD.◃s≼ (T.mono (B.tw 3) (P.Ok-tw 3) (M.rbᶻ (B.tw 3)) (baseᴱ 3)
    B.zero (P.z≤ (B.tw 3)) (betaᴱ 3)
    (B.◃u B.zero B.zero (proj₁ (O.Ωt (B.tw 2))) (proj₂ (O.Ωt (B.tw 2))))))
    (CS.rr≼ (proj₁ (S.Step.out 2 (S.Step.chain 2 0)))))

not-prior-upper : K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 0)))
  ≼ K.readRW (Keel⁻.twc keelᴱ 2) → ⊥
not-prior-upper q = NF.s≼-irrefl (K.readRW (Keel⁻.twc keelᴱ 2)) (≼-trans prior-strict q)

Fq : ℕ → O.Tr⁺ B.zero
Fq q = S.Step.out 2 (S.Step.chain 2 q)

strict-upper : ∀ q → L.suc (K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 q))))
  ≼ K.readRW (Keel⁻.twc keelᴱ 3)
strict-upper q = ≼-trans (s≼s (Q.read≤ (proj₁ (Fq q))))
  (≼-trans (s≼s (DS.cumᴿ Fq q (≼-refl _)))
  (≼-trans (KD.◃s≼ (O.+-mono (O.cum (λ i → proj₁ (Fq i)) q) (proj₂ (Fq (suc q)))))
  (≼-trans (CS.rr≼ (O.cum (λ i → proj₁ (Fq i)) (suc q))) (≼l (suc q) (≼-refl _)))))
```
