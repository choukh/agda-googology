# 第 3 站实际链的最小检查
验收文件；编译等式记录实际 chain 2 的第 0、1 点和输出，目标 HC 为闭项。
比较对 Pair、Pair2 固定原 FirstMissing 的 q=1、2；未填支配，不增加强度，不否定其他 q。
来源：YiFRStep.Step 逐条展开；HC 复用 YiGIEnd.hs、YiExInst.back 与 YiRefTw2.hω-inv。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMSShape where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
import OCF.Lean.YiFRStep as S
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiGIInst using (baseᴱ; betaᴱ; gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiGIEnd using (hs)
open import OCF.Lean.YiExInst using (back)
open import Data.List using ([]; _∷_)
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiRefTw2 using (hω-inv)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
k = B.tw 2
ell = B.tw 3
child = S.Step.child 2
CB : (c : B.Tr k) → F.Base (child c)
CB c i u = baseᴱ 3 i (P.inc c u)
CF : (c : B.Tr k) (j : B.L) → j P.≤ child c → O.Tr⁺ j → O.Tr⁺ j
CF c j w β = TB.ψ (child c) (proj₂ (P.Ok-tw 3) c) (proj₂ (MT.rbᶻ ell) c) (CB c) j w β (proj₁ (O.Ωt (child c)))
chain0 : S.Step.chain 2 0 ≡ B.zero
chain0 = refl
chain1 : S.Step.chain 2 1 ≡ proj₁ (CF B.zero k P.self (baseᴱ 3 k (P.ink P.self)))
chain1 = refl
feed-form : ∀ c → S.Step.feed 2 c ≡ proj₁ (CF c k (P.self P.∙ P.lift k (B.↑ k c)) (baseᴱ 3 k (P.ink P.self)))
feed-form c = refl
out-form : ∀ c → S.Step.out 2 c ≡ CF c B.zero (P.z≤ (child c)) (betaᴱ 3)
out-form c = refl
out0 : S.Step.out 2 (S.Step.chain 2 0) ≡ CF B.zero B.zero (P.z≤ k) (betaᴱ 3)
out0 = refl
out1 : S.Step.out 2 (S.Step.chain 2 1) ≡ CF (proj₁ (CF B.zero k P.self (baseᴱ 3 k (P.ink P.self)))) B.zero (P.z≤ (child (S.Step.chain 2 1))) (betaᴱ 3)
out1 = refl
opaque
  target-hc : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1)
  target-hc = SI.conv (hω-inv (back (hs 3)) (S.rowω 2) 1)
Pair : Set
Pair = (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1)) → SI.E.tree h ≼ K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 1)))
output0-nz : B._⊢_◃_ B.zero B.zero (proj₁ (S.Step.out 2 (S.Step.chain 2 0)))
output0-nz = proj₂ (S.Step.out 2 (S.Step.chain 2 0))
output1-nz : B._⊢_◃_ B.zero B.zero (proj₁ (S.Step.out 2 (S.Step.chain 2 1)))
output1-nz = proj₂ (S.Step.out 2 (S.Step.chain 2 1))

target-form : E.fsn (Keel⁻.row keelᴱ 3) 1 ≡ E.ψ [] (E.Ωt (E.Ωt (E.EBOψ 2))) ∷ []
target-form = refl

chain1-root : S.Step.chain 2 1 ≡ B.Ω (inj₁ (inj₁ tt))
  (λ c → proj₁ (O.Up (S.Step.child 1 c) (O.down O.stop c)
    (baseᴱ 3 k (P.ink P.self)) (proj₁ (O.Ωt (S.Step.child 1 c)))))
chain1-root = refl
chain2-form : S.Step.chain 2 2 ≡ proj₁ (CF (S.Step.chain 2 1) k
  (P.self P.∙ P.lift k (B.↑ k (S.Step.chain 2 1))) (baseᴱ 3 k (P.ink P.self)))
chain2-form = feed-form (S.Step.chain 2 1)

Pair2 : Set
Pair2 = (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → SI.E.tree h ≼ K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 2)))
```
