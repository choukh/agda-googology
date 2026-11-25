# 原 q=0 的两次原生折叠
验收文件；编译等式：原 q0 等于 tw2 上先更新底、再折一次 Ω 树，起始数据逐字为原 baseᴱ2、betaᴱ2。
没有给出独立记号上界，不判定 FirstMissing；Twice 只是原调用的展开式，没有修改原定义。
来源：直接展开 YiGIInst、YiTBRow 配 rbᶻ；保留所有目标层的底分量与原起点。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUDQ0Update where
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiRWFold as F

beta3-form : proj₁ (GI.betaᴱ 3) ≡ proj₁
  (TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (GI.baseᴱ 2)
    B.zero (P.z≤ (B.tw 2)) (GI.betaᴱ 2) (proj₁ (O.Ωt (B.tw 2))))
beta3-form = refl

base-zero-form : ∀ i (u : i P.≤ B.tw 2) →
  proj₁ (GI.baseᴱ 3 i (P.inc B.zero u)) ≡ proj₁
  (TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (GI.baseᴱ 2)
    i u (GI.baseᴱ 2 i u) (proj₁ (O.Ωt (B.tw 2))))
base-zero-form i u = refl

module Twice (A : F.Base (B.tw 2)) (β : O.Tr⁺ B.zero) where
  upd : F.Base (B.tw 2)
  upd i u = TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) A i u (A i u) (proj₁ (O.Ωt (B.tw 2)))
  first : O.Tr⁺ B.zero
  first = TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) A B.zero (P.z≤ (B.tw 2)) β (proj₁ (O.Ωt (B.tw 2)))
  second : O.Tr⁺ B.zero
  second = TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) upd B.zero (P.z≤ (B.tw 2)) first (proj₁ (O.Ωt (B.tw 2)))

q0-twice : proj₁ (FR.Step.out 2 (FR.Step.chain 2 0)) ≡
  proj₁ (Twice.second (GI.baseᴱ 2) (GI.betaᴱ 2))
q0-twice = refl
```
