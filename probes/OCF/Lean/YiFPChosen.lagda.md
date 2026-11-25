# 实际有限孩子上的移植验收
验收文件；编译定理：chosen 的孩子层号为 4，移植主引理给出原输出的 M 1 关系。
chosen-MS 经新 St/J/MS/lower；chosen-old 单独调用旧 sΩ-LF，陈述逐字相同，不比较证明项。
底前提 chosen-premise 无条件实填；不声称一般 Need 或 MinimalGoal。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFPChosen where
open import OCF.Lean.YiFPFinite
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCLFam using (fn; M; Mβ)
open import OCF.Lean.YiCLLow using (s0; ss)
open import OCF.Lean.YiRBFam using (can; pu; pt; tu; OKB)
open import OCF.Lean.YiKVRel using (⊴r)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
import OCF.Lean.YiTBFam as Old
import OCF.Lean.YiBVSmall as Small
import OCF.Lean.YiBVDomain as Domain
chosen : Tr zero
chosen = suc zero
chosen-path : pt {n = 4} {j = 1} (pu (pu (can (ss s0)))) ≡ Small.lower chosen
chosen-path = refl
chosen-premise : OKB (Small.Small.child-base chosen)
chosen-premise i u = ⊴r
chosen-MS : M 1 (ψᴺ 1 (Ωᴺ 4)) (proj₁ (Small.Small.child-out chosen))
chosen-MS = lower {n = 3} {j = 1} (proj₂ Small.okay chosen , proj₂ (Domain.Input.table Small.minimal) chosen , Small.Small.child-base chosen)
  (tu (pu (can (ss s0)))) (Ωt (fn 1)) chosen-premise (Mβ 0)

chosen-old : M 1 (ψᴺ 1 (Ωᴺ 4)) (proj₁ (Small.Small.child-out chosen))
chosen-old = Old.sΩ-LF {n = 3} {j = 1} (proj₂ Small.okay chosen)
  (proj₂ (Domain.Input.table Small.minimal) chosen) (tu (pu (can (ss s0))))
  (Small.Small.child-base chosen) (Ωt (fn 1)) chosen-premise (Mβ 0)
```
