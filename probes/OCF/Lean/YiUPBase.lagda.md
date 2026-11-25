# 原第 1 链点的限制底
验收文件；固定原 Step 2 的 q=1，限制底逐字是 Ω 树加三个标准零层折叠的嵌入。
不提供这三个闭项或 betaᴱ 3 的独立记号上界，不判定 FirstMissing。
来源：PA 后到纸面诊断的具体式；此处按 YiTBRow/YiMTTab 独立展开，未改原底或起点。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUPBase where
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiFRStep as FR

δ : ℕ → B.Tr B.zero
δ n = MT.twᶻ n
c₁ = FR.Step.chain 2 1
base-form : ∀ i (u : i P.≤ FR.Step.child 2 c₁) →
  proj₁ (GI.baseᴱ 3 i (P.inc c₁ u)) ≡
  (((proj₁ (O.Ωt i) O.+ O.ι i (δ 0)) O.+ O.ι i (δ 1)) O.+ O.ι i (δ 2))
base-form i u = refl
```
