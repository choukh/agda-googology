# 原对象的 Ω 截段规格
验收文件；编译定理：槽位共尾型及 cut-row 输运回原 child-feed 的等式。
原名 kept 的同一性在二分定位与封装改写后仍遇 8G 堆墙，按本路停止条件停报。
不声称 BranchNeed 到 NextSlot 的接线或新的值下界；第 0 步分支对应未完成。
来源：YiKWObjects.cut-row/child-feed-eq；这里只作等式输运。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWYCut where
open import Data.List using ([])
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiC0Next as N
import OCF.Lean.YiC1Slot as S
import OCF.Lean.YiKWObjects as W
import OCF.Lean.YiBVRows as V
import OCF.Lean.YiRXOmegaHead as R
import OCF.Align.EboLeanDef as E
cof-slot : E.cof N.slot ≡ E.cΩ []
cof-slot = refl
original-row : S.cut S.path (proj₁ N.child-feed) ≡ B.Ω V.q1 W.branches
original-row = trans (cong (λ t → S.cut S.path (proj₁ t)) (sym W.child-feed-eq)) W.cut-row
```
