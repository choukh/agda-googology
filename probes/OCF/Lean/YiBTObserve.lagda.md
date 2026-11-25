# 第 1 项零分支的有限观察
验收文件；首孩子的头为 ℕ 极限，因此实际分支不等于 next⁺(Ωt one) 的字面树。
这是形状测试与字面否定，不是序数值否定；不否定第 1 项下界。
来源：YiC1Slot 的截段工具；实际分支为 YiBTOne.branch。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBTObserve where
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import OCF.Lean.YiBTOne as N
import OCF.Lean.YiBTLocal as C
import OCF.Lean.YiBSClean as U
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiC1Slot as Cut
observe : B.Tr U.one → Cut.Head
observe x = Cut.head (Cut.cut (0 ∷ []) x)
opaque
  unfolding N.branch N.kept N.child-feed C.c₁ U.Inner.feed U.Inner.g
  first-head : observe (N.branch B.zero) ≡ Cut.hl
  first-head = refl
simple-first-head : observe (proj₁ (O.next⁺ (O.Ωt U.one))) ≡ Cut.hΩ
simple-first-head = refl
not-simple : N.branch B.zero ≡ proj₁ (O.next⁺ (O.Ωt U.one)) → ⊥
not-simple e with trans (sym first-head) (trans (cong observe e) simple-first-head)
... | ()
```
