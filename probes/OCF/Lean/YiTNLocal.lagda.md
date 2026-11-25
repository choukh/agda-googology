# 第 0 步的精确未填值界
不读记号；条件定理：Offset 推出 ChainAdvance 1；Offset 未构造。
输入 ChainItem 1 已有居民；此文件不宣称第 0 步、Cover 或 UL.FirstRow 完成。
来源：YiTYLocal.source-feed、YiTZLocal.source-chain-one 与 YiTNShift.shifted-to-two。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTNLocal where
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTYLocal as Y
import OCF.Lean.YiTQChain as Q
import OCF.Lean.YiTNShift as S
open import Data.Product using (proj₁)
first-input : Y.Canonical.ChainItem 1
first-input = Y.Canonical.chain-one
source-two : T.Source.chain 2 ≡ Y.source-fold Q.omega
source-two = trans (Y.source-feed (T.Source.chain 1))
  (cong Y.source-fold T.source-chain-one)
Offset : Set
Offset = V.val B.zero (Y.source-fold Q.omega)
  V.≼ V.val B.zero (proj₁ S.Actual.folded)
second-from-offset : Offset → Y.Canonical.ChainAt 2 2
second-from-offset p = subst
  (λ x → V.val B.zero x V.≼ V.val B.zero (T.Canonical.Target.chain 2))
  (sym source-two) (V.≼-trans p S.shifted-to-two)
advance-from-offset : Offset → Y.Canonical.ChainAdvance 1
advance-from-offset p _ = 2 , second-from-offset p
```
