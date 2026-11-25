# 第 0 步的已通过部分：cof 与第 1 层向上搬运
验收文件；编译定理：slot 的 cof 前提成立，第 1 层使用 YiCLFam.m⊴N 1。
kept 的头与分支类型转换在私有试验中 8G 耗尽；改形状后仍耗尽，按本路停止条件停报。
本件不构造或改名原 BranchNeed，不给出 NextSlot 或第 1 项的条件接线。
来源：slot 复用 YiC0Next；向上搬运直接复用 YiCLFam.m⊴N。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWXCheck where
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiC0Next as N

slot-cof : E.cof N.slot ≡ E.cΩ []
slot-cof = refl

up-one : ∀ {t x x′} → H.M 1 t x → K._⊴_ x x′ → H.M 1 t x′
up-one = H.m⊴N 1
```
