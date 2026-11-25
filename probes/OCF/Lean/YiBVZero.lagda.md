# 零项情形覆盖最小实例的一切孩子
验收文件，读记号；编译定理：任意 d 的指定孩子折叠均承载 fsT slot []。
这处理 M⁰ 推导的 mz 情形；没有处理 m1/mL/mw，不是 BranchNeed 的居民。
表、底与路径逐字使用 YiBVSmall 的最小规范实例；没有接到实际截段。
来源：YiBVReadBound.extend 与已实填的 YiBVSmall.at-two。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBVZero where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiBVDomain as D
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiBVReadBound as R
import OCF.Align.EboLeanDef as E
zero-at : ∀ d (o : P.Ok (S.child d)) (r : TB.Rb (S.child d))
  → R.Bound S.small-index (S.child d) o r (S.lower d)
zero-at d = R.extend-presented S.small-index K.two (P.inc tt P.self) S.at-two
  (B.suc d) (S.child d) refl
all-zero : ∀ d → H.M 1 (E.fsT D.slot []) (proj₁ (S.Small.child-out d))
all-zero d = zero-at d (proj₂ S.okay d) (proj₂ (D.Input.table S.minimal) d)
  (S.Small.child-base d) (O.Ωt K.one) (λ i u → K.⊴r) (H.Mβ 0)
```
