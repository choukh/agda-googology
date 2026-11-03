# 证书与阶段无关: 与 `no-Ω₂` 并排 (陈述)

> 不含记号的定义, 但**模块层面**的导入链经 [Level](Level.lagda.md) 碰到 [Finite](Finite.lagda.md) 的镜像表记 (`InaccThetaNeg` 的既有导入, 定义级切片是 0). 所以这个文件不被任何 `LevelK*` 导入, 只用来把两个定理放在同一个类型检查里. 改变的前提见 [LevelKNeg](LevelKNeg.lagda.md).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKCoexist where

open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.InaccTreeBase using (toLv; Ω)
open import OCF.Align.InaccFloorTree using (Sib; natL)
open import OCF.Align.InaccSingularBase using (WLPO)
open import OCF.Align.InaccThetaEq using (module Eqv)
open import OCF.Align.InaccThetaNeg using (module Neg)
open import OCF.Align.LevelKNeg using (module Canon; module Co)
open import Data.Nat.Properties using (≤-refl)

module Both (S : Sib) where
  private
    module Old  = Neg S (λ _ → ⊤)
    module OldE = Eqv S (λ _ → ⊤)

  -- 旧: 第 1 层的分支全称 (`Bs 1 = ⊤`), `LvG` 推出 WLPO
  old : OldE.LvG (toLv (Ω (natL 2))) → WLPO
  old = Old.no-Ω₂

  -- 新: 第 1 层的分支在地板里, `LvG` 是定理
  new : Canon.LvG S 2 (toLv (Ω (natL 2)))
  new = Co.new S
```
