# 实际相邻 Stage 的坐标相同，可入范围却不同

本文件纠正“跨 step 保留节点必需高层坐标回缩”的过强判断。
源 Stage(step S) 的旧种类与目标 Stage S 的种类坐标相同。
下面在实际 S⊥ 实例上证明障碍可以完全落在可入证据，和坐标类型无关。
只否定固定低世界下保持该坐标的可入拉回，不否定会增长低世界的折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerStageBoundary where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerWorldStage

module Source = Stage (step S⊥) (tt , hz)
module Target = Stage S⊥ tt

same-coordinate : Source.E′ (inj₁ (inj₂ tt)) ≡ Target.E′ (inj₂ tt)
same-coordinate = refl

target-one : Target.A′ hz (inj₂ tt) (hs hz)
target-one = hsuc hself , tt

source-no-one : ∀ (B : HB (step S⊥)) → Source.A′ B (inj₁ (inj₂ tt)) (hs hz) → ⊥
source-no-one B ()

no-fixed-pull : (∀ (B : HB (step S⊥)) (c : Cd) →
  Target.A′ hz (inj₂ tt) c → Source.A′ B (inj₁ (inj₂ tt)) c) → ⊥
no-fixed-pull pull = source-no-one hz (pull hz (hs hz) target-one)

-- 使用的低世界不是非法世界。
legal-low-world : LgW (step S⊥) (tt , hz)
legal-low-world = tt , tt
```

前提有显式实例：低世界合法，目标坐标 1 合法且带尾部路径 0⊲1。
结论对所有源外层世界 B 成立，说明仅升外层 B 不能改变被冻结的低层界。
没有比较裸下标，也不声称源与目标拥有统一公共上界。
翻译账：只检验已有 Stage 的具体实例，不改树、可入或折叠。
