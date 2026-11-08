# 以可数输出回灌全部Ω的消费接口

原样补齐所有raw坐标支持已被反例排除。本实验不保留目标Ω节点，全部
Ω都走同一Cd对角回灌；因此没有向keep索取任意raw坐标证书。回调输出
先合法化，再结构编码到源Coord。算法不同于旧typed fold，不声称保值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumeIf where
open import Data.Product using (Σ)
open import OCF.Lean.CRwBase
open import OCF.Lean.HigherIndexClassIf using (U; Native)
open import OCF.Lean.HigherIndexFoldIf using (Source)
open import OCF.Lean.HigherIndexSupportIf
open import OCF.Lean.HigherIndexSupportSource using (Supported)

record CoordinateCoding : Set₁ where
  field
    code : ∀ c κ β → LgB β → Cd → Σ (E (Native c) κ) (Coord c κ β)
    legal-next : ∀ c κ β → LgB β → ∀ e (ad : Coord c κ β e) → LgB (next c κ β e ad)

record Consumer : Set₁ where
  field
    run : ∀ β → LgB β → ∀ B → LgB B → ∀ a → Supported β B a → Cd
```

code的rank分支将用原floor c加纯嵌入，不用常值坐标；低指标用β加leg。
界的关系仍由Coord及已有next-up携带。Consumer只给原函数类型，实际
运行器另给构造子方程、全floor实例与可数合法完成；不以记录本身验收。
