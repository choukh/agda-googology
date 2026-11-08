# 实际分类器保留坐标合法性的含义

把原生分类器返回的 to 与局部分量 LegalCoordinate 对齐。
rank 的前提恰为原始 HB(Native i) 的 LgB，不额外假设 Source 世界截面。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeLegalClass where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge using (Native; Class; base; rank; raise; classify)
open import OCF.Align.BoundedNativeLegalWorld using (LegalCoordinate)

Supported : ∀ {B A} → (A → Set) → Class B A → Set
Supported Q (base κ to fr a b) = ∀ e → LegalCoordinate hz κ e → Q (to e)
Supported Q (rank i p to fr a b) = ∀ e → LgB e → Q (to e)

raise-supported : ∀ {B C A} (Q : A → Set) (p : B ⊲ C) cl →
  Supported Q cl → Supported Q (raise p cl)
raise-supported Q p (base κ to fr a b) h = h
raise-supported Q p (rank i q to fr a b) h = h

classify-supported : ∀ c κ → Supported (LegalCoordinate c κ) (classify c κ)
classify-supported hz κ e le = le
classify-supported (hs c) (inj₁ κ) =
  raise-supported (LegalCoordinate c κ) (hsuc hself) (classify c κ) (classify-supported c κ)
classify-supported (hs c) (inj₂ _) e le = le
classify-supported (hl f) (n , κ) =
  raise-supported (LegalCoordinate (f n) κ) (hlim n hself) (classify (f n) κ) (classify-supported (f n) κ)
```

Supported 已由真实 classify 对所有输入实例化，不是新增未填的接口字段。
它解决回灌取枝时“分类得到的坐标是否满足原局部合法条件”，尚不解决
折叠输出的合法性递归或保留下来种类的世界相容。
