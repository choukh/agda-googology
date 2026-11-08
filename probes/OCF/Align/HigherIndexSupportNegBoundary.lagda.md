# 旧rank障碍在未来支持界下的实际准入

共用冻结的Support接口。旧合法坐标不能在当前低界取得支持，但在
后继低界取得支持，并成为新rank的真实准入坐标。这里检验准入域，
不宣称已经构造支持化输出或证明原raw运行器合法。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HigherIndexSupportNegBoundary where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.HigherIndexSupportIf
import OCF.Align.HigherIndexFoldNegRank as Old
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (no-successor-back)

not-current : ∀ β → Support Old.omega β (Old.coordinate β) → ⊥
not-current β s = no-successor-back β (proj₁ (proj₁ s))

future-support : ∀ β → Support Old.omega (hs β) (Old.coordinate β)
future-support β = (hself , tt) , (λ e ad → tt)

rank-admitted : ∀ β → LgB β →
  Coord (hs Old.omega) (inj₂ tt) β (Old.coordinate β)
rank-admitted β lb = hs β , hsuc hself , lb , future-support β

actual-next : ∀ β (lb : LgB β) →
  next (hs Old.omega) (inj₂ tt) β (Old.coordinate β) (rank-admitted β lb) ≡ hs β
actual-next β lb = refl

zero-instance : Coord (hs Old.omega) (inj₂ tt) hz (Old.coordinate hz)
zero-instance = rank-admitted hz tt
```

输入坐标的合法性是原Old.legal-coordinate；旧完整地板与公共高界
仍分别为Old.input与Old.B，并有Old.legal-input、Old.legal-B。
新准入允许未来界，所以原not-current不能用来否定新Coord。
这里也没有要求β和高界每次同时严格增长。
