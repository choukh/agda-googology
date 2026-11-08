# 有最大分支不补出旧值关系的Ω左规则

共用HigherIndexViewIf的实际有界值域。零界下的常零Ω节点仍是合法
闭对象，全部可入分支都为零。然而Fold1If的旧高层关系没有Ω左消去，
不能据最大分支把节点与零验收为该关系下的同值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HigherIndexViewNegValue where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.HigherIndexViewIf

module D = Domain (step S⊥) (tt , hz) (tt , tt)

source : HB (step S⊥)
source = hΩ (inj₂ tt) (λ _ → hz)
source-legal : LgB source
source-legal = (λ _ _ _ _ → hself) , (λ _ _ → tt)
object : D.Object
object = source , source-legal

maximum : E D.Target (inj₂ tt)
maximum = hz , hself
maximum-property : ∀ e → Pr D.Target (inj₂ tt) tt e maximum
maximum-property (e , bd) = bd

branch-zero : ∀ (e : E D.Target (inj₂ tt)) → D.restrict (hz {S = step S⊥}) ≡ hz
branch-zero (e , bd) = refl

not-node-below-zero : D.value object ≤ᵛ hz → ⊥
not-node-below-zero ()
```

否定的只是既有高层关系中的这个上界。若另定义Ω为有界分支上确界的
Cd解释，常零节点解释为零并无矛盾；那是新解释，仍需明确相应值口径。
本篇没有否定动态支持路线、任何折叠或C的强度。
