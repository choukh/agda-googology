# 任意raw坐标不能原样补上未来支持

共用冻结HigherIndexSupportIf。这里针对原样读取所有raw坐标的必要条件，
不针对允许变换未准入坐标的算法。选定raw坐标在每个合法低界都会读取
该界自身，然后要求其二次后继位于一次后继内；所以扩大初界也不能补证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HigherIndexConsumeNegFuture where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.HigherIndexClassIf using (Native)
open import OCF.Lean.HigherIndexSupportIf
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (no-successor-back)
import OCF.Align.HigherIndexFoldNegRank as Old

raw : HB (Native Old.omega)
raw = hΩ (inj₁ tt , inj₂ tt)
  (λ e → hΩ (inj₂ (hs (hs e)) , inj₂ tt) (λ _ → hz))

no-support : ∀ β → LgB β → Support Old.omega β raw → ⊥
no-support β lb s = no-successor-back (hs β)
  (proj₁ (proj₁ (proj₂ s β (hself , lb))))

no-future-coordinate : ∀ β → Coord (hs Old.omega) (inj₂ tt) β raw → ⊥
no-future-coordinate β (v , p , lv , s) = no-support v lv s

-- 当前世界可取合法零界；允许的坐标域也非空。
zero-admitted : Coord (hs Old.omega) (inj₂ tt) hz hz
zero-admitted = hz , hself , tt , tt
```

raw是所检验的全raw域中的真实元素，没有声称它合法。原样全raw接口
必须处理它；如果接口只接收合法或已支持坐标，本定理不能代替所需反例。
原高层地板与公共高界的合法性已有Old.legal-input、Old.legal-B，
并未假定所有坐标受支持。此结果也不否定准入域保访问的总变换。
