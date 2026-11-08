# Ω指标分类不能擦除可入字段

共用冻结HigherIndexClassIf。否定对象仅是自动给所有raw种类填Position，
不是带证分类接口。固定世界里的合法Ω指标树既有可入分量，也有不可入
分量；下面全部使用实际同一类型的种类。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HigherIndexNegPosition where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (ls; lz)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.HigherIndexClassIf
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (no-successor-back)

omega : HB U
omega = flL (ls lz)
legal-omega : LgB omega
legal-omega = Lg-flL (ls lz)

blocked-kind : ∀ β → K (Native omega)
blocked-kind β = inj₂ (hs β) , inj₂ tt
no-position : ∀ β → Position (tt , β) omega (blocked-kind β) → ⊥
no-position β p = no-successor-back β (proj₁ p)

-- 合法世界实例覆盖任意合法β，故不是利用非法世界造成失败。
legal-world : ∀ β → LgB β → LgW U (tt , β)
legal-world β lb = tt , lb

-- 同一合法世界和同一合法Ω树，坐标0的分量可入。
allowed-kind : K (Native omega)
allowed-kind = inj₂ hz , (inj₁ tt , inj₂ tt)
allowed : Position (tt , hs hz) omega allowed-kind
allowed = hsuc hself , tt

no-total-position :
  (∀ κ → Position (tt , hs hz) omega κ) → ⊥
no-total-position all = no-position (hs hz) (all (blocked-kind (hs hz)))

-- 真正经过Ω分支的路径有实例，不可沿用Cd的荒谬消去。
omega-path : hs hz ⊲[ (tt , hs hz) ] omega
omega-path = hLim hself hself
branch-one : Position (tt , hs hz) omega (blocked-kind hz)
branch-one = hself , tt

-- 另一个rank实例的指标本身含Ω。
above-omega : Position (tt , hs hz) (hs omega) (inj₂ tt)
above-omega = tt
rank-witness : Class (tt , hs hz) (hs omega) (E (Native (hs omega)) (inj₂ tt))
rank-witness = rank omega hself (λ a → a) (λ a → a) (λ _ → refl) (λ _ → refl)
```

可入样本与不可入样本共享合法世界(tt,1)、合法指标omega；失败只出在
显式分量坐标2不在界1内。rank-witness的指标本身含Ω，但共同界为
hs omega，直接路径hself，不需要任何裸指标三歧。
本篇不给原C封顶，也不否定下一指标层带Position的构造。
