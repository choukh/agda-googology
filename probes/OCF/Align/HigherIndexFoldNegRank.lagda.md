# 动态低指标策略之后的真实rank坐标缺口

共用冻结HigherIndexFoldStrategyIf。它已修复原omega组件地板；本篇
检验其后继组件的完整地板。最高rank仍要求全部raw坐标，而合法坐标
也可含当前低界不可入的种类。否定仅针对这个Path全分支字段。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HigherIndexFoldNegRank where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecFl using (flL; Lg-flL; Lg-ι)
open import OCF.Lean.HigherIndexClassIf using (U; Native)
open import OCF.Lean.HigherIndexFoldIf using (k; g; Source)
open import OCF.Lean.HigherIndexFoldStrategyIf using (Path)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (no-successor-back)

omega : HB U
omega = flL k
c : HB U
c = hs omega
B : HB U
B = hs c
legal-c : LgB c
legal-c = Lg-flL k
legal-B : LgB B
legal-B = legal-c
c-in-B : ∀ β → c ⊲[ tt , β ] B
c-in-B β = hsuc hself

-- 该坐标自身合法；分支恒为0，所以并非借不合法坐标触发缺口。
coordinate : Cd → HB (Native omega)
coordinate β = hΩ (inj₂ (hs β) , inj₂ tt) (λ _ → hz)
legal-coordinate : ∀ β → LgB (coordinate β)
legal-coordinate β = (λ lw e e′ p → hself) , (λ lw e → tt)

input : HB Source
input = ι (inj₂ c) (flL (g c))
legal-input : LgB input
legal-input = Lg-ι (inj₂ c) (flL (g c)) (Lg-flL (g c))

obstruction : ∀ β → Path β B input → hs β ⊲ β
obstruction β p = proj₁ (proj₂ (proj₁ (proj₂ p (coordinate β))))
no-input-path : ∀ β → Path β B input → ⊥
no-input-path β p = no-successor-back β (obstruction β p)

legal-world : ∀ β → LgB β → LgW U (tt , β)
legal-world β lb = tt , lb
```

最高分支先读coordinate β，没有先经过changing事件；其up后的旧种类
沿Position读到hsβ⊲β。低世界可取合法β=0，公共高界与原输入、所选
rank坐标均合法。故只把raw量词缩为合法坐标仍不足，还须表达相对于
当前世界的坐标支持，或设计能接纳该坐标的动态策略。

此结果不否定StrategyClosed对原omega组件的修复，也未证明任何实际
反馈轨道恰会采到coordinate β，不是否定输出合法性或序数强度。
