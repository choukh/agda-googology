# 完成后补字面共同界的精确接口

输入只有原合法公共高度B及其位置a。若要用有界高度比较处理任意
完成输入，就还须实填下面的共同界字段，不能把Sim当作该字段。
本接口与HeightIf.capture不同：它只问完成高度有没有可用的共同界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableCompletionBoundIf where
open import Data.Product using (Σ; _×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableHeightIf using (Leading; path)
open import OCF.Lean.GeneralOmegaCountableHeightLeading using (leg-leading)

Common : Cd → Cd → Set
Common a b = Σ Cd (λ W → LgB W × ((a ⊲ W) × (b ⊲ W)))
record PositionCompletionBounding : Set where
  field
    bound : ∀ {a B : Cd} → LgB B → a ⊲ B → Common (leg a) (leg B)

-- 前沿域的实际构造；它不填满任意位置的字段。
leading-bound : ∀ {a B : Cd} → Leading a B → Common (leg a) (leg B)
leading-bound {B = B} p = leg B , Lg-leg B , path (leg-leading p) , hself
```

leading-bound适用于任意非有限前沿位置，全部原左加法前缀均属此域。
任意hlim n位置是否支持这个字段另行检验，不以该部分构造代替全域。
