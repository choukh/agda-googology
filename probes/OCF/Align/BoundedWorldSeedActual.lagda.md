# 全部真实旧最高坐标的Seed实例

不是仅给初始地板：原Whole.Model.ce每一步由原act与加法生成，
因此整族均取得中Ω只在Seed0坐标上量化的证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldSeedActual where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedWorldSeedIf
open import OCF.Align.BoundedWorldSeedClosure
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Align.BoundedWorldPrefixSeed as Prefix

old1-coordinates : ∀ n → Seed1 (Whole.Model.ce n)
old1-coordinates zero = floor1
old1-coordinates (suc n) = add1 (old1-coordinates n) (act1 (old1-coordinates n))

actual-prefix : Seed1 Prefix.prefix
actual-prefix = old1-coordinates 1
```

证书本身不证明中槽可以从任何输入恢复，也不证明这些输出进入C。
mid保持仍是独立义务，不从接口记录推定其存在。
