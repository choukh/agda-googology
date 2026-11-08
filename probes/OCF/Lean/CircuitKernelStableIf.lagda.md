# Third 的遗传未来证书：候选充分域

本证书不是纲领要求，也不是旧 Gd 的等价改名。Ω 分支必须在每个
合法未来世界的实际 AdT 坐标上继续给遗传证书。KS 没有世界自反字段，
所以未来关系显式加入“停留”；不假定原世界序自反。
这里只给候选域，不承诺原全地板或 Φ 输出落入此域。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitKernelStableIf where
open import Data.Unit using (⊤)
open import Data.Product using (_×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
import OCF.Lean.ThirdFold as F

module For (U : KS) where
  data Future (w : Wd U) : Wd U → Set where
    stay : Future w w
    grow : ∀ {v} → _≤w_ U w v → Future w v

  Stable : ∀ m → Wd U → HB (Tw U m) → Set
  Stable m w hz = ⊤
  Stable m w (hs a) = Stable m w a
  Stable m w (hl f) = ∀ n → Stable m w (f n)
  Stable m w (hΩ κ g) = Pos U w m κ ×
    (∀ {v} → Future w v → (lv : LgW U v) → ∀ e →
      F.AdT U v lv m κ e → Stable m v (g e))
```
