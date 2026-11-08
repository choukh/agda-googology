# 累积解释器的直接布劳威尔树闭项

本版本与 TotalOrbitClosed 执行同一新算法，尝试删除最后 Ordᴵ→Ordᶜ0
的表示转换。类型内置的是 `⊑ᴵ` 步进，尚未证字面第一位置；本篇是
较弱 View 的表示实验，不是纲领全部验收已完成的成品。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.TotalOrbitNative where

open import Data.Nat using (ℕ; zero)
open import OCF.Free.Level using (Ordᴵ; zero)
import OCF.Free.TotalOrbitRun as A
import OCF.Free.NativeBrouwer as N
import OCF.Align.TotalOrbitSource as S
open import OCF.Align.LadderOrdPos using (end)

closed : Ordᴵ
closed = A.run (S.High.raw end zero)

closed-view : N.View closed
closed-view = N.view closed

fgh : ℕ → ℕ
fgh = N.FGH closed
```

这仍不是旧 ψ₀(Ω_{Ω·ω²}) 的值证明；原高源仍完整，读法未核准。
