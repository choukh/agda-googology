# 只生产完整高源，不导入计值与证书

与本轮 TotalOrbitClosed 的 raw 定义逐字相同，单独放置以隔离成品生产
与表示转换／验收。不改任何旧 Ladder 文件。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.TotalOrbitSource where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.LadderOrdPos using (HB)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
import OCF.Align.LadderOrdTree as T

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

module Rows (S : HtB) where
  open T S
  raw : Ht → Ordᴵ → Z
  raw m a = toZ (ψ̄ᵠ ok₀ (λ i h r → ok₀ i) (Ω̇ m a) ev₀ zero)

module High = Rows (HB ω²ᶜ)
```
