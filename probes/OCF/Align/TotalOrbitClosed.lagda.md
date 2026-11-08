# 删去原证书生产的完整高源实验

固定原来已验高实例的整个源，而不预先算出其 `V` 或搬运 `Goodᴺ`。
底输出采用新累积语义，因而闭项合法但不继承旧值标签。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalOrbitClosed where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
import OCF.Free.TotalOrbitBuild as A
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.LadderOrdPos using (HB; end)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
import OCF.Align.LadderOrdTree as T

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

module Rows (S : HtB) where
  open T S

  raw : Ht → Ordᴵ → Z
  raw m a = toZ (ψ̄ᵠ ok₀ (λ i h r → ok₀ i) (Ω̇ m a) ev₀ zero)

  tree : Ht → Ordᴵ → Ordᶜ zero
  tree m a = A.tree (raw m a)

  legal : ∀ m a → HS (tree m a)
  legal m a = A.legal (raw m a)

module High = Rows (HB ω²ᶜ)

closed : Ordᶜ zero
closed = High.tree end zero

closed-legal : HS closed
closed-legal = High.legal end zero

fgh : ℕ → ℕ
fgh = FGH closed
```

本篇执行与证书没有使用 `LadderOrdMain`、`GᴺTᵠ` 或 `forceᴺ`。
保留 Q／地板／环境生成源，尚未全删；已删的是原整套合法性生产。
旧源在旧语义的值为 ψ₀(Ω_{Ω·ω²})，这句话不能用作本闭项的值界。
