# b₂ 在下一实际有限层的零槽中

第四层，无条件。将第 3 层所有带覆盖证书的运行都达到 b₂ 的定理，用于第 4 层实际零槽内重算的运行。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseRunValue where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (proj₁)
open import OCF.Align.Value using (_≼_)
open import WVOne using (read)
import W4Block as W
import W4Path as P
import B12Terminal as T
import B13FiniteTower as Fin
import B12TerminalTail as Tail
import WVTwo
open import Relation.Binary.PropositionalEquality using (refl)
import WKTower as Tower
open import Survey.W4FiniteRaiseRun using (module At)
import B12TerminalSrc as Source
import B13FiniteClosed as Covered
import Survey.W4PTOFinite as PTO
open import OCF.Lean.YiRefTw2 using (Rt)
import Survey.EboPTOFinite as B

module Actual = At Source.middle

two-in-slot : Rt (B.tower-h 2 2) ≼ read (proj₁ (T.Run.bs (T.finiteRun 3) W.zero
  (Actual.path 2 (P.z≤ (Tower.gL 2)))))
two-in-slot = Actual.transfer 2 (Rt (B.tower-h 2 2)) PTO.two-in-run Covered.middle-covered

module TailFromTwo = Fin.Actual WVTwo.lvl2 2 refl Tail.mulω (Rt (B.tower-h 2 2))
  (Fin.timesω (Tower.gL 2)) PTO.two-in-run

ix : ℕ → ℕ
ix = W.iter suc 2

tail-in-slots : ∀ m → Fin.constant Tail.mulω (Rt (B.tower-h 2 2)) m ≼
  read (proj₁ (T.Run.bs (Actual.higher (ix m)) W.zero (Actual.path (ix m) (P.z≤ (Tower.gL (ix m))))))
tail-in-slots m = Actual.transfer (ix m) (Fin.constant Tail.mulω (Rt (B.tower-h 2 2)) m)
  (TailFromTwo.allAt m) Covered.middle-covered
```
