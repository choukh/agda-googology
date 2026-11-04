# 读位置的证据搬到 `X₀`

> 不含记号. 结论写在 [DomFold](DomFold.lagda.md). `Tc` 在 [GuardTightBase](GuardTightBase.lagda.md) 与 [DomFoldBase](DomFoldBase.lagda.md) 里只差 `⊲` 的写法, 所以旧的紧证据 (`RdIter.Tc-c`, `RdAdd.Tc-top` 等) 一个函数就搬过来.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DomFoldRead where

open import Data.Product using (_,_)
open import OCF.Align.GuardTightLv
open Lv Dom₀
import OCF.Align.GuardTightBase as GB
open import OCF.Align.DomFoldDom using (X₀)
import OCF.Align.DomFoldBase as DBase
private module NB = DBase X₀

convR : ∀ {c t g} → GB.Rdr c t g → NB.Rdr c t g
convR r η e P with r η e P
... | GB.rdF d Q tr = NB.rdF d Q tr
... | GB.rdB a ea l d Q tr = NB.rdB a ea (λ q → GB.⊲-lt {a} {η} l q) d Q tr

convTc : ∀ L → GB.Tc L → NB.Tc L
convTc zero tc = tc
convTc (suc k) tc = convTc k tc
convTc (lim f) tc = λ n → convTc (f n) (tc n)
convTc (lc c t g) (r , u , v) = convR r , convTc t u , (λ η e → convTc (g η e) (v η e))
```
