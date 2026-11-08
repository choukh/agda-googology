# 实际读回所创建的低事件成对

原 `rd₂` 在 κ₀ 闭包的每个 H₀ 坐标 x 上创建 `evx lW x`。
两端历史不同，事件增量不要求字面相等：它们是同一个有证种类，
payload 逐枝 Shape。此处覆盖全部原 H₀（包括 Ω），不只有限坐标。

本关系只记录低事件对应及可忘掉的高事件，不提供任意 continuation
的相容性。特别不能将 `paired` 作为任意 u 的函数替换律。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnValueEvent where

open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import OCF.Align.CumReadCF using (A; Lg; azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnCodeIf using (Shape; sz)
import OCF.Align.EventReturnCodeBuild as Code

data EventShape : Ev → Ev → Set where
  same-kind : ∀ c (p : c ⊲[ azero ] b₁) {x y : HB (Lev c)}
    (lx : LgB x) (ly : LgB y) → Shape x y →
    EventShape (ev c p x lx) (ev c p y ly)

payload : ∀ {a H H′} (la : Lg a) x →
  Shape (xε {a , H} (la , tt) x) (xε {a , H′} (la , tt) x)
payload la x = Code.observed la (Code.encoded x) sz

paired : ∀ {a H H′} (la : Lg a) x →
  EventShape (evx {a , H} (la , tt) x) (evx {a , H′} (la , tt) x)
paired {a} {H} {H′} la x = same-kind hz (hsuc hself)
  (lxε {a , H} (la , tt) x) (lxε {a , H′} (la , tt) x) (payload la x)

data HistLow : Hist → Hist → Set where
  empty : HistLow [] []
  low : ∀ {H H′ x y} (lx : LgB x) (ly : LgB y) → Shape x y → HistLow H H′ →
    HistLow (ev hz (hsuc hself) x lx ∷ H) (ev hz (hsuc hself) y ly ∷ H′)
  forget-left : ∀ {H H′} x (lx : LgB x) → HistLow H H′ →
    HistLow (ev (hs hz) hself x lx ∷ H) H′
  forget-right : ∀ {H H′} x (lx : LgB x) → HistLow H H′ →
    HistLow H (ev (hs hz) hself x lx ∷ H′)

extend-actual : ∀ {a H H′} (la : Lg a) → HistLow H H′ → ∀ x →
  HistLow (evx {a , H} (la , tt) x ∷ H) (evx {a , H′} (la , tt) x ∷ H′)
extend-actual {a} {H} {H′} la p x = low
  (lxε {a , H} (la , tt) x) (lxε {a , H′} (la , tt) x) (payload la x) p
```

`HistLow` 允许忘掉本次高 κ₁ 事件，并在两端接上原观察创建的 κ₀
事件。尚未证明原 u 或全部 Run 对它相容；这一欠账保留在运行侧。

以下实例来自原运行器的实际首格，并覆盖它的全部 H₀ 观察坐标。

```agda
import OCF.Align.EventReturnValueCell as Cell
import OCF.Align.EvFoldClosed as Closed

actual-erasure : HistLow (Cell.R.hc Cell.cell) []
actual-erasure = forget-left
  (proj₁ (RB κ₁ (tt , tt) (Cell.R.zRL κ₁ Cell.state)))
  (proj₂ (RB κ₁ (tt , tt) (Cell.R.zRL κ₁ Cell.state))) empty

actual-observation : ∀ x →
  HistLow
    (evx {Closed.one , Cell.R.hc Cell.cell} (tt , tt) x ∷ Cell.R.hc Cell.cell)
    (evx {Closed.W₁} (tt , tt) x ∷ [])
actual-observation x = extend-actual tt actual-erasure x
```
