# 相关事件历史的低层重放

高事件可以被忘掉，观察新建的低事件只要求增量逐枝同形。
这里证明这种历史关系确实保持原重放器算出的低界，而不只是
给两张表贴上关系。它不声称保持高界或原 Run 的任意分支。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnReplay where

open import Data.Product using (Σ; _,_; _×_)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree using (Hist; rp; b₁)
open import OCF.Align.EventReturnCodeIf using (Shape; sz; ss; sl; so)
open import OCF.Align.EventReturnValueEvent using (HistLow; empty; low; forget-left; forget-right)

add-shape : ∀ {S : KS} {a a′ b b′ : HB S} → Shape a a′ → Shape b b′ →
            Shape (a ⊞ b) (a′ ⊞ b′)
add-shape p sz = p
add-shape p (ss q) = ss (add-shape p q)
add-shape p (sl q) = sl (λ n → add-shape p (q n))
add-shape p (so q) = so (λ e → add-shape p (q e))

low-replay : ∀ {H H′ : Hist} → HistLow H H′ →
  Shape (rp H hz (hsuc hself)) (rp H′ hz (hsuc hself))
low-replay empty = sz
low-replay (low lx ly p q) = add-shape (low-replay q) p
low-replay (forget-left {H} {H′} x lx q) = low-replay {H} {H′} q
low-replay (forget-right {H} {H′} x lx q) = low-replay {H} {H′} q

-- 同一世界中的字面位置可以按 Shape 配对；不把 Shape 当命题等式。
positions : ∀ {S : KS} {a b : HB S} → Shape a b →
            ∀ {w x} → x ⊲[ w ] a → Σ (HB S) (λ y → (y ⊲[ w ] b) × Shape x y)
positions p hself = _ , (hself , p)
positions (ss p) (hsuc q) with positions p q
... | y , (r , s) = y , (hsuc r , s)
positions (sl p) (hlim n q) with positions (p n) q
... | y , (r , s) = y , (hlim n r , s)
positions (so p) (hLim {c = c} e q) with positions (p c) q
... | y , (r , s) = y , (hLim e r , s)
```

`positions` 只在相同世界内运输字面位置，允许右侧坐标取逐枝对应者；
没有证明固定原坐标也在右界内。用于运行时，还须回调尊重相关坐标。

以下将通用重放定理实例化到原 κ₁ 首格及其全部观察坐标。

```agda
open import Data.Unit using (tt)
open import Data.List using ([]; _∷_)
open import OCF.Align.EvFoldRead using (evx)
import OCF.Align.EventReturnValueEvent as E
import OCF.Align.EventReturnValueCell as Cell
import OCF.Align.EvFoldClosed as Closed

actual-low : Shape (rp (Cell.R.hc Cell.cell) hz (hsuc hself))
                   (rp [] hz (hsuc hself))
actual-low = low-replay E.actual-erasure

actual-next : ∀ x →
  Shape (rp (evx {Closed.one , Cell.R.hc Cell.cell} (tt , tt) x ∷ Cell.R.hc Cell.cell) hz (hsuc hself))
        (rp (evx {Closed.W₁} (tt , tt) x ∷ []) hz (hsuc hself))
actual-next x = low-replay (E.actual-observation x)
```
