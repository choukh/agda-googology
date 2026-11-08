# 复合折叠的单向上移律

实际使用 Fab3Typed 的合法折叠，不改规则。对任意层 n 与值合法输入 x，
把 x 上移一层再折到底，不低于原来折到底的值。
这不是 `NegFold1Fab3` 否定的双向相容：上移会增加折叠次数，允许值增长。
所有层对由显式有限上移路径联系，公共上界就是路径终点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SupValueLift where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.Fab3Typed using (T; Ω; W; fold; module Fold; Σ⊥)
open import OCF.Align.Fab5ValRel using (module Rel; Mo-up)
open import OCF.Align.Fab5Val using (crT; cr⊥; LE; fold-mono; Mo-Ω; module FoldVal)

module R n = Rel (crT n)

lift-lower : ∀ n (x : HB (T n)) → R.Mo n (W n) x →
  LE 0 (fold n x) (fold (suc n) (up x))
lift-lower n x mx = fold-mono n mx
  (FoldVal.Mo-Ψ (T n) (crT n) (R.≤-refl n _) (Mo-Ω n)
    (up x) (Mo-up (crT n) x mx))
  (FoldVal.infl (T n) (crT n) x)

level : ℕ → ℕ → ℕ
level n zero = n
level n (suc k) = suc (level n k)

raise : ∀ n k → HB (T n) → HB (T (level n k))
raise n zero x = x
raise n (suc k) x = up (raise n k x)

raise-mo : ∀ n k x → R.Mo n (W n) x → R.Mo (level n k) (W (level n k)) (raise n k x)
raise-mo n zero x mx = mx
raise-mo n (suc k) x mx = Mo-up (crT (level n k)) (raise n k x) (raise-mo n k x mx)

raise-lower : ∀ n k x → R.Mo n (W n) x →
  LE 0 (fold n x) (fold (level n k) (raise n k x))
raise-lower n zero x mx = R.≤-refl 0 _
raise-lower n (suc k) x mx = R.≤-trans 0 (raise-lower n k x mx)
  (lift-lower (level n k) (raise n k x) (raise-mo n k x mx))

sample : ∀ n → HB (T n) → ℕ → HB S⊥
sample n x k = fold (level n k) (raise n k x)

sample-step : ∀ n x → R.Mo n (W n) x → ∀ k → LE 0 (sample n x k) (sample n x (suc k))
sample-step n x mx k = lift-lower (level n k) (raise n k x) (raise-mo n k x mx)

-- 对真实地板族的实例，不是空的谓词。
floor-raise : ∀ n k → LE 0 (fold n (Ω n)) (sample n (Ω n) k)
floor-raise n k = raise-lower n k (Ω n) (Mo-Ω n)
```

这是 sup 值下界的一个可直接使用的步骤：若某个 sup 构造覆盖第 m 层
经过有限上移的输入，则它也覆盖原层输入；不必证明上移保持值相等。
这里还没有把任意 sup 输入投影到各分量，因而没有声称 sup 折叠已完成。
翻译账：只加值定理；上移、折叠与值合法条件均为既有树侧定义。
