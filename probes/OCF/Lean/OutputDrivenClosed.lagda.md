# 输出驱动世界、完整下降与无参数对角闭项

第 `r` 轮将上轮累计可数输出的后继放入最低非平凡底的指标界，
每个底执行 `r+1` 次全槽实际回灌；随后第 `r+1` 个底的原完整地板
逐底下降到可数树。`r+1` 保证每轮至少发生一次更新，并随底数增加更新轮数；
这里不假设它是传播所有高信息的充分次数，也不声称不同轮的值单调。
最终累计相邻项按原第一位置步进，因此直接给合法树与 FGH。

`Driven.output` 不读当前 State.index：零高度槽运行的低世界固定，
该指标项的多轮增长不等于新高反馈。真正读取新界的环节在非零塔槽，
其 `topT` 取 `bounds`，以及完整下降时 `topS` 读取整个新底世界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (FGH)
import OCF.Lean.OutputDrivenFamily as Family
import OCF.Lean.OutputDrivenDown as Down

module Round (r : ℕ) (c : Cd) (lc : LgB c) where
  module Worlds = Family.Family (suc r) (hs c) lc
  module D = Down.With Worlds.worlds Worlds.legal
  output : Cd
  output = D.TN r
  legal-output : LgB output
  legal-output = D.legal-TN r

y : ℕ → Cd
legal-y : ∀ r → LgB (y r)
y zero = hz
y (suc r) = y r ⊞ Round.output r (y r) (legal-y r)
legal-y zero = tt
legal-y (suc r) = Lg-⊞ _ _ (legal-y r) (Round.legal-output r (y r) (legal-y r))

stage : ℕ → Cd
stage r = Round.output r (y r) (legal-y r)

closed : Cd
closed = hl y

legal-closed : LgB closed
legal-closed = (λ r → ⊞-fst (y r) (stage r)) , legal-y

fgh : ℕ → ℕ
fgh = FGH closed
```

这给出实际闭项，不填入任何记号、外给世界族或外给输出族。
仍保留旧 Er 洗法与跨底下降规则；是否保留达到 EBO 所需的高值，
必须另作值证明，不能从原源名字或世界增长推得。
