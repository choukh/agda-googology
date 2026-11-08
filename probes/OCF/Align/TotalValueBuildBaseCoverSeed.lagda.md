# 原首闭包起点保留整个第一旧层号

不以值不等式反射前驱域：原 seed 就是同参数 Ω1 的完整读取，故用
BaseEmbedding 直接嵌入，再沿真实累计前缀与 Trace.start 搬到坐标0。
这是后续全轨道归纳的实填初值，不是最终高行验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseCoverSeed (S : HtB) where
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Free.Level
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.TotalValueBuildIf using (BoundedEmbedding)
open import OCF.Align.TotalValueBuildStrict using (module N)
open import OCF.Align.TotalValueBuildBaseEmbedding S using (original-step)
open import OCF.Align.TotalValueBuildEmbedding using (cumulative)
open import OCF.Align.TotalValueEmbeddingOps using (compose)
open import OCF.Align.ValueJudgeBase using (_≼_)
import OCF.Align.TotalValueBuildBaseOrbit S as Orbit
import OCF.Align.TotalValueBuildBaseCoverStep S as Cover
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.TotalOrbitRun as R
open import OCF.Free.Prefix using (toZ)

module Actual {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) where
  module B = Orbit.Actual ok env ev p
  module C = Cover.Actual ok env ev p

  seed-embedding : BoundedEmbedding (N.L 1) (B.η zero)
  seed-embedding = subst (BoundedEmbedding (N.L 1)) (sym B.start)
    (compose (original-step zero proj₂ ok env ev p)
      (cumulative B.c (R.run (toZ B.seed))))

  second-whole : N.γ 2 ≼ A.read (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p)))
  second-whole = C.whole 1 zero seed-embedding
```
