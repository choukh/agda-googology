# 原底回调夹在两次折叠之间

上界并非任意回调律。这里只消费原 tl Ωη 的异族读取以及 η 的
遗传严格性，累计层由 V3 的完整前驱嵌入吸收。世界和可入环境
仍按原运行器量化。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailBaseAbsorb (S : HtB) where
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ωˢ; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Align.LadderOrdTree S
import OCF.Align.OrdLabZLevel as P
open import OCF.Align.OrdLabZUniform using (Uniform)
open import OCF.Align.TotalValueBuildStrict using (SV; Pos; St-F; SV-toLevel)
open import OCF.Align.TotalValueTailBaseUpper S using (omega-upper)
open import OCF.Align.TotalValueTailAbsorb using (cumulative-absorbed)
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.TotalOrbitRun as R
open import OCF.Align.ValueJudgeBase using (_≼_; ≼-trans)

omega-upper-absorbed : ∀ {m c φ χ w ℓ η} → SV η → Pos η →
  (cv : ∀ {L} → Ev L φ → Simᴵ η L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  A.read (R.run (toZ (ψ̄ᵠ ok env
    (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ η)) ev p))) ≼
  P.ψ⁰ (P.Ω (toLevel (P.ψ⁰ (P.Ω η)) (Uniform η)))
omega-upper-absorbed {η = η} sv pos cv ok env ev p = ≼-trans
  (omega-upper (Uniform η) cv ok env ev p)
  (cumulative-absorbed (SV-toLevel _ (Uniform η) (St-F sv pos)))
```
