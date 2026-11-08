# 原底算子的全参数新语义下界

这是完整原 tl/ψ̄ 运行的值定理，覆盖全部 η、世界、目标的合法环境，
包括原高阶节点内部的完整反馈。没有把读法降为有限参数测试。
它是高闭包值证明的底算子步骤，不是最终端行已经达到此处任意 η。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBaseLower (S : HtB) where
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ωˢ; toZ)
open import OCF.Free.Floor using (Flr; Ev)
open import OCF.Align.LadderOrdTree S
import OCF.Align.OrdLabZLevel as P
import OCF.Align.TotalValueBuildBaseRead S as B
open import OCF.Align.TotalValuePureLower using (pure-lower)
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.TotalOrbitRun as R
open import OCF.Align.ValueJudgeBase

omega-lower : ∀ {m c φ χ w ℓ η}
  (cv : ∀ {L} → Ev L φ → Simᴵ η L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  P.ψ⁰ (P.Ω η) ≼
    A.read (R.run (toZ (ψ̄ᵠ ok env (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ η)) ev p)))
omega-lower {η = η} cv ok env ev p = ≼-trans
  (≅→≼ (P.ψ⁰≅ψ {p = p} {σ = cv ev} (P.Ω-refl η)))
  (pure-lower (B.omega-read cv ok env ev p))
```

前提并非任意 η 都有实例；必须保留合法世界和零目标的共同界证据。
例如 η=1、φ=flo 1、ℓ=2，以 toFlo 1 suc 和零到2的路径满足要求，
环境取默认 w₀／ok₀、κ fz 的平凡需求。本文没有用记号标签作前提。
