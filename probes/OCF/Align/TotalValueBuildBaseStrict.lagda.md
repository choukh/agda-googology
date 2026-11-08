# 原 base 回调输出的严格性闭包

字段逐字作用原 tl/ψ̄/run，不是另外一个反馈解释器。参数 SV 在旧
NC 全轨道可满足；累计偏移的 SV 经真实 Run.add 保持。这里给实际
递归一步需要的生成性，不把它冒充私有整个 coord 的已完成模拟。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseStrict (S : HtB) where
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ωˢ; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Align.LadderOrdTree S
import OCF.Align.OrdLabZLevel as P
open import OCF.Align.TotalValueBuildStrict using (SV; Pos; St-F; module N; SV-L; pos-L)
open import OCF.Align.TotalValueBuildRunStrict using (pure-strict; add-sv)
open import OCF.Align.TotalValueBuildBaseEmbedding S using (pure-right)
import OCF.Align.TotalValueBuildBaseRead S as B
import OCF.Free.TotalOrbitRun as R

callback-sv : ∀ {m c φ χ w ℓ η}
  (sv : SV η) (pos : Pos η)
  (cv : ∀ {L} → Ev L φ → Simᴵ η L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  SV (R.run (toZ (ψ̄ᵠ ok env
    (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ η)) ev p)))
callback-sv {η = η} sv pos cv ok env ev p = pure-strict (St-F sv pos)
  (pure-right (B.omega-read cv ok env ev p)
    (≅-sym (P.ψ⁰≅ψ {p = p} {σ = cv ev} (P.Ω-refl η))))

feedback-sv : ∀ offset {m c φ χ w ℓ η} → SV offset →
  (sv : SV η) (pos : Pos η)
  (cv : ∀ {L} → Ev L φ → Simᴵ η L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  SV (R.add offset (R.run (toZ (ψ̄ᵠ ok env
    (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ η)) ev p))))
feedback-sv offset d sv pos cv ok env ev p =
  add-sv d (callback-sv sv pos cv ok env ev p)

original-callback : ∀ n {m c φ χ w ℓ}
  (cv : ∀ {L} → Ev L φ → Simᴵ (N.L n) L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  SV (R.run (toZ (ψ̄ᵠ ok env
    (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ (N.L n))) ev p)))
original-callback n = callback-sv (SV-L n) (pos-L n)
```
