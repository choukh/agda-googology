# 原 base 回调消费有界前驱嵌入

原 rowB 的回调不是任意 Z 函数。本篇固定其真实 tl Ωζ 和地板
fz⊔fkζ，完整消费源参数到 ζ 的有界嵌入。所有内部 typed Ω 反馈都由
BaseRead 保留，最终由新 run 的实际累计输出覆盖。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseConsumer (S : HtB) where
open import Data.Product using (proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ωˢ; toZ)
open import OCF.Free.Floor using (Ev; fz; fk; _⊔_)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.TotalValueBuildIf using (BoundedEmbedding)
open import OCF.Align.TotalValueBuildTypedEmbedding using (bounded-ψ; cumulative-ψ)
open import OCF.Align.TotalValueBaseLower S using (omega-lower)
import OCF.Align.OrdLabZLevel as P
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.TotalOrbitRun as R
open import OCF.Align.ValueJudgeBase using (_≼_; ≼-trans)

base-callback : ∀ {m a χ w ℓ η ζ} → BoundedEmbedding η ζ →
  (ok : Ok w) (env : Eh h₀ m w χ)
  (ev : Ev ℓ (fz ⊔ fk ζ)) (p : zero <ᴵ ℓ) →
  P.ψ⁰ (P.Ω η) ≼ A.read (R.run
    (toZ (ψ̄ᵠ ok env
      (tl {m = m} {c = a} {χ = χ} (fz ⊔ fk ζ)
        (λ e q → proj₂ e (suc q)) (Ωˢ ζ)) ev p)))
base-callback emb ok env ev p = ≼-trans (bounded-ψ emb)
  (omega-lower (λ e q → proj₂ e (suc q)) ok env ev p)

cumulative-callback : ∀ c η {m a χ w ℓ}
  (ok : Ok w) (env : Eh h₀ m w χ)
  (ev : Ev ℓ (fz ⊔ fk (R.add c η))) (p : zero <ᴵ ℓ) →
  P.ψ⁰ (P.Ω η) ≼ A.read (R.run
    (toZ (ψ̄ᵠ ok env
      (tl {m = m} {c = a} {χ = χ} (fz ⊔ fk (R.add c η))
        (λ e q → proj₂ e (suc q)) (Ωˢ (R.add c η))) ev p)))
cumulative-callback c η ok env ev p = ≼-trans (cumulative-ψ c η)
  (omega-lower (λ e q → proj₂ e (suc q)) ok env ev p)
```

这给出全部参数的原 base 回调，而非仅 0/1 或有限样本。尚未证明
旧整条反馈轨道在每一步嵌入新轨道；也未证明 rowC 的 Ωd 与更新后
cap 环境消费同一嵌入。因此不能将本篇当作高端闭项已达到旧值。
