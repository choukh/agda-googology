# 原底回调的完整累计上界实例

这里把纯读取上界用于原 tl Ωη 的实际运行，保留全部环境、共同源界
和原反馈基本列。输出不是任意模型。上界为原 ordᴰ 累计后的读回；
它尚需另经累计吸收定理才能变成最终闭项的具名高度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailBaseUpper (S : HtB) where
open import Data.Nat using (ℕ; suc)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ωˢ; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Align.LadderOrdTree S
import OCF.Align.OrdLabZLevel as P
import OCF.Align.TotalValueBuildBaseRead S as B
open import OCF.Align.TotalValueBuildBaseEmbedding S using (pure-right)
open import OCF.Align.TotalValueTailPureUpper using (pure-upper; readD)
open import OCF.Align.TotalValueCumulativeAbsorb using (bkᴵ)
open import OCF.Align.TotalValueBuildStrict using (module N)
open import OCF.BTBO using (module Ord-Ord)
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.TotalOrbitRun as R
open import OCF.Align.ValueJudgeBase using (_≼_)

omega-upper : ∀ {m c φ χ w ℓ η}
  (h : HS (P.ψ⁰ (P.Ω η)))
  (cv : ∀ {L} → Ev L φ → Simᴵ η L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  A.read (R.run (toZ (ψ̄ᵠ ok env
    (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ η)) ev p))) ≼
  readD (Ord-Ord.ordᴰ (bkᴵ (toLevel (P.ψ⁰ (P.Ω η)) h)))
omega-upper {η = η} h cv ok env ev p = pure-upper h
  (pure-right (B.omega-read cv ok env ev p)
    (≅-sym (P.ψ⁰≅ψ {p = p} {σ = cv ev} (P.Ω-refl η))))

-- 原 NoCumsum 的全部反馈参数，HS 证书由原 cert 实填。
original-step-upper : ∀ n {m c φ χ w ℓ}
  (cv : ∀ {L} → Ev L φ → Simᴵ (N.L n) L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  A.read (R.run (toZ (ψ̄ᵠ ok env
    (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ (N.L n))) ev p))) ≼
  readD (Ord-Ord.ordᴰ (bkᴵ (N.L (suc n))))
original-step-upper n = omega-upper (N.cert (suc n))
```

原轨道参数及其合法性已经实填；环境仍按原 tl 的真实类型量化，
不能把它省成任意低公共源。该上界不需要额外 SV 前提，SV 是之后
将累计层吸入再一次 ψΩ 的实际前提。原 NoCumsum 全族提供 SV-L，
但它不等于 EBO 全塔或最高端行本身。
