# 原 base 全回调的可回灌输出嵌入

本篇把同参数的值下界加强成整个前驱域的有界嵌入。源参数带 SV 与
非零构造形状；这两项在原 NC 全反馈轨道上已有实填。世界与地板仍是
原运行器的实际参数，不声称任意参数都有默认公共环境。异参数的
ψ 输出嵌入和整高行反馈同步仍是独立义务。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseEmbedding (S : HtB) where
open import Data.Nat using (ℕ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ; Ωˢ; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Align.LadderOrdTree S
import OCF.Align.OrdLabZLevel as P
open import OCF.Align.OrdLabZPrefix using (_~_; z~; s~; l~; lᵢ~; upˡ; upʳ)
open import OCF.Align.TotalValueBuildIf using (BoundedEmbedding)
open import OCF.Align.TotalValueBuildStrict using (SV; Pos; St-F; SV-toLevel; module N; SV-L; pos-L)
open import OCF.Align.TotalValuePureEmbedding using (pure-embedding)
import OCF.Align.TotalValueBuildBaseRead S as B
import OCF.Free.TotalOrbitRun as R

pure-right : ∀ {x : Ordˢ zero} {y z : Ordᶜ zero} → x ~ y → y ≅ z → x ~ z
pure-right z~ z≅ = z~
pure-right (s~ r) (s≅ e) = s~ (pure-right r e)
pure-right (l~ r) (l≅ e) = l~ (λ n → pure-right (r n) (e n))
pure-right (lᵢ~ {p = ()} e r) q
pure-right (upˡ {r = ()} r) q
pure-right (upʳ {r = ()} r) q

omega-embedding : ∀ {m c φ χ w ℓ η}
  (sv : SV η) (pos : Pos η) (h : HS (P.ψ⁰ (P.Ω η)))
  (cv : ∀ {L} → Ev L φ → Simᴵ η L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  BoundedEmbedding (toLevel (P.ψ⁰ (P.Ω η)) h)
    (R.run (toZ (ψ̄ᵠ ok env (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ η)) ev p)))
omega-embedding {η = η} sv pos h cv ok env ev p =
  pure-embedding h (SV-toLevel _ h (St-F sv pos))
    (pure-right (B.omega-read cv ok env ev p)
      (≅-sym (P.ψ⁰≅ψ {p = p} {σ = cv ev} (P.Ω-refl η))))

-- 全部原反馈参数；不是仅首个纯树样本。
original-step : ∀ n {m c φ χ w ℓ}
  (cv : ∀ {L} → Ev L φ → Simᴵ (N.L n) L)
  (ok : Ok w) (env : Eh h₀ m w χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
  BoundedEmbedding (N.L (Data.Nat.suc n))
    (R.run (toZ (ψ̄ᵠ ok env
      (tl {m = m} {c = c} {χ = χ} φ cv (Ωˢ (N.L n))) ev p)))
original-step n = omega-embedding (SV-L n) (pos-L n) (N.cert (Data.Nat.suc n))
```
