# 纯读取保留整个前驱嵌入，而非只保值下界

源的遗传严格边界用于合并重叠极限支。该前提由实际旧折叠的严格性
模块提供，不能用任意 HS 替代。目标是完整新 run 的坐标类型。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValuePureEmbedding where
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ; toZ)
open import OCF.Align.OrdLabZPrefix using (_~_; z~; s~; l~; lᵢ~; upˡ; upʳ)
open import OCF.Align.TotalValueBuildIf
open import OCF.Align.TotalValueEmbeddingOps using (identity; widen; successor)
open import OCF.Align.TotalValueBuildStrict using (SV; svz; svs; svl)
import OCF.Align.TotalValueTailEmbedding as L
import OCF.Free.TotalOrbitRun as R

pure-embedding : ∀ {x : Ordˢ zero} {y : Ordᶜ zero} (hy : HS y) →
  SV (toLevel y hy) → x ~ y → BoundedEmbedding (toLevel y hy) (R.run (toZ x))
pure-embedding hy svz z~ = widen (identity zero) z⊑
pure-embedding hy (svs ds) (s~ p) = successor (pure-embedding (hs⁻ hy) ds p)
pure-embedding hy (svl ds st) (l~ {f = f} {g = g} p) =
  L.Assemble.embedding {f = λ n → toLevel (g n) (hl₁ hy n)}
    {s = λ n → toLevel-⊑ (hl₁ hy n) (hl₁ hy _) (hl₂ hy n)}
    (λ n → R.run (toZ (f n))) st
    (λ n → pure-embedding (hl₁ hy n) (ds n) (p n))
pure-embedding hy ds (lᵢ~ {p = ()} e p)
pure-embedding hy ds (upˡ {r = ()} p)
pure-embedding hy ds (upʳ {r = ()} p)
```
