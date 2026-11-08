# 实际反馈坐标的有界累计嵌入

本接口沿用 BTBOFull.PEmb 的前驱嵌入口径，但对象逐字是新解释器的
Free.Level 层号。每一对被比较的下标均带源界内的前驱证据；不声明
裸回调单调，也不把这种嵌入自动送入任意 Z 闭包。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildIf where
open import OCF.Free.Level
import OCF.Free.TotalOrbitRun as R

record BoundedEmbedding (a b : Ordᴵ) : Set where
  field
    map : ∀ {d} → d ≺ᴵ a → Ordᴵ
    bound : ∀ {d} (p : d ≺ᴵ a) → map p ≺ᴵ b
    ordered : ∀ {d e} (p : d ≺ᴵ a) (q : e ≺ᴵ a) →
      d ≺ᴵ e → map p ≺ᴵ map q
    coherent : ∀ {d e} (p : d ≺ᴵ a) (q : e ≺ᴵ a) →
      d ≅ᴵ e → map p ≅ᴵ map q

record CumulativeEmbedding : Set where
  field
    cumulative : ∀ c a → BoundedEmbedding a (R.add c a)
```

这是新增界造成的坐标变化的一个实填结构事实，不是完整值合同。
原高源回调是否保持该嵌入，以及输出比较，仍需独立证明。
