# 用坐标加法保存初始中槽

这是验收侧的新编码，不改变原树、原双槽解释器或闭项。
中Ω的分支同时把捕获中槽加到访问坐标与递归中槽；底Ω仍逐枝递归。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldRebaseIf where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V)

enc : HB U → HB V → HB V
enc b hz = hz
enc b (hs a) = hs (enc b a)
enc b (hl f) = hl (λ n → enc b (f n))
enc b (hΩ (inj₁ (inj₁ ())) g)
enc b (hΩ (inj₁ (inj₂ _)) g) = hΩ (inj₁ (inj₂ tt)) (λ c → enc b (g c))
enc b (hΩ (inj₂ _) g) = hΩ (inj₂ tt) (λ e → enc (b ⊞ e) (g (b ⊞ e)))
```

此处只定义编码，不宣称它保合法或已被实际主线覆盖。
