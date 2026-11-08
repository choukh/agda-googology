# 值不等式在下一次折叠内提升成完整前驱嵌入

不直接逆射裸值序。两侧有遗传严格边界；先进入累加层号、再用原
分块值比较、最后把累加前驱吸收到目标的下一次 ψ⁰Ω 折叠内。
这是错位回灌中允许多走一步的精确代价。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueCumulativeLift where
open import OCF.Free.Level
open import OCF.Align.OrdLabZLevel using (ψ⁰; Ω)
open import OCF.Align.TotalValueBuildIf
open import OCF.Align.TotalValueEmbeddingOps using (compose)
open import OCF.Align.TotalValueBuildStrict using (SV; St-≅)
open import OCF.Align.TotalValueBuildReadStrict using (read-strictness)
open import OCF.Align.ValueJudgeBase
import OCF.Free.TotalOrbitBuild as A
import OCF.Align.TotalValueCumulativeBase as B
import OCF.Align.TotalValueCumulativeInto as I
import OCF.Align.TotalValueCumulativeAbsorb as V
import OCF.Align.TotalValueCumulativeEb as E
import OCF.Align.TotalValueBuildTypedEmbedding as P

read-back : ∀ a → B.tr₀ (V.bkᴵ a) ≅ A.read a
read-back zero = z≅
read-back (suc a) = s≅ (read-back a)
read-back (lim f st) = l≅ (λ n → read-back (f n))

from-typed : ∀ {a b} → P.PEmb a b → BoundedEmbedding a b
from-typed e = record
  { map = P.PEmb.map e ; bound = P.PEmb.bnd e
  ; ordered = P.PEmb.mono e ; coherent = P.PEmb.coh e }

lift : ∀ a b → SV a → SV b → (h : HS (ψ⁰ (Ω b))) →
  A.read a ≼ A.read b → BoundedEmbedding a (toLevel (ψ⁰ (Ω b)) h)
lift a b sa sb h v = compose (from-typed (I.PW₃ (I.V1 sa)))
  (compose (from-typed (I.PW₁ (E.V2 (V.bkᴵ a) (V.bkᴵ b)
    (St-≅ (read-back a) (read-strictness sa))
    (St-≅ (read-back b) (read-strictness sb))
    (≼-trans (≅→≼ (read-back a)) (≼-trans v (≅→≼ (≅-sym (read-back b))))))))
    (from-typed (I.PW₂ h (V.V3 sb))))
```

此结论的目标比 b 多了一次 ψ⁰Ω，不是原来未证的一般值序反射。
自然数/原 NC 轨道的 SV 已有实际实例；使用时仍须给目标折叠的 HS。
