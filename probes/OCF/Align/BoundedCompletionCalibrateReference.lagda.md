# 校准参照的既有记号标签

本篇明确属于记号验收层。使用既有Correspond.ε₀-label，不新定义树或标签。
OCFSpecAnchor的ε₀锚点与该带标签参照在此处由检查器核对为同一树。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionCalibrateReference where
open import OCF.Align.Level using (Ordᶜ; zero)
import OCF.Align.OCFSpecAnchor as A
import OCF.Align.Correspond as C
import OCF.Align.NoCumsum as N
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

reference : Ordᶜ zero
reference = A.ε₀
same-reference : reference ≡ N.γ 1
same-reference = refl
reference-label : C.Lab reference (C.γᴱ 1)
reference-label = C.ε₀-label
```

γᴱ1就是既有Correspond定理的ψ₀(Ω₁)=ε₀项。这里只确定参照资格，
实际Fold1.TΩ1与此参照的值比较在其他校准文件完成，不由本篇预设。
