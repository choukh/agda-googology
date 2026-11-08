# 真实γ提升的局部值验收接口

本篇允许记号导入，仅用于研究验收。source不进入原code、闭项或其
证书；它是对一种直接比较方案的探测对象，不要求最终覆盖必须同站。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaGammaIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.LHRecTy using (LH; lz; ls; Lv)
open import OCF.Lean.LHRecLay using (_⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B

source : L.Ordᶜ L.zero → LH
source t = ls lz ⊕L upL lz (B.forget t)
reference : ∀ t → L.HS t → Cd
reference t h = B.forget (L.ψ⁰ (L.Ω (L.toLevel t h)))
candidate : L.Ordᶜ L.zero → Cd
candidate t = run (source t) (flL (source t))

record Comparison (t : L.Ordᶜ L.zero) (h : L.HS t) : Set where
  field
    lower : reference t h ≤ᵛ candidate t
```

Comparison只对指定t提出大小方向，不假设所有t都可填。t=1的非空
实例另篇实现；γ₂是否满足此同源方案尚未知。最终Λ验收允许把原阶段
送入更高新阶段，不以此接口的困难否定错位覆盖。
