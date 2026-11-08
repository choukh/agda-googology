# 原可数高度运行器的全有限一致性

验收专用。将真实cl/dcl/cmpB分类实例填入异族模拟，下面全部结论
不再带Classification假设。num n上的leg、合法证书和零路径已经
由Normalize逐字规范化；没有改变新运行器的ℕ高度累计地板。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteAll where
open import OCF.Lean.CRwBase using (Cd; hl)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num)
import OCF.Lean.GeneralOmegaCountableObserveClosed as C
import OCF.Align.GeneralOmegaGammaCoverFinite as F
import OCF.Align.GeneralOmegaGammaActual as G
open import OCF.Align.GeneralOmegaCountableFiniteClass using (instance-classification)
import OCF.Align.GeneralOmegaCountableFiniteWhole as W

open W.Bridge instance-classification public

-- 原Γ的全部数值参数输出；不是原Γ迭代stage的改名。
raw-family : Cd
raw-family = hl (λ n → C.rawΓ (num n))
first-callback≤family : G.reference-branch 0 ≤ᵛ raw-family
first-callback≤family = ≤-trans F.first≤finite
  (l≤ (λ n → ≤l n (reference≤raw n)))
family≤first-callback : raw-family ≤ᵛ G.reference-branch 0
family≤first-callback = ≤-trans (l≤ (λ n → ≤l n (raw≤reference n))) F.finite≤first
```

无条件导出raw-same全n（原rawΓ(num n)与Finite.stage n结构对应）、
raw≤finite/finite≤raw、reference≤raw/raw≤reference及reference≤Γ。
因此每个原rawΓ(num n)的序数值是ψ₀(Ω_n)，原合法Γ(num n)不低于
该参照。整参数族的原raw极限与γ₂首回调互相≤ᵛ。

本篇没有证明原Γ迭代闭项C.tree覆盖这些输入；更没有证明Γ保值单调。
ℕ高度的累计floor与原记号逐点floor不同，下一步必须在真实回调里
证明相应值界，不能把本篇有限一致性推广为任意Cd高度的一致性。
