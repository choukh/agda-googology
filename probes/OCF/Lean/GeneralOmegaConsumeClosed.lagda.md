# 完整ΛL源地板的合法可数实验闭项

这里交付原完整源地板经新总解释器产生的合法树及树上FGH。源名ΛL
不等于输出值已验收为ψ₀Λ；输出大小另列，不能由类型名替代证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaConsumeClosed where
open import Data.Nat using (ℕ)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.LHRecLay using (ΛL)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.CountableCompletionRun using (inflation)
import OCF.Lean.GeneralOmegaConsumeRun as R
import OCF.Lean.Fold1 as F

raw : Cd
raw = R.run ΛL (flL ΛL)
tree : Cd
tree = leg raw
legal-tree : LgB tree
legal-tree = Lg-leg raw
raw-lower : raw ≤ᵛ tree
raw-lower = inflation raw
fgh : ℕ → ℕ
fgh = F.FGH tree
```

无参数、无假设，源是原ΛL的全部地板，不是有限截断。中间输出已经
是Cd，完成后是标准合法布劳威尔树。定义闭包必须通过记号无关审计。
目前未给EBO下界、上界或同值，亦未给C、D的比较。

翻译账：复用旧LH与ΛL源族，仍受记号启发；新算法不复制任何阶段的
基本列规则，所有Ω一条规则。坐标取低层地板加纯反馈是主动选择，
既不是树侧唯一性结论，也不算已让树自足。
