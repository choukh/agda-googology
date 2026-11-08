# 与记号无关的树侧一步变换

只读取输入Cd树，不读取HS、标签或参照γ。raw运行原消费者，tree由
原leg完成为合法树；这个名字不声明与记号γ下一步同值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaGammaTreeIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.LHRecTy using (LH; lz; ls)
open import OCF.Lean.LHRecLay using (_⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL)
import OCF.Lean.GeneralOmegaConsumeRun as R

level : Cd → LH
level c = ls lz ⊕L upL lz c
raw : Cd → Cd
raw c = R.run (level c) (flL (level c))
tree : Cd → Cd
tree c = leg (raw c)
legal : ∀ c → LgB (tree c)
legal c = Lg-leg (raw c)
```
