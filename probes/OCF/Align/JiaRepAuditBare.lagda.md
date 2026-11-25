# 关系式码树对应审查：最小正规 Ω 排除裸 ψ 码

这是 S1 第三轮的限定否定，沿用原 `JiaBase`、`JiaFold` 与冻结的 `JiaRep`。
最小正规 Ω 的树侧折叠走相等层的最小不动点分支，其第零项字面为零。
裸记号码 ψ₀(Ω) 的第零基本列为 ψ₀(1)=ω，故两者不能满足逐基本列关系。
结论对任意种子成立，不以一个不正确的种子实例充当反例。

本篇只否定把码侧对应运算选为裸 ψ 符号。作者允许自定码侧对应运算；
因此它不否定该设计，也不修改树族或要求给原始树补码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRepAuditBare where

open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
open import OCF.Align.EboLeanDef using (T; ψ; Ωt; Ωs)
open import OCF.Align.EboLeanBase using (n[])
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase using (Seeds; Tree; below; module Layer)
open import OCF.Align.JiaFold using (regular; module Fold)
open import OCF.Align.JiaRep using (Rep; module RelLayer)

one omega bare : T
one = Ωt []
omega = Ωs []
bare = ψ [] omega ∷ []

zero-not-omega : ∀ (a : Acc′ []) → Rep a Layer.z (ψ [] one ∷ []) → ⊥
zero-not-omega a ()

no-bare-regular : ∀ (seeds : Seeds) (a₁ : Acc′ one) (a₀ : Acc′ []) →
  Rep a₀
    (Fold.ψ seeds a₁ a₀ (below n[] OCF.Align.EboLeanDef.[]<)
      (regular a₁ n[]))
    bare → ⊥
no-bare-regular seeds (acc h₁) (acc h₀) (RelLayer.rl e branches) =
  zero-not-omega (acc h₀) (branches 0)
```

`one` 是树族的第 1 层，`regular a₁ n[]` 是其中按零层原始树分支的
正规 Ω；定理没有改窄它的分支域。树侧根的零项由 `lfp` 的定义给出，
不需展开可及证明、计算种子或比较低层树。
