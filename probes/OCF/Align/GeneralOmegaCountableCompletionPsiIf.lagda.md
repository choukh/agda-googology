# canonical Ω折叠在固定输入完成下的有向值接口

这是验收接口，不改树、折叠或证书。源只需旧HS，不额外假设其
遗忘树字面合法；原γ₁具备此证书。结论直接比较零层输出的值，
没有要求两个不同层索引三歧、相等或旧前驱包含。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableCompletionPsiIf where
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B

record CompletionPsiLower : Set₁ where
  field
    lower : ∀ (t : L.Ordᶜ L.zero) (h : L.HS t) →
      B.forget (L.ψ⁰ (L.Ω (L.toLevel t h))) ≤ᵛ
      B.forget (L.ψ⁰ (L.Ω (height (leg (B.forget t)) (Lg-leg (B.forget t)))))
```

这个字段尚待构造或否定。必须分别交真实非有限实例及整个字段
的结论；已有输入膨胀、外层重索引或高层值同余不能代填。两次
完成的目标运输也必须实际编译，不能由纸面串接直接宣称γ₂下界。
