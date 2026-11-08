# 可数树完成接口

这个备选把任意可运行的raw可数树完成为合法树，并要求保留raw值下界。
原raw树与完成树是两个定义；接口不要求同值或统一值上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CountableCompletionIf where
open import OCF.Lean.CRwBase using (Cd; LgB)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

record Completion : Set₁ where
  field
    complete : Cd → Cd
    lawful : ∀ a → LgB (complete a)
    lower : ∀ a → a ≤ᵛ complete a
```

这不是序数值同余接口，也不证明raw树相同值时完成树有相同值。
实际实例和原生下降闭项由后续文件给出；接口不替代具体终点验收。
