# 带高度族解封：目标类型
验收文件；这里只编译下界的类型，不给出目标下界的证明。
`Target` 取自 `CrossMAccept.tψΩ`；其 ψ₀(Ω_{Ω²}) 读法沿用原简报。
`Lower` 要求带逐项标签的参照树存在，并在值序下不高于原 `T⊤`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHFTarget where

open import Data.Product using (Σ; _×_)
open import Data.List using ([]; _∷_)
open import OCF.Free.Level using (Ordᶜ; zero)
open import OCF.Align.EBO using (T; ψ; natT; Ωt; Ωs)
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.ValueJudgeBase using (_≼_)
open import OCF.Align.CrossMClosed using (T⊤)

Target : T
Target = ψ [] (Ωt (ψ (natT 1) (Ωs []) ∷ [])) ∷ []

Lower : T → Set
Lower t = Σ (Ordᶜ zero) λ R → Lab R t × (R ≼ T⊤)

Goal : Set
Goal = Lower Target
```
