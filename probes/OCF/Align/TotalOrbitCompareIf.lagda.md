# 固定累计解释器与旧计值的比较合同

只比较冻结算法在同一 Z 输入上的值。Goodᴺ 是旧侧实际证书，
不进入新解释器定义。两个合同均量化全部裸程序，不代表 Ω̇ 生成域。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.TotalOrbitCompareIf where
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force using (Goodᴺ; forceᴺ)
open import OCF.Align.ValueJudgeBase using (_≼_; _≈ᵛ_)
import OCF.Free.TotalOrbitBuild as A

record SameValue : Set where
  field
    same : ∀ x (G : Goodᴺ x) → forceᴺ x G ≈ᵛ A.tree x

record OldLower : Set where
  field
    lower : ∀ x (G : Goodᴺ x) → forceᴺ x G ≼ A.tree x
```
