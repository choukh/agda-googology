# YiXVCountableTransportInput
> 验收文件。档位：编译定理。字面端点相等条件下的正反向搬运接口。
> 推广 YiXVFiniteFamily/Level 的结构递归；共享映射证明供搬运与加法复用。未证明可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableTransportInput where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A

record Ops {a b} (e : a L.≅ᴵ b) (same : a ≡ b) : Set where
  field
    good : ∀ {X} → A.Gd X → A.Gd (L.tr e X)
    mono : ∀ {X Y} → A.Le X Y → A.Le (L.tr e X) (L.tr e Y)
    minus-good : ∀ {X} → A.Gd X → A.Gd (L.tr⁻ e X)
    minus-mono : ∀ {X Y} → A.Le X Y → A.Le (L.tr⁻ e X) (L.tr⁻ e Y)
```
