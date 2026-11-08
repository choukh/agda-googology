# 一步折叠的总构造

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerCollapseRun where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf

module Run (S : KS) where
  open Ops S
  fold : HB (step S) → HB S
  fold hz = hs hz
  fold (hs a) = repeat (fold a)
  fold (hl f) = sum (λ n → fold (f n))
  fold (hΩ (inj₁ κ) g) = hΩ κ (λ c → fold (g c))
  fold (hΩ (inj₂ _) g) = collapse (λ c → fold (g c))

  instance-fold : Collapse S
  instance-fold = record
    { fold = fold ; at-zero = refl ; at-suc = λ a → refl
    ; at-lim = λ f → refl ; keep = λ κ g → refl ; remove = λ g → refl }
```

终止依输入树：即便分支坐标由先前输出生成，递归仍进入 g 的子树。
未给任意 S 的合法性定理，也没有据此声称 ψ₀Λ。
