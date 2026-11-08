# 原 Third 的有界目标运行族：共享接口

源树、源合法高度和世界固定；目标带同一源高度下的实际第一位置。
每个目标仍接收它自己的原 GT 种子。这里的精确性字段逐字引用旧 Φ，
并实例原 Er；不改变洗法。Sh 只保证 ℕ 构造的步进，不当成高层 LgB。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRunFamilyIf where
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTw using (Sb)
import OCF.Lean.ThirdFold as Fold
import OCF.Lean.ThirdSan as San

module Source (n : ℕ) (w : Wd (Sb n)) (lw : LgW (Sb n) w)
  (fb : HB (Sb n)) (M : HB (Sb n)) (lm : LgB M) where
  module F = Fold (Sb n) w lw
  module E = San (Sb n) w lw fb
  record RunFamily (h : HB (F.T M)) (nd : F.Gd M h) : Set where
    field
      run : ∀ t → t ⊲[ w ] M → F.GT t → F.GT t
      exact : ∀ t pt b → run t pt b ≡ F.F.Φ E.Er M (F.F.wfC E.Er M) lm t pt b h nd
      shape : ∀ t pt b → F.F.Sh E.Er (proj₁ (run t pt b))
```

精确字段排除常值替身。接口不要求界外目标的输出，也不要求不同路径
证明的运行相等。高层合法化与运行后局部界更新在实际实例中另给。
