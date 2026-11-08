# 原事件返回合同的校准

只按读回层以下的实际位置消去，不判定两个任意高度。
这不是新增第三种事件的读回；它明确原合同能够实填的范围。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnBuild where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnIf

drop-at : ∀ κ {a H H′ t} → t ⊲[ a , H ] RLay κ →
          D t (a , H) → D t (a , H′)
drop-at (_ , hself) hself x = drp₂ x
drop-at (_ , hself) (hsuc hself) x = drp₁ x
drop-at (_ , hself) (hsuc (hsuc hself)) x = drp x
drop-at (_ , hsuc hself) hself x = drp₁ x
drop-at (_ , hsuc hself) (hsuc hself) x = drp x

actual : ∀ κ → ReturnAt κ
actual κ = record
  { read = RB κ
  ; read-exact = λ _ _ → refl
  ; event = evRB κ
  ; event-exact = λ _ _ → refl
  ; move = λ _ _ _ p x → drop-at κ p x }
```
