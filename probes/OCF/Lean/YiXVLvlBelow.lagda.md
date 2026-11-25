# YiXVLvlBelow
> 验收文件。档位：编译定理。原 lvl 的每个字面前驱都有源第一位置前驱及字面下标等式。
> 按 YiLSRead.St≺/st-dn/lt≺ 与 Level.sim/<ᴵ-dec 的现有计算证明；未交可数层折叠闭包或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVLvlBelow where
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L

record Below (x : S.Tr S.zero) {i} (q : i L.<ᴵ T.lvl x) : Set where
  constructor below
  field
    source : S.Tr S.zero
    same : i ≡ T.lvl source
    step : S.zero S.⊢ source ◃ x
cut : ∀ x {i} (q : i L.<ᴵ T.lvl x) → Below x q
cut S.zero ()
cut (S.suc x) L.zero = below x refl S.◃s
cut (S.suc x) (L.suc q) = below (Below.source old) (Below.same old) (S.◃t (Below.step old) S.◃s)
  where old = cut x q
cut (S.lim f a) (L.lim n q) = below (Below.source old) (Below.same old) (S.◃t (Below.step old) (S.◃l n))
  where old = cut (f n) q
cut (S.Ω () g) q
cut (S.up x () y e) q
```
