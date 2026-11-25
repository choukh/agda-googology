# YiXVCountableRetain
> 验收文件。档位：编译定理。原保留分支由字面代表等式给回搬接口，沿用原 tr⁻。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableRetain where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableMapInput as V
import OCF.Lean.YiXVCountableTransportInput as Q
import OCF.Lean.YiXVCountableTransport as T
import OCF.Lean.YiXVCountablePull as P
pull : ∀ {κ ν i j} (q : i L.<ᴵ κ) (r : j L.<ᴵ ν) (e : i L.≅ᴵ j) → i ≡ j → V.Pull {κ} {ν} q
pull q r e same = P.make q (L.restr e r (L.tr⁻ e)) same bk (λ X → refl)
  (L.tr⁻-≅ e (L.Ω-≅ (L.≅ᴵ-sym e))) (λ gx → L.tr⁻-≅ e (A.self gx))
  where
  bk : P.Back (L.restr e r (L.tr⁻ e))
  P.Back.good bk = Q.Ops.minus-good (T.ops e same)
  P.Back.mono bk = Q.Ops.minus-mono (T.ops e same)
actual : V.Pull {L.suc L.zero} {L.suc L.zero} L.zero
actual = pull L.zero L.zero L.z≅ refl
```
