# YiWBNeg 的反例对象在 N 下通过
不读记号；编译定理，无前提：`YiOGSelf.left ≼ YiOGSelf.right` 在 `YiRRRel.N` 里成立（`left-right`），所以 `source-carry ≼ target-carry` 也成立（`carry`）；`Le`、`W` 下这一对不成立（`YiOGSelf.no-self-transfer`, `YiWBNeg.no-carry-w`）。
证法照 `YiWBNeg.val-left-right`：在 `right` 里第 1 层槽位的结点处用 `≼W`，入口是 `Ωt L1`（`entry`），入口之上的分支 z′ 处由 `Up≼` 给出 `left ≼ Up … z′`。
不否定什么；底前提的完整实例在 [YiRRTwo](YiRRTwo.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRRPair where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (subst; subst₂; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (self)
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiOGSelf as Self
import OCF.Lean.YiOGFold as Fold
import OCF.Lean.YiWBNeg as WN
open import OCF.Lean.YiRRRel

L2 : L
L2 = nd sS (λ _ → L1)

d₁ : Dn L2 L1
d₁ = down stop tt
```

`right` 里第 1 层槽位的结点逐字是 `Ω p₁ (λ z → next⁺ (Up L1 d₁ (Ωt L2) z))`.

```agda
node-in : N L2 (proj₁ WN.leftT) (proj₁ (Fold.ψ L2 Self.Hi.oa (F.B₀ L2) L2 self (Ωt L2) (proj₁ (Ωt L2))))
node-in = ≼W (proj₁ (Ωt L1)) (entry L1 tt) (λ z′ r → ≼l 0 (Up≼ L1 d₁ (Ωt L2) (Ωt L2) (Ωt≼ L2 tt) r))

in-P : N L2 (proj₁ WN.leftT) (proj₁ (WN.Pc (proj₁ (next⁺ (Ωt L2)))))
in-P = ≼l 0 (≼l 0 node-in)

left-right : N L2 (proj₁ Self.left) (proj₁ Self.right)
left-right = subst₂ (λ x y → N L2 (proj₁ x) (proj₁ y)) (sym Self.left-form) (sym Self.right-form)
  (subst (λ t → N L2 (proj₁ WN.leftT) t) (sym Self.Hi.value-row)
    (≼l 1 (right-add (subst (λ t → N L2 (proj₁ WN.leftT) (proj₁ (WN.Pc t))) (sym WN.tick-zero) in-P)
      (proj₁ (Self.Hi.piece 0)))))

carry : N L2 (proj₁ Self.source-carry) (proj₁ Self.target-carry)
carry = subst₂ (λ x y → N L2 (proj₁ x) (proj₁ y)) (sym Self.source-carry-two) (sym Self.target-carry-two) left-right
```
