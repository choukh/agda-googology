# YiXVReadKeepLinkInput
> 验收文件。档位：编译定理。保留回调的实际槽位等式与输入搬运接口，含保留、对角实例。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadKeepLinkInput where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadSlots as Slots
import OCF.Lean.YiXVReadWholeInput as Whole
import OCF.Lean.YiXVReadPaths as P

record Link (cur : S.Tr S.zero) (p : S.Pos⁼ (J.ℓ cur)) (y : S.Tr S.zero)
  (q : S.Pos (J.ℓ y)) (cv : S.Br (J.ℓ y) q → S.Br⁼ (J.ℓ cur) p) : Set where
  constructor link
  field
    same : J.slot y q ≡ Whole.slot cur p
    pull : ∀ a X → U.Fam y q a X → Whole.Rel cur p (cv a) (Slots.cast same X)

model-keep : Link (S.suc S.zero) (inj₂ (inj₁ tt)) (S.suc S.zero) (inj₁ tt) (λ a → a)
model-keep = link refl (λ a X h → h)
model-diag : S.zero P.≤ᵀ Whole.slot S.zero (inj₁ tt)
model-diag = P.here
```
