# 保留节点的实际异合法证坐标回送

源端使用原cl的to，目标端使用原along/frA。两端低层是同一原i，
其合法证可以不同；实际层同构E不要求与规范证明相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedKeepCoord where
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; module C)
open import OCF.Lean.BoundedDiagonalSame using (same-refl)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; height-shape)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedClass
open import OCF.Align.GeneralOmegaCountableTypedAlong
open import OCF.Align.GeneralOmegaCountableTypedProofVia using (transport-via)

index-equal : ∀ {j k} → j ≡ k → j L.≅ᴵ k
index-equal {j} refl = L.≅ᴵ-refl j

feed-casts : ∀ i l₁ l₂ {j k : L.Ordᴵ} {A D : Set}
  (Q₁ : L.Ordᶜ j → A → Set) (Q₂ : L.Ordᶜ k → D → Set)
  (eq₁ : j ≡ height i l₁) (eq₂ : k ≡ height i l₂)
  (encode : HB (F i) → A) (fr : D → HB (F i)) →
  (∀ {x e} → Read i l₁ (canonical i l₁) x e → Q₁ (cast (sym eq₁) x) (encode e)) →
  (∀ {x e} → Q₂ x e → Read i l₂ (canonical i l₂) (cast eq₂ x) (fr e)) →
  (E : j L.≅ᴵ k) → ∀ {x e} → Q₂ x e → Q₁ (L.tr⁻ E x) (encode (fr e))
feed-casts i l₁ l₂ Q₁ Q₂ refl refl encode fr put get E r =
  put (transport-via i l₁ l₂ E (get r))

keep-shape : ∀ {B : Cd} {lB κ i pi encode} →
  ClassLink B lB κ (C.nw i pi encode) → ∀ {t} lt (p : hs i ⊲ t) →
  rank B lB κ L.≅ᴵ rank t lt (C.along p)
keep-shape {lB = lB} {i = i} {pi = pi} (linked eq feed) lt p =
  L.≅ᴵ-trans (index-equal eq)
    (L.≅ᴵ-trans (height-shape (same-refl i) (lgB⊲ pi tt lB) (lgB⊲ p tt lt))
      (index-equal (sym (along-rank p lt))))

keep-move : ∀ {B : Cd} {lB κ i pi encode} →
  ClassLink B lB κ (C.nw i pi encode) → ∀ {t} lt (p : hs i ⊲ t)
  (E : rank B lB κ L.≅ᴵ rank t lt (C.along p)) {x e} →
  Coord t lt (C.along p) x e → Coord B lB κ (L.tr⁻ E x) (encode (C.frA p e))
keep-move {B} {lB} {κ} {i} {pi} {encode} (linked eq feed) lt p E =
  feed-casts i (lgB⊲ pi tt lB) (lgB⊲ p tt lt)
    (Coord B lB κ) (Coord _ lt (C.along p)) eq (along-rank p lt)
    encode (C.frA p) feed (along-read p lt) E
```
