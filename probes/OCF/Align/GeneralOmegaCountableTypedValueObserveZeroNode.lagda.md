# 辅助逐点解释器的原零目标分派

只展开真实分类，不比较零路径证明。same保留调用处pt，above保留
原秩反馈路径；这为任意root零路径的递归提供归约式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueObserveZeroNode where
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableNextCapturePointIf using (point-node)
open import OCF.Lean.GeneralOmegaCountableObserveZeroPath using (zero-decision)

pick-zero : ∀ {B A} (i : Cd) (pi : hs i ⊲ B) (to : HB (F i) → A)
  (r : (hz ⊲ hs i) ⊎ (hs i ⊲ hz)) (pt : hz ⊲ B)
  (rec : ∀ j → j ⊲ B → A → HB (F j)) →
  point-node pt (C.pick S⊥ to pi r) rec ≡ point-node pt (zero-decision i pi to) rec
pick-zero hz pi to (inj₁ (hsuc hself)) pt rec = refl
pick-zero (hs i) pi to (inj₁ (hsuc (hsuc p))) pt rec = refl
pick-zero (hl f) pi to (inj₁ (hsuc (hlim n p))) pt rec = refl
pick-zero (hΩ () f) pi to r pt rec
pick-zero i pi to (inj₂ ()) pt rec

normal-point-node : ∀ {B κ} (pt : hz ⊲ B) → C.Cl {S⊥} B κ →
  (∀ j → j ⊲ B → E (F B) κ → HB (F j)) → Cd
normal-point-node pt (C.bas () to) rec
normal-point-node pt (C.nw i pi to) rec = point-node pt (zero-decision i pi to) rec

normalize-point-node : ∀ {B κ} lB (pt : hz ⊲ B) (v : C.Cl {S⊥} B κ)
  (rec : ∀ j → j ⊲ B → E (F B) κ → HB (F j)) →
  point-node pt (C.dcl pt lB v) rec ≡ normal-point-node pt v rec
normalize-point-node lB pt (C.bas () to) rec
normalize-point-node lB pt (C.nw i pi to) rec = pick-zero i pi to (cmpB pi pt _ lB) pt rec

```
