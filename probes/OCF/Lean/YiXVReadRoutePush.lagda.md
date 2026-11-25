# YiXVReadRoutePush
> 验收文件。档位：编译定理。原 psh/pshBr 沿 Route 搬运时，保留实际槽位对象与分支模拟。
> 跟踪 YiLegPath 的原计算；不改树、折叠、UR、比较器。未交完整极限／节点世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRoutePush where
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadSlots as Slots
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadOmegaInput as Ω
import OCF.Lean.YiXVReadWholeInput as Whole

suc-slot : ∀ r (p : S.Pos⁼ (J.ℓ r)) → J.slot (S.suc r) p ≡ Whole.slot r p
suc-slot r (inj₁ t) = refl
suc-slot r (inj₂ p) = refl
lim-slot : ∀ (f : ℕ → S.Tr S.zero) (d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)) n (p : S.Pos⁼ (J.ℓ (f n))) →
  J.slot (S.lim f d) (n , p) ≡ Whole.slot (f n) p
lim-slot f d n (inj₁ t) = refl
lim-slot f d n (inj₂ p) = refl
suc-pull : ∀ r (p : S.Pos⁼ (J.ℓ r)) a X → U.Fam (S.suc r) p a X →
  Whole.Rel r p a (Slots.cast (suc-slot r p) X)
suc-pull r (inj₁ t) a X h = h
suc-pull r (inj₂ p) a X h = h
lim-pull : ∀ (f : ℕ → S.Tr S.zero) (d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)) n (p : S.Pos⁼ (J.ℓ (f n))) a X →
  U.Fam (S.lim f d) (n , p) a X → Whole.Rel (f n) p a (Slots.cast (lim-slot f d n p) X)
lim-pull f d n (inj₁ t) a X h = h
lim-pull f d n (inj₂ p) a X h = h

slot : ∀ {top y v} (rv : R.Route top y v) (p : S.Pos⁼ (J.ℓ y)) →
  Whole.slot top (P.psh v p) ≡ Whole.slot y p
slot R.here p = refl
slot (R.ins {r = r} {v = v} rv) p = trans (suc-slot r (P.psh v p)) (slot rv p)
slot (R.inl {f = f} {d = d} n {v = v} rv) p = trans (lim-slot f d n (P.psh v p)) (slot rv p)
slot (R.inlu {f = f} {d = d} {vs = vs} rv) p = trans (lim-slot f d 0 (P.psh (vs 0) p)) (slot (rv 0) p)
pull : ∀ {top y v} (rv : R.Route top y v) (p : S.Pos⁼ (J.ℓ y)) a X →
  Whole.Rel top (P.psh v p) a X → Whole.Rel y p (P.pshBr v p a) (Slots.cast (slot rv p) X)
pull R.here p a X h = h
pull {y = y} (R.ins {r = r} {v = v} rv) p a X h =
  subst (Whole.Rel y p (P.pshBr v p a))
    (subst-subst {P = λ r → L.Ordᶜ (T.lvl r)} (suc-slot r (P.psh v p)) {y≡z = slot rv p} {p = X})
    (pull rv p a (Slots.cast (suc-slot r (P.psh v p)) X) (suc-pull r (P.psh v p) a X h))
pull {y = y} (R.inl {f = f} {d = d} n {v = v} rv) p a X h =
  subst (Whole.Rel y p (P.pshBr v p a))
    (subst-subst {P = λ r → L.Ordᶜ (T.lvl r)} (lim-slot f d n (P.psh v p)) {y≡z = slot rv p} {p = X})
    (pull rv p a (Slots.cast (lim-slot f d n (P.psh v p)) X) (lim-pull f d n (P.psh v p) a X h))
pull {y = y} (R.inlu {f = f} {d = d} {vs = vs} rv) p a X h =
  subst (Whole.Rel y p (P.pshBr (vs 0) p a))
    (subst-subst {P = λ r → L.Ordᶜ (T.lvl r)} (lim-slot f d 0 (P.psh (vs 0) p)) {y≡z = slot (rv 0) p} {p = X})
    (pull (rv 0) p a (Slots.cast (lim-slot f d 0 (P.psh (vs 0) p)) X) (lim-pull f d 0 (P.psh (vs 0) p) a X h))

actual-ω : Whole.Rel S.zero (inj₁ tt) S.zero (L.Ω L.zero)
actual-ω = pull R.model-ω (inj₁ tt) S.zero (L.Ω L.zero) Whole.model-ω
```
