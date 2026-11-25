# YiXVReadKeepLink
> 验收文件。档位：编译定理。保留回调证据的复合与后继、极限槽位搬运。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadKeepLink where
open import Data.Nat using (ℕ; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadSlots as Slots
import OCF.Lean.YiXVReadWholeInput as Whole
import OCF.Lean.YiXVReadPaths as P
open import OCF.Lean.YiXVReadKeepLinkInput using (Link; link)

pre : ∀ cur p mid p′ (cv₀ : S.Br⁼ (J.ℓ mid) p′ → S.Br⁼ (J.ℓ cur) p)
  (e : Whole.slot mid p′ ≡ Whole.slot cur p)
  (h₀ : ∀ a X → Whole.Rel mid p′ a X → Whole.Rel cur p (cv₀ a) (Slots.cast e X))
  {y q cv} → Link mid p′ y q cv → Link cur p y q (λ a → cv₀ (cv a))
pre cur p mid p′ cv₀ e h₀ (link same pull) = link (trans same e) λ a X h →
  subst (Whole.Rel cur p (cv₀ _))
    (subst-subst {P = λ r → L.Ordᶜ (T.lvl r)} same {y≡z = e} {p = X})
    (h₀ _ (Slots.cast same X) (pull a X h))

rise-suc : ∀ r p {y q cv} → Link r p y q cv → Link (S.suc r) (inj₂ p) y q cv
rise-suc r (inj₁ t) (link e h) = link e h
rise-suc r (inj₂ p) (link e h) = link e h
rise-lim : ∀ (f : ℕ → S.Tr S.zero) (d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)) m p {y q cv} →
  Link (f m) p y q cv → Link (S.lim f d) (inj₂ (m , p)) y q cv
rise-lim f d m (inj₁ t) (link e h) = link e h
rise-lim f d m (inj₂ p) (link e h) = link e h
diag-suc : ∀ r p {y} → y P.≤ᵀ Whole.slot r p → y P.≤ᵀ J.slot (S.suc r) p
diag-suc r (inj₁ t) h = h
diag-suc r (inj₂ p) h = h
diag-lim : ∀ (f : ℕ → S.Tr S.zero) (d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)) m p {y} →
  y P.≤ᵀ Whole.slot (f m) p → y P.≤ᵀ J.slot (S.lim f d) (m , p)
diag-lim f d m (inj₁ t) h = h
diag-lim f d m (inj₂ p) h = h
```
