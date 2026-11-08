# 原观察器目标零处的有证路径相容

这里不判定两条零路径相等。固定同一source、合法证据与实际kind，
其秩为零时只有same，秩非零时只有above；above的目标到秩路径
不进入反馈计算。用原遗传坐标关系同步same反馈，因而不能删掉
输入Rel前提，也没有要求任意高层分支保持Same。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObserveZeroPath where
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableRelIf
open import OCF.Lean.GeneralOmegaCountableRelClass
open import OCF.Lean.GeneralOmegaCountableRelRun

record ZeroPathSimulation : Set₁ where
  field
    full-zero : ∀ B lB (pt qt : hz ⊲ B) {a b} → Rel B a b →
      Rel hz (observe B lB hz pt a) (observe B lB hz qt b)

zero-decision : ∀ {B A} (i : Cd) → hs i ⊲ B → (HB (F i) → A) → C.Dc F B hz A
zero-decision hz pi to = C.same to
zero-decision (hs i) pi to = C.above (hs i) pi (z⊲ᴮ (hs i)) to
zero-decision (hl f) pi to = C.above (hl f) pi (z⊲ᴮ (hl f)) to
zero-decision (hΩ () f) pi to

pick-zero : ∀ {B A} (i : Cd) (pi : hs i ⊲ B) (to : HB (F i) → A)
  (r : (hz ⊲ hs i) ⊎ (hs i ⊲ hz)) (pt : hz ⊲ B)
  (rec : ∀ j → j ⊲ B → A → HB (F j)) →
  node pt (C.pick S⊥ to pi r) rec ≡ node pt (zero-decision i pi to) rec
pick-zero hz pi to (inj₁ (hsuc hself)) pt rec = refl
pick-zero (hs i) pi to (inj₁ (hsuc (hsuc p))) pt rec = refl
pick-zero (hl f) pi to (inj₁ (hsuc (hlim n p))) pt rec = refl
pick-zero (hΩ () f) pi to r pt rec
pick-zero i pi to (inj₂ ()) pt rec

normal-node : ∀ {B κ} (pt : hz ⊲ B) → C.Cl {S⊥} B κ →
  (∀ j → j ⊲ B → E (F B) κ → HB (F j)) → Cd
normal-node pt (C.bas () to) rec
normal-node pt (C.nw i pi to) rec = node pt (zero-decision i pi to) rec

normalize-node : ∀ {B κ} lB (pt : hz ⊲ B) (v : C.Cl {S⊥} B κ)
  (rec : ∀ j → j ⊲ B → E (F B) κ → HB (F j)) →
  node pt (C.dcl pt lB v) rec ≡ normal-node pt v rec
normalize-node lB pt (C.bas () to) rec
normalize-node lB pt (C.nw i pi to) rec = pick-zero i pi to (cmpB pi pt _ lB) pt rec

normal-related : ∀ {B κ} (pt qt : hz ⊲ B) (v : C.Cl {S⊥} B κ) → ClGood v →
  (rec rec′ : ∀ j → j ⊲ B → E (F B) κ → HB (F j)) →
  (∀ {a b} → Coord B κ a b → Rel hz (rec hz pt a) (rec′ hz qt b)) →
  (∀ j pj {a b} → Coord B κ a b → Rel j (rec j pj a) (rec′ j pj b)) →
  Rel hz (normal-node pt v rec) (normal-node qt v rec′)
normal-related pt qt (C.bas () to) good rec rec′ at-zero at-same
normal-related pt qt (C.nw hz pi to) good rec rec′ at-zero at-same = rl
  (λ n → at-zero (good (iterate-rel (λ r → at-zero (good r)) (floor-related hz) n)))
normal-related pt qt (C.nw (hs i) pi to) good rec rec′ at-zero at-same = rl
  (λ n → at-zero (good (iterate-rel
    (λ r → at-same (hs i) (⊲ᴮ-tr (hsuc hself) pi) (good r)) (floor-related (hs i)) n)))
normal-related pt qt (C.nw (hl f) pi to) good rec rec′ at-zero at-same = rl
  (λ n → at-zero (good (iterate-rel
    (λ r → at-same (hl f) (⊲ᴮ-tr (hsuc hself) pi) (good r)) (floor-related (hl f)) n)))
normal-related pt qt (C.nw (hΩ () f) pi to) good rec rec′ at-zero at-same

node-zero-path : ∀ B lB (pt qt : hz ⊲ B) κ
  (rec rec′ : ∀ j → j ⊲ B → E (F B) κ → HB (F j)) →
  (∀ {a b} → Coord B κ a b → Rel hz (rec hz pt a) (rec′ hz qt b)) →
  (∀ j pj {a b} → Coord B κ a b → Rel j (rec j pj a) (rec′ j pj b)) →
  Rel hz (node pt (classify B lB hz pt κ) rec)
    (node qt (classify B lB hz qt κ) rec′)
node-zero-path B lB pt qt κ rec rec′ at-zero at-same = subst₂ (Rel hz)
  (sym (normalize-node lB pt (C.cl B κ) rec))
  (sym (normalize-node lB qt (C.cl B κ) rec′))
  (normal-related pt qt (C.cl B κ) (cl-good B κ) rec rec′ at-zero at-same)

zero-path-observe : ∀ B lB (pt qt : hz ⊲ B) {a b} → Rel B a b →
  Rel hz (observe B lB hz pt a) (observe B lB hz qt b)
zero-path-observe B lB pt qt rz = floor-related hz
zero-path-observe B lB pt qt (rs p) = rl (left-rel (zero-path-observe B lB pt qt p))
zero-path-observe B lB pt qt (rl p) = rl (λ n → zero-path-observe B lB pt qt (p n))
zero-path-observe B lB pt qt (ro {κ} {f} {g} p) = node-zero-path B lB pt qt κ
  (λ j pj e → observe B lB j pj (f e)) (λ j pj e → observe B lB j pj (g e))
  (λ r → zero-path-observe B lB pt qt (p r))
  (λ j pj r → observe-related B lB j pj (p r))

instance-zero : ZeroPathSimulation
instance-zero = record { full-zero = zero-path-observe }
```

floor-related为任意B实填输入。结论只限目标零，既不建立任意目标
路径相容，也不将不同source高度判等；Γ的规范零路径可以与实际
分量路径在这个有证域内比较，完成运输仍需另用Same或结构模拟。
