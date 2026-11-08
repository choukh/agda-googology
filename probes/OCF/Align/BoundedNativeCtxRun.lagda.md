# 同一Ctx的具体保留算法

保留原zero1/srepeat/limpoint规则，仅让整分量的全部kind共用同一Ctx。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeCtxRun where
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecLeg using (pw; lgpw; ek; frC; toC; frto; bdTo; bdFr; prFr)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.TowerCollapseClosed using (module LegalSum)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedNativeCtxIf

module Keep {c t : Cd} (q : c ⊲ t) where
  C = context q
  run : HB (Native c) → HB (Native t)
  run hz = hs hz
  run (hs a) = Ops.repeat (Native t) (run a)
  run (hl f) = hl (λ n → run (f n))
  run (hΩ κ g) = hΩ (ek C κ) (λ e → run (g (frC C κ e)))

  position : ∀ {a b W} → a ⊲[ pw C W ] b → run a ⊲[ W ] run b
  position hself = hself
  position (hsuc p) = ⊲ᴮ-tr (position p) (hlim 0 hself)
  position (hlim n p) = hlim n (position p)
  position {a} {hΩ κ g} {W} (hLim {c = e} b p) =
    hLim (bdTo C κ b)
      (subst (λ d → run a ⊲[ W ] run (g d)) (sym (frto C κ e)) (position p))

  legal : ∀ a → LgB a → LgB (run a)
  legal hz l = l
  legal (hs a) l = LegalSum.sum-legal (Native t) _ (λ n → legal a l)
  legal (hl f) (st , l) = (λ n → position (st n)) , (λ n → legal (f n) (l n))
  legal (hΩ κ g) (mo , l) =
    (λ lw b b′ p → position (mo (lgpw C lw) (bdFr C κ b) (bdFr C κ b′) (prFr C κ p))) ,
    (λ lw b → legal (g _) (l (lgpw C lw) (bdFr C κ b)))

instance-retain : ∀ {B} lB c (pc : c ⊲ B) t (pt : t ⊲ B) (q : c ⊲ t) → Retain lB c pc t pt q
instance-retain lB c pc t pt q = record
  { run = Keep.run q
  ; at-zero = refl ; at-suc = λ a → refl ; at-lim = λ f → refl ; at-node = λ κ g → refl
  ; position = Keep.position q ; legal = Keep.legal q }
```

位置律与合法性对整个分量树成立，分量中的全部Ω构造子都包括在内。
这不是一般跨分量Source的全部分支折叠；后者仍需单独定义与验收。
