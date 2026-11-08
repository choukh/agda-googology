# 真实双中 Ω 前缀仍读取中槽

选定p=floor1⊞act floor1，正是旧第三地板的第一个后继最高坐标。
下面对全部可数c证明：中槽取up c时，low的输出不低于c。因此不能
给这个真实前缀一个与中槽无关的可数上界。此结论不否定实际轨道受控的覆盖。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldPrefixSeed where
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.NegFold1If using (Sm; sz; ss; sl; Sm-mul; ¬s≤ᵛ)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym; zz)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor; pure-up; pure-reflexive)
open import OCF.Align.BoundedCompletionUniformIf using (Value)
import OCF.Align.BoundedCompletionUniformClosure as U
open import OCF.Align.BoundedWorldValueTwoSlot
open import OCF.Align.BoundedWorldCoverIf using (act)
import OCF.Align.BoundedWorldValueWhole as Whole
import OCF.Align.BoundedWorldValueCoverReduce as Reduce
import OCF.Align.BoundedNativeValueFirst as First
open import OCF.Align.FrozenAbsorbNegUpper using (P; infl)

prefix : HB V
prefix = floor 1 ⊞ act (floor 1)

pure-in : ∀ (c : Cd) → Sm (up {U} (up {S⊥} c)) c
pure-in hz = sz
pure-in (hs c) = ss (pure-in c)
pure-in (hl f) = sl (λ n → pure-in (f n))
act-pure : ∀ {a : HB V} {c : Cd} → Sm a c → Sm (act a) (P (hs hz) c)
act-pure sz = ss sz
act-pure (ss p) = sl (Sm-mul (act-pure p))
act-pure (sl p) = sl (λ n → act-pure (p n))

prefix-pure : ∀ u b p {a : HB V} {c : Cd} → Sm a c → low u b p ≤ᵛ low u b (p ⊞ a)
prefix-pure u b p sz = ≤-refl _
prefix-pure u b p (ss r) = ≤l 0 (prefix-pure u b p r)
prefix-pure u b p (sl r) = ≤l 0 (prefix-pure u b p (r 0))

floor-seed : ∀ u (c : Cd) → c ≤ᵛ low u (up c) (floor 1)
floor-seed u c = ≤l 0 (≤-trans (infl (hs hz) (≤-refl _) c)
  (≤-trans (First.sm-value (First.sm-sym (First.terminal-pure u (First.up-pure c))))
    (same-value (same-sym (Reduce.low-up (pure-up (pure-reflexive c)) (pure-reflexive u) (up c))))))

prefix-seed : ∀ u (c : Cd) → c ≤ᵛ low u (up c) prefix
prefix-seed u c = ≤l 0 (≤-trans (floor-seed u c)
  (prefix-pure u (up c) (floor 1) (act-pure (pure-in c))))

slot-self : ∀ (c : Cd) → Value hz (up c) (up c)
slot-self c = U.pure-up (≤-refl c)

no-uniform-middle-bound : ∀ u X →
  (∀ b → Value hz b b → low u b prefix ≤ᵛ X) → ⊥
no-uniform-middle-bound u X bound = ¬s≤ᵛ X
  (≤-trans (prefix-seed u (hs X)) (bound (up (hs X)) (slot-self (hs X))))
```

slot-self为所有测试种子提供真实分支值自证。量化范围是所有有值自证
的raw中槽，不声称这些槽全在Old3轨道中。跨到normal的关系必须同时
约束实际中槽增长，不能把prefix输出冻结成固定可数常量。
