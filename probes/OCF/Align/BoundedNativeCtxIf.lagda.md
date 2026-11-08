# 同一上下文保留整个原生分量

本实验针对编译过的NegOutput合法性反例，使用真实HB(Native c)分量。
它不把任意Source分支误认为属于同一分量，不替换既有NativeRun。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeCtxIf where
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLeg using (pw; ek; frC)
open import OCF.Lean.BoundedContextRun using (path-context)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedDescentValueBridge using (Native)

context : ∀ {c t : Cd} → c ⊲ t → OCF.Lean.LHRecLeg.Ctx (Native t) (Native c)
context = path-context (ls lz) lz

record Retain {B : Cd} (lB : LgB B) (c : Cd) (pc : c ⊲ B)
  (t : Cd) (pt : t ⊲ B) (q : c ⊲ t) : Set where
  field
    run : HB (Native c) → HB (Native t)
    at-zero : run hz ≡ hs hz
    at-suc : ∀ a → run (hs a) ≡ Ops.repeat (Native t) (run a)
    at-lim : ∀ (f : ℕ → HB (Native c)) → run (hl f) ≡ hl (λ n → run (f n))
    at-node : ∀ κ g → run (hΩ κ g) ≡
      hΩ (ek (context q) κ) (λ e → run (g (frC (context q) κ e)))
    position : ∀ {a b W} → a ⊲[ pw (context q) W ] b → run a ⊲[ W ] run b
    legal : ∀ a → LgB a → LgB (run a)
```

所有高度带共同合法B的位置，q是其中c到t的已给路径。全部kind使用
同一个context q，包括底种类；不再让底种类独立跳到目标第0拷贝。
