# 实际生成元的种子不能任意冻结为常值

直接检验左前缀稳定性：对生成元 top1，任意种子 b 的模型值严格超过 b。
因此不能把 changing 递归中的前缀基值无条件替换为种子零时的常量。
这不否定零种子同点吸收律，也不否定更高冻结生成元的共尾吸收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenAbsorbSeed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ʳ)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenOutputIf using (Mode; changing; frozen; update; Generated; initial)
import OCF.Align.FrozenOutputIf as If
import OCF.Lean.Fold1Fold as F
import OCF.Lean.Fold1 as Original

right-add : ∀ (a b : Cd) → b ≤ᵛ (a ⊞ b)
right-add a hz = z≤
right-add a (hs b) = s≤s (right-add a b)
right-add a (hl f) = l≤ (λ n → ≤l n (right-add a (f n)))

module Seed (A : Cd) (positive-A : hs hz ≤ᵛ A) where
  open If.Model A
  positive-pure : ∀ m b c → hs hz ≤ᵛ run m b (up c)
  positive-pure m b hz = positive-A
  positive-pure m b (hs c) = ≤l 0 (positive-pure m b c)
  positive-pure m b (hl f) = ≤l 0 (positive-pure m b (f 0))

  inflate-pure : ∀ m b c → c ≤ᵛ run m b (up c)
  inflate-pure m b hz = z≤
  inflate-pure m b (hs c) = ≤l 1 (add-mono (inflate-pure m b c) (positive-pure m b c))
  inflate-pure m b (hl f) = l≤ (λ n → ≤l n (inflate-pure m b (f n)))

  module Orbit (m : Mode) (b : Cd) where
    module K = F.Col _⊞_ _⊞_ b b (update m)
      (λ w e → run m w (up e)) (λ w e → run m w (up e))

    strict-seed : hs b ≤ᵛ run m b (top (hs hz))
    strict-seed = ≤l 1 (≤-trans
      (≤-trans (⊞-≤ʳ b (positive-pure m b b))
        (inflate-pure m (K.cw 1) (K.ce 1)))
      (right-add (K.oo 0) (K.oo 1)))

  no-uniform-seed-bound : ∀ m B → (∀ b → run m b (top (hs hz)) ≤ᵛ B) → ⊥
  no-uniform-seed-bound m B bound = ¬s≤ᵛ B (≤-trans (Orbit.strict-seed m B) (bound B))

  no-zero-seed-replacement : ∀ m →
    (∀ b → run m b (top (hs hz)) ≤ᵛ run m hz (top (hs hz))) → ⊥
  no-zero-seed-replacement m = no-uniform-seed-bound m (run m hz (top (hs hz)))

positive-actual-base : hs hz ≤ᵛ Original.TΩ1
positive-actual-base = ≤l 0 (s≤s z≤)
module Actual = Seed Original.TΩ1 positive-actual-base

actual-generated : Generated (top (hs hz))
actual-generated = initial
```

前提有实际实例：零点是已桥接的 Original.TΩ1，正性由其第零分支给出，
被测试前缀正是 Generated.initial。否定范围只涉及任意种子的统一界；
当前真实旧种子来自特定回灌轨道，能否由更高冻结轨道吸收仍未解决。
