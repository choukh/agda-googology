# 原多槽世界：最高回灌与尚待证明的输出覆盖

本接口保留原 Fold1 的全部世界。最高槽回灌时，较低槽不变，但输出
仍读取那些槽；因此坐标去世界化不等于完整折叠去世界化。
比较的目标 m 与源 hs m 的共同界逐字是 hs m，路径 hsuc hself。
这里先冻结可以实际实例化的最高坐标契约，而不将完整输出覆盖偷放成公理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldCoverIf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same)
import OCF.Lean.Fold1If as I
import OCF.Lean.Fold1Fold as F

act : ∀ {S} → HB S → HB S
act hz = hs hz
act (hs a) = hl (I.mul (act a))
act (hl f) = hl (λ n → act (f n))
act (hΩ κ g) = hΩ κ (λ e → act (g e))

module Actual (m : Cd) (lm : LgB m) (W : Wd (I.Lv (hs m))) where
  module Original = F.Col _⊞_ _⊞_ W (proj₂ W)
    (λ V e → proj₁ V , e)
    (λ V e → F.Φ (hs m) lm m (hsuc hself) V (up e))
    (λ V e → F.Φ (hs m) lm hz (hsuc (z⊲ᴮ m)) V (up e))
  orbit : ℕ → HB (I.Lv m)
  orbit zero = proj₂ W
  orbit (suc n) = orbit n ⊞ act (orbit n)

record HighestSimulation : Set₁ where
  field
    coordinate : ∀ m lm (W : Wd (I.Lv (hs m))) {a b} → Same a b →
      Same (F.Φ (hs m) lm m (hsuc hself) W (up a)) (act b)
    coordinates : ∀ m lm W n → Same (Actual.Original.ce m lm W n)
      (Actual.orbit m lm W n)
    lower-world : ∀ m lm W n → proj₁ (Actual.Original.cw m lm W n) ≡ proj₁ W
```

Original.oo/oO仍是原多槽折叠的输出及部分和；没有将它们改成固定seed1
的 read 或 UniformStage.orbit。完整值目标还需把这些原输出送到规范族。
