# 真实含Ω组件的合法内部View闭项

原组件高度是flL U，输入是其完整原地板。根坐标界取ω，包含所有有限
自然数；其余层世界取合法后继1，避免把全部分支只限为零。输出是新的
有界坐标树值，不冒称原组件值保持或动态折叠已完成。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexViewClosed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤Ω; s≤s; z≤)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.HigherIndexClassIf using (U; Native)
open import OCF.Lean.HigherIndexFoldIf using (k; g)
open import OCF.Lean.HigherIndexSupportFloor using (floor-support)
open import OCF.Lean.HigherIndexViewIf
import OCF.Lean.HigherIndexViewRun as V

one-world : ∀ x → Wd (Lv x)
one-world lz = tt
one-world (ls x) = one-world x , hs hz
one-world (ll f) = λ n → one-world (f n)
one-world (lΩ k g) (inj₁ _) = one-world k , hs hz
one-world (lΩ k g) (inj₂ d) = one-world (g d)
one-world-legal : ∀ x → LgW (Lv x) (one-world x)
one-world-legal lz = tt
one-world-legal (ls x) = one-world-legal x , tt
one-world-legal (ll f) = λ n → one-world-legal (f n)
one-world-legal (lΩ k g) (inj₁ _) = one-world-legal k , tt
one-world-legal (lΩ k g) (inj₂ d) = one-world-legal (g d)

num : ℕ → Cd
num zero = hz
num (suc n) = hs (num n)
num-legal : ∀ n → LgB (num n)
num-legal zero = tt
num-legal (suc n) = num-legal n
ω : Cd
ω = hl num
ω-legal : LgB ω
ω-legal = (λ n → hsuc hself) , num-legal

coordinate : HB U
coordinate = flL k
x : LH
x = g coordinate
W : Wd (Lv x)
W (inj₁ _) = tt , ω
W (inj₂ d) = one-world (g (up d))
lW : LgW (Lv x) W
lW (inj₁ _) = tt , ω-legal
lW (inj₂ d) = one-world-legal (g (up d))

module Actual = V.View (Lv x) W lW
closed : Actual.Object
closed = flL x , Lg-flL x
output : HB Actual.Target
output = Actual.value closed
legal-output : LgB output
legal-output = Actual.legal (flL x) (Lg-flL x)
internal-view : Actual.Shape
internal-view = Actual.view closed
value-view : output ≡ Actual.assemble internal-view
value-view = Actual.value-view closed

-- 所有自然数坐标确实在同一字面ω界内；不是有限样本测试。
admitted : ∀ n → E Actual.Target (inj₁ tt , inj₂ tt)
admitted n = num n , hlim n hself

positive : hs hz ≤ᵛ output
positive = ≤Ω (admitted 1)
  (≤Ω (hs hz , hself) (≤Ω (hs hz , hself) (s≤s z≤)))
```

positive是关于这一具体合法输出的值定理，仅为下界1，不是攀升强度
声明。该实例提供真实含Ω组件、无限坐标域、同类型递归View与合法输出；
尚不解决动态β/B变化时保持同一支持坐标输出层，以及全回灌fold闭包。
