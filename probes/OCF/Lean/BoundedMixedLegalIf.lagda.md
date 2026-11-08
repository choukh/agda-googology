# 实际全自然数混合输出的逐项合法义务

本接口固定原运行器与原输入，不允许用另一个fold或合法化输出填充。
put/floor/sums与Align.BoundedFoldValueMixed字面同形；在Lean重述仅为
避免定义层导入验收层，桥可由refl检查。Pointwise不是已取得的实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedMixedLegalIf where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf using (Pos; Safe; T; G)
open import OCF.Lean.LHRecFl using (flL)
import OCF.Lean.BoundedContextClosed as C
import OCF.Lean.BoundedFoldRun as Run

β = hl C.num
S = Safe β C.B
F : ℕ → KS
F n = T (up (C.num n))
finite-pos : ∀ n κ → Pos β (up (C.num n)) κ
finite-pos zero κ = tt
finite-pos (suc n) (inj₁ κ) = finite-pos n κ
finite-pos (suc n) (inj₂ _) = tt
put : ∀ n → HB (F n) → HB S
put n hz = hz
put n (hs a) = hs (put n a)
put n (hl f) = hl (λ j → put n (f j))
put n (hΩ κ g) = hΩ ((inj₂ (C.num n) , κ) , (hlim n hself , finite-pos n κ))
  (λ c → put n (g c))
floor : ℕ → HB S
floor n = put n (flL (G (up (C.num n))))
sums : ℕ → HB S
sums zero = floor zero
sums (suc n) = sums n ⊞ floor (suc n)
module Fold = Run.Run β (proj₂ C.legal-w) C.B C.legal-B
at : ℕ → HB (T hz)
at n = Fold.fold hz (z⊲ᴮ C.B) (sums n)
output : HB (T hz)
output = Fold.fold hz (z⊲ᴮ C.B) (hl sums)

record Pointwise : Set where
  field
    legal-at : ∀ n → LgB (at n)
```

外层步进已由BoundedFoldValueMixedSteps.folded-step证明；这里只记录
尚缺的全部逐项合法性。没有附加无法实例化的任意坐标单调假设。
