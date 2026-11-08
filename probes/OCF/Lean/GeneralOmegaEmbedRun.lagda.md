# 编码分支模拟的真实运行与部分和闭包

以下sound对原run证明，并在Ω处比较完整反馈坐标链和输出部分和，
没有另造解释器。它不借用高层值关系的任意分支选择规则。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedRun where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (LH; Lv)
open import OCF.Lean.GeneralOmegaEmbedIf
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
import OCF.Lean.GeneralOmegaConsumeRun as R
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.BoundedDiagonalSame using (same-add; module Compare)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.HigherIndexConsumeCode using (pure)

repeat-same : ∀ {a b : Cd} → Same a b → Same (Ops.repeat S⊥ a) (Ops.repeat S⊥ b)
repeat-same {a} {b} p = ll partial where
  partial : ∀ n → Same (Ops.partial S⊥ (λ _ → a) n) (Ops.partial S⊥ (λ _ → b) n)
  partial zero = p
  partial (suc n) = same-add (partial n) p

sound : ∀ {x y a b} → Coded x y a b → Same (R.run x a) (R.run y b)
sound cz = ss zz
sound (cs p) = repeat-same (sound p)
sound (cl p) = ll (λ n → sound (p n))
sound {x} {y} (co {κ} {κ′} {f} {g} p) =
  Compare.result (λ d → R.run x (f (code x κ d)))
    (λ e → R.run y (g (code y κ′ e)))
    (λ d → R.run x (f (code x κ d)))
    (λ e → R.run y (g (code y κ′ e)))
    (λ q → sound (p q)) (λ q → sound (p q))

add : ∀ {x y a b c d} → Coded x y a b → Coded x y c d → Coded x y (a ⊞ c) (b ⊞ d)
add p cz = p
add p (cs q) = cs (add p q)
add p (cl q) = cl (λ n → add p (q n))
add p (co q) = co (λ r → add p (q r))

pure-related : ∀ x y {a b} → Same a b → Coded x y (pure (Lv x) a) (pure (Lv y) b)
pure-related x y zz = cz
pure-related x y (ss p) = cs (pure-related x y p)
pure-related x y (ll p) = cl (λ n → pure-related x y (p n))
pure-related x y (oo {κ = ()} p)

partial-related : ∀ {x y} (f : ℕ → HB (Lv x)) (g : ℕ → HB (Lv y)) →
  (∀ n → Coded x y (f n) (g n)) → ∀ n →
  Coded x y (Ops.partial (Lv x) f n) (Ops.partial (Lv y) g n)
partial-related f g p zero = p zero
partial-related f g p (suc n) = add (partial-related f g p n) (p (suc n))
```

partial-related保留原完整部分和，不能把它当作各分量嵌入已经相容。
这里没有Same→LgB的运输；合法性需要独立第一位置证明。
