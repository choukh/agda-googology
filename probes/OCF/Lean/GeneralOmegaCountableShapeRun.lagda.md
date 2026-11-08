# 原Γ的全域同形保持

每次观察的分类都在自己的合法公共source界内进行。对应合法步进
使分类同步；异坐标HTrees证书使原全部反馈同步。没有用任意高层
Same充当分支函数同余，也没有要求两个source有字面公共上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableShapeRun where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ)
open import OCF.Lean.GeneralOmegaCountableShapeIf
open import OCF.Lean.GeneralOmegaCountableShapeBase
open import OCF.Lean.GeneralOmegaCountableShapeCompare
open import OCF.Lean.GeneralOmegaCountableShapeFloor
open import OCF.Lean.GeneralOmegaCountableShapeNode
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)

module Induction (S T : KS) (k : K S → K T) (Q : ∀ κ → E S κ → E T (k κ) → Set)
  (P : HB S → HB T → Set)
  (z : P hz hz)
  (s : ∀ {a b} → P a b → P (hs a) (hs b))
  (l : ∀ {f g} → (∀ n → P (f n) (g n)) → P (hl f) (hl g))
  (o : ∀ {κ f g} → (∀ {x y} → Q κ x y → P (f x) (g y)) → P (hΩ κ f) (hΩ (k κ) g)) where
  run : ∀ {a b} → HTrees S T k Q a b → P a b
  run tz = z
  run (ts p) = s (run p)
  run (tl p) = l (λ n → run (p n))
  run (to p) = o (λ r → run (p r))

left-tree : ∀ {a b : Cd} (p : Same a b) {x y} → Tree p x y →
  ∀ n → Tree p (leftMul x n) (leftMul y n)
left-tree p r zero = tz
left-tree p r (suc n) = add-tree r (left-tree p r n)

module Observe {A B : Cd} (source : Same A B) (la : LgB A) (lb : LgB B)
  (legal : LegalShape source la lb) where
  Result : HB (F A) → HB (F B) → Set
  Result x y = ∀ {t u} (target : Same t u) {pt qt} → Paths target source pt qt →
    Tree target (observe A la t pt x) (observe B lb u qt y)
  at-zero : Result hz hz
  at-zero target h = floor-tree target
  successor : ∀ {x y} → Result x y → Result (hs x) (hs y)
  successor ih target h = tl (left-tree target (ih target h))
  limit : ∀ {f g} → (∀ n → Result (f n) (g n)) → Result (hl f) (hl g)
  limit ih target h = tl (λ n → ih n target h)
  omega : ∀ {κ f g} → (∀ {x y} → Coord source κ x y → Result (f x) (g y)) →
    Result (hΩ κ f) (hΩ (map-K source κ) g)
  omega {κ} {f} {g} ih target h = node-shape source la lb legal target h κ
    (λ i pi e → observe A la i pi (f e)) (λ i pi e → observe B lb i pi (g e))
    (λ p hp r → ih r p hp)
  preserve : ∀ {x y} → Tree source x y → Result x y
  preserve = Induction.run (F A) (F B) (map-K source) (Coord source) Result at-zero successor limit omega

zero-tree : ∀ {a b} → Tree zz a b → Same a b
zero-tree tz = zz
zero-tree (ts p) = ss (zero-tree p)
zero-tree (tl p) = ll (λ n → zero-tree (p n))
zero-tree (to {κ = ()} p)
canonical-observer : CanonicalObserverShape
canonical-observer = record { preserve = λ {a} {b} p r → zero-tree
  (Observe.preserve (leg-same p) (Lg-leg a) (Lg-leg b) (canonical-leg-legal p)
    r zz (zero-paths (leg-same p))) }
gamma-shape : GammaShape
gamma-shape = from-observer canonical-observer
Γ-same : ∀ {a b : Cd} → Same a b → Same (Γ a) (Γ b)
Γ-same = GammaShape.preserve-Γ gamma-shape
```

该定理适用于全部原Cd输入且输出正是原Γ。它只保持Same结构，
不保持任意值等价，也没有取消高度加法右吸收的独立义务。
