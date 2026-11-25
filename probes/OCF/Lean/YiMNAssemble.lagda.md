# MinimalGoal 的组装、实际前缀与精确域分支
验收文件，读记号；编译定理 exact-branchˣ 填入实际底与 β，对精确域的全部原 M⁰ 下标给带 mc 的关系。
组装链：needˣ → 实际前缀及 η 范围 → DropActual → GoalExactᴰ；AllBranches → 原 MinimalGoal。
(b) actual-prefix、(c) eta-range 已填；首个阻点 (a) DropActual 未填，exact-from-drop 仅为条件接线。
精确域另名 Exact；no-all-exact 排除从原全域统一取精确标签；原 MinimalGoal 未证，登记事件未触发。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMNAssemble where
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([])
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiHCCheck as HC
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiBVDomain as D
import OCF.Lean.YiGLFrame as L
import OCF.Lean.YiGLExact as R
import OCF.Lean.YiXPSmall as X
import OCF.Lean.YiELZero as Z
import OCF.Lean.YiGCBridge as G
import OCF.Lean.YiQLRead as Q
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-trans′)
import OCF.Lean.YiMNRange as Range
AllBranches : Set
AllBranches = ∀ η d → K.M⁰ η d → G.At η d
assemble : AllBranches → S.MinimalGoal
assemble all = G.from-narrow (λ η d m _ → all η d m)
via-step : Q.Step → S.MinimalGoal
via-step = Q.minimal-from
Exact : B.Tr B.zero → Set
Exact d = Σ E.T (λ ν → Z.Ex⁰ ν d)
GoalExactˣ : Set
GoalExactˣ = ∀ η d → K.M⁰ η d → Exact d
  → R.Rˣ K.one (Q.Target η) (proj₁ (S.Small.child-out d))
GoalExactᴰ : Set
GoalExactᴰ = ∀ η d → K.M⁰ η d → Exact d → G.At η d
DropActual : Set
DropActual = ∀ η d → K.M⁰ η d → Exact d
  → R.Rˣ K.one (Q.Target η) (proj₁ (S.Small.child-out d)) → G.At η d
actual-prefix : ∀ d → R.Prefixˣ (S.Small.child-base d) []
actual-prefix d p κ lab = R.topˣ (B.at (S.child d) p) lab
eta-range : ∀ {η d ν} → K.M⁰ η d → Z.Ex⁰ ν d → η ≤ᵀ ν
eta-range m q = Range.ex-bound (HC.of⁰ m) q
exact-branchˣ : GoalExactˣ
exact-branchˣ η d m (ν , q) = X.needˣ d (proj₁ (proj₂ label)) η
  (≤-trans′ (eta-range m q) (proj₁ (proj₂ (proj₂ label))))
  (proj₂ S.okay d) (proj₂ (D.Input.table S.minimal) d)
  (S.Small.child-base d) (O.Ωt K.one) (λ i u → K.⊴r)
  (actual-prefix d) (R.topˣ K.one (L.lbl-fin 1))
  where
  label = Z.child-lbl d q
exact-from-drop : DropActual → GoalExactᴰ
exact-from-drop drop η d m q = drop η d m q (exact-branchˣ η d m q)
exact-zero : Exact B.zero
exact-zero = [] , Z.ex-nat 0
zero-lower : K.M⁰ [] B.zero
zero-lower = K.mz
zero-drop : ∀ d → K.M⁰ [] d → Exact d
  → R.Rˣ K.one (Q.Target []) (proj₁ (S.Small.child-out d)) → G.At [] d
zero-drop d m q r = G.zero d
no-all-exact : (∀ η d → K.M⁰ η d → Exact d) → ⊥
no-all-exact all = Z.no-lbl-slow _ (proj₂ (all [] Z.slow K.mz))
```
