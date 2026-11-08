# 保旧Ω的typed轨道与实际重化地板访问

不改变Typed动作，也不把旧Ω改成纯树。相关轨道的Reify层直接由
已证ΩL/加法/upL闭包产生。值结论分别标明实际访问与相关运行同形，
均不冒称typed整输出已被更高地板支配。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaReifyRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (ΩL; twL; ΛL)
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.BoundedMixedAffine using (module Action)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.GeneralOmegaReifyIf
open import OCF.Lean.GeneralOmegaEmbedOmegaIf
open import OCF.Lean.GeneralOmegaEmbedOmegaLayer using (add-layer; omega-layer; up-layer; tower-layer; lambda-layer)
open import OCF.Lean.GeneralOmegaEmbedOmegaFloorRun using (floor; tree-add)
open import OCF.Lean.GeneralOmegaEmbedOmegaCodeActual using (floor-same)
open import OCF.Lean.FrozenWorldLift using (Same)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
import OCF.Lean.GeneralOmegaSampleRun as S
import OCF.Lean.GeneralOmegaConsumeRun as R

orbit-legal : ∀ j n → LgB (Orbit j n)
orbit-legal j = Action.legal-chain (Lv j) (flL j) (Lg-flL j)
visited-legal : ∀ j → LgB (VisitedFloor j)
visited-legal j = S.Floor.sample-legal j (Reify j) zero
visited-value : ∀ j → R.run (ΩL (ls j)) (VisitedFloor j) ≤ᵛ R.run (ΩL (ls j)) (flL (ΩL (ls j)))
visited-value j = S.Floor.sample-value j (Reify j) zero
instance-reification : Reification
instance-reification = record { orbit-legal = orbit-legal ; visited-legal = visited-legal ; visited-value = visited-value }

partial-tree : ∀ {x y} (p : Layer x y) {f g} →
  (∀ n → Tree p (f n) (g n)) → ∀ n → Tree p (Ops.partial (Lv x) f n) (Ops.partial (Lv y) g n)
partial-tree p q zero = q zero
partial-tree p q (suc n) = tree-add p (partial-tree p q n) (q (suc n))

affine-tree : ∀ {x y A B a b} (p : Layer x y) → Tree p A B → Tree p a b →
  Tree p (Action.run (Lv x) A a) (Action.run (Lv y) B b)
affine-tree p q tz = q
affine-tree p q (ts r) = tl (partial-tree p (λ _ → affine-tree p q r))
affine-tree p q (tl r) = tl (λ n → affine-tree p q (r n))
affine-tree p q (to k r) = to k (λ e → affine-tree p q (r e))

orbit-tree : ∀ {x y} (p : Layer x y) n → Tree p (Orbit x n) (Orbit y n)
orbit-tree p zero = ts tz
orbit-tree p (suc n) = tree-add p (orbit-tree p n) (affine-tree p (floor p) (orbit-tree p n))
reify-layer : ∀ {x y a b} (p : Layer x y) → Tree p a b → Layer (Reify x a) (Reify y b)
reify-layer p r = add-layer (omega-layer p) (up-layer p r)
orbit-layer : ∀ {x y} (p : Layer x y) n → Layer (Reify x (Orbit x n)) (Reify y (Orbit y n))
orbit-layer p n = reify-layer p (orbit-tree p n)
orbit-value : ∀ {x y} (p : Layer x y) n →
  Same (R.run (Reify x (Orbit x n)) (flL (Reify x (Orbit x n))))
    (R.run (Reify y (Orbit y n)) (flL (Reify y (Orbit y n))))
orbit-value p n = floor-same (orbit-layer p n)

tower-orbit : ∀ n m → Layer (Reify (twL n) (Orbit (twL n) m)) (Reify (twL n) (Orbit (twL n) m))
tower-orbit n = orbit-layer (tower-layer n)
lambda-orbit : ∀ m → Layer (Reify ΛL (Orbit ΛL m)) (Reify ΛL (Orbit ΛL m))
lambda-orbit = orbit-layer lambda-layer
```

visited-value是原更高ΩL节点一次真实完整回调的值包含，保留θ左前缀。
它不是删除前缀后的floor值包含，更没有把Orbit后续项说成真实采样。
orbit-tree与orbit-value覆盖原typed动作全部自然数迭代，旧Ω分支在
关系中原样保留；所需typed输出的有向支配仍待证明。
