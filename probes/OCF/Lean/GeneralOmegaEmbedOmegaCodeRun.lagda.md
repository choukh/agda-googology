# 原code保持低层关系，原Tree关系给完整运行同形

实际编码为低层地板加pure(leg反馈)。前篇读取的低层Layer正好消费
已证原floor闭包与纯树关系，然后encode回同一Kind的Coord。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedOmegaCodeRun where
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (lvl)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaConsumeLayerRun using (leg-same)
open import OCF.Lean.GeneralOmegaEmbedOmegaIf
open import OCF.Lean.GeneralOmegaEmbedOmegaCodeIf
open import OCF.Lean.GeneralOmegaEmbedOmegaFloorRun using (floor; tree-add)
import OCF.Lean.GeneralOmegaEmbedIf as C
import OCF.Lean.GeneralOmegaEmbedRun as Proof
import OCF.Lean.GeneralOmegaConsumeRun as R

pure-related : ∀ {x y} (p : Layer x y) {a b} → Same a b →
  Tree p (pure (Lv x) a) (pure (Lv y) b)
pure-related p zz = tz
pure-related p (ss r) = ts (pure-related p r)
pure-related p (ll r) = tl (λ n → pure-related p (r n))
pure-related p (oo {κ = ()} r)

code-related : ∀ {x y} (p : Layer x y) {κ κ′} (r : Kind p κ κ′) {d e} →
  Same d e → Coord p r (code x κ d) (code y κ′ e)
code-related p {κ} {κ′} r q = encode p {κ} {κ′} r
  (tree-add (lower p {κ} {κ′} r) (floor (lower p {κ} {κ′} r))
    (pure-related (lower p {κ} {κ′} r) (leg-same q)))

coded : ∀ {x y a b} (p : Layer x y) → Tree p a b → C.Coded x y a b
coded p tz = C.cz
coded p (ts r) = C.cs (coded p r)
coded p (tl r) = C.cl (λ n → coded p (r n))
coded p (to {κ = κ} {κ′ = κ′} r f) = C.co (λ q → coded p (f (code-related p {κ} {κ′} r q)))

sound : ∀ {x y a b} (p : Layer x y) → Tree p a b → Same (R.run x a) (R.run y b)
sound p r = Proof.sound (coded p r)
```

sound比较原run的全部反馈与输出和。没有读标签、裸层号比较、函数
外延或两份Layer证明的无关性；不能把任意raw树免费视作有Tree自证。
