# 旧第二地板的实际全轨道解释

旧 TΩ2 的最高槽初值是最低 Ω 地板，而非 1。这里将这个差异保留在
整条坐标链中；不借 TΩ2 的 ψ₀(Ω₂) 读法作为值前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionValueAcceptOld where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)
open import OCF.Align.FrozenInnerOuter using (same-add; same-mul)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Lean.Fold1If
import OCF.Lean.Fold1 as Old
import OCF.Lean.Fold1Fold as F
import OCF.Align.FrozenOutputSim as Sim

U = step S⊥
act : HB U → HB U
act hz = hs hz
act (hs a) = hl (OCF.Lean.Fold1If.mul (act a))
act (hl f) = hl (λ n → act (f n))
act (hΩ (inj₁ ()) g)
act (hΩ (inj₂ _) g) = hΩ (inj₂ tt) (λ e → act (g e))

rel-mul : ∀ {a b} → Rel hz a b → ∀ n → Rel hz
  (OCF.Lean.Fold1If.mul a n) (OCF.Lean.Fold1If.mul b n)
rel-mul p zero = p
rel-mul p (suc n) = rel-add (rel-mul p n) p

act-bridge : ∀ {a b} → Rel hz a b → ∀ W → Rel hz
  (F.Φ (num 2) tt (num 1) (hsuc hself) W (up a)) (act b)
act-bridge rz W = rs rz
act-bridge (rs p) W = rl (rel-mul (act-bridge p W))
act-bridge (rl p) W = rl (λ n → act-bridge (p n) W)
act-bridge (ro {κ = inj₁ ()} p) W
act-bridge (ro {κ = inj₂ _} p) W = ro (λ x y r → act-bridge (p x y r) W)

fold-bridge : ∀ {a b} → Rel hz a b → ∀ {u v} → Same u v → ∀ w → Same
  (F.Φ (num 2) tt hz (hsuc (hsuc hself)) ((tt , u) , w) (up a)) (T.fold v b)
fold-bridge rz uv w = ss zz
fold-bridge (rs p) uv w = ll (same-mul (fold-bridge p uv w))
fold-bridge (rl p) uv w = ll (λ n → fold-bridge (p n) uv w)
fold-bridge (ro {κ = inj₁ ()} p) uv w
fold-bridge {a = hΩ (inj₂ _) f} {b = hΩ (inj₂ _) g} (ro p) {u} {v} uv w = ll D.sums
  where
  WR : Wd (step U) → Wd U → Set
  WR W V = Same (proj₂ (proj₁ W)) (proj₂ V)
  branch : ∀ {W V x y} → WR W V → Same x y → Same
    (F.Φ (num 2) tt hz (hsuc (hsuc hself)) W (up (f x))) (T.fold (proj₂ V) (g y))
  branch {W = ((tt , u′) , w′)} {V = (tt , v′)} r xy = fold-bridge (p _ _ xy) r w′
  module D = Sim.Sim WR ((tt , u) , w) (tt , v) uv u v uv
    (λ W e → (tt , e) , proj₂ W) (λ V e → tt , e) (λ r xy → xy)
    (λ W e → F.Φ (num 2) tt hz (hsuc (hsuc hself)) W (up (f e)))
    (λ V e → T.fold (proj₂ V) (g e))
    (λ W e → F.Φ (num 2) tt hz (hsuc (hsuc hself)) W (up (f e)))
    (λ V e → T.fold (proj₂ V) (g e)) branch branch

module Actual = F.Col _⊞_ _⊞_ ((tt , hz) , floor zero) (floor zero)
  (λ W e → proj₁ W , e)
  (λ W e → F.Φ (num 2) tt (num 1) (hsuc hself) W (up e))
  (λ W e → F.Φ (num 2) tt hz (hsuc (hsuc hself)) W (up e))
module Pure = F.Col _⊞_ _⊞_ tt (floor zero) (λ _ _ → tt)
  (λ _ e → act e) (λ _ e → T.fold hz e)

actual-world : ∀ n → proj₂ (proj₁ (Actual.cw n)) ≡ hz
actual-world zero = refl
actual-world (suc n) = refl

coordinates : ∀ n → Rel hz (Actual.ce n) (Pure.ce n)
coordinates zero = floor-rel zero
coordinates (suc n) = rel-add (coordinates n) (act-bridge (coordinates n) (Actual.cw n))

outputs : ∀ n → Same (Actual.oo n) (Pure.oo n)
outputs zero = fold-bridge (coordinates zero) zz (floor zero)
outputs (suc n) = fold-bridge (coordinates (suc n)) zz (Actual.ce (suc n))
sums : ∀ n → Same (Actual.oO n) (Pure.oO n)
sums zero = outputs zero
sums (suc n) = same-add (sums n) (outputs (suc n))

old2 : Same (Old.TΩ (num 2) tt) (hl Pure.oO)
old2 = ll sums
```

此定理识别原旧闭项的所有反馈坐标与输出和；尚非它与 normalized 1
之间的值比较，也没有声称旧第二地板已通过记号标签验收。
