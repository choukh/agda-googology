# 原 mid/low 的联合有向语义

两个槽同时比较。中Ω的坐标链由mid生成，输出由low生成；底Ω的
回灌只更新底槽。所有数组仍是原Fold1.Col，未用两段折叠代替low。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TwoSlotValueRun where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; l≤; ≤l)
open import OCF.Lean.Fold1Base using (mul-≤)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel)
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V; mid; low)
open import OCF.Lean.TwoSlotValueIf
import OCF.Lean.Fold1Fold as F

value-mul : ∀ {c a b} → Value c a b → ∀ n → Value c (mul a n) (mul b n)
value-mul p zero = p
value-mul p (suc n) = add-rel (value-mul p n) p
value-repeat : ∀ {c a b} → Value c a b → Value c (hl (mul a)) (hl (mul b))
value-repeat p = vl (λ n → vli n (value-mul p n))

middle-positive : ∀ u (a : HB V) → Value hz (hs hz) (mid u a)
middle-positive u hz = vs vz
middle-positive u (hs a) = vli 0 (middle-positive u a)
middle-positive u (hl f) = vli 0 (middle-positive u (f 0))
middle-positive u (hΩ (inj₁ (inj₁ ())) g)
middle-positive u (hΩ (inj₁ (inj₂ _)) g) = vor (λ c → middle-positive u (g c))
middle-positive u (hΩ (inj₂ _) g) = vli 0 (middle-positive u (g u))

lower-positive : ∀ x u (a : HB V) → hs hz ≤ᵛ low x u a
lower-positive x u hz = OCF.Lean.Fold1If.s≤s OCF.Lean.Fold1If.z≤
lower-positive x u (hs a) = ≤l 0 (lower-positive x u a)
lower-positive x u (hl f) = ≤l 0 (lower-positive x u (f 0))
lower-positive x u (hΩ (inj₁ (inj₁ ())) g)
lower-positive x u (hΩ (inj₁ (inj₂ _)) g) = ≤l 0 (lower-positive x u (g x))
lower-positive x u (hΩ (inj₂ _) g) = ≤l 0 (lower-positive x u (g u))

middle : ∀ {a b u v} → Value (num 1) a b → Value hz u v →
  Value hz (mid u a) (mid v b)
middle {b = b} {v = v} vz uv = middle-positive v b
middle (vs p) uv = value-repeat (middle p uv)
middle (vr p) uv = vli 0 (middle p uv)
middle (vl p) uv = vl (λ n → middle (p n) uv)
middle (vli n p) uv = vli n (middle p uv)
middle (vo {κ = inj₁ (inj₁ ())} p) uv
middle (vo {κ = inj₁ (inj₂ _)} p) uv = vo (λ x y xy → middle (p x y xy) uv)
middle {u = u} {v} (vo {κ = inj₂ _} {f} {g} p) uv = vl (λ n → vli n (sums n))
  where
  module L = F.Col _⊞_ _⊞_ u u (λ _ e → e)
    (λ b e → mid b (f e)) (λ b e → mid b (f e))
  module R = F.Col _⊞_ _⊞_ v v (λ _ e → e)
    (λ b e → mid b (g e)) (λ b e → mid b (g e))
  coordinates : ∀ n → Value hz (L.ce n) (R.ce n)
  outputs : ∀ n → Value hz (L.oo n) (R.oo n)
  coordinates zero = uv
  coordinates (suc n) = add-rel (coordinates n) (outputs n)
  outputs zero = middle (p u v uv) uv
  outputs (suc n) = middle (p _ _ (coordinates (suc n))) (coordinates (suc n))
  sums : ∀ n → Value hz (L.oO n) (R.oO n)
  sums zero = outputs zero
  sums (suc n) = add-rel (sums n) (outputs (suc n))
middle (vor {κ = inj₁ (inj₁ ())} p) uv
middle (vor {κ = inj₁ (inj₂ _)} p) uv = vor (λ c → middle (p c) uv)
middle {v = v} (vor {κ = inj₂ _} p) uv = vli 0 (middle (p v) uv)

lower : ∀ {a b u v x y} → Value (num 1) a b → Value hz u v → x ≤ᵛ y →
  low x u a ≤ᵛ low y v b
lower {b = b} {v = v} {y = y} vz uv xy = lower-positive y v b
lower (vs p) uv xy = l≤ (λ n → ≤l n (mul-≤ (lower p uv xy) n))
lower (vr p) uv xy = ≤l 0 (lower p uv xy)
lower (vl p) uv xy = l≤ (λ n → lower (p n) uv xy)
lower (vli n p) uv xy = ≤l n (lower p uv xy)
lower (vo {κ = inj₁ (inj₁ ())} p) uv xy
lower {u = u} {v} {x} {y} (vo {κ = inj₁ (inj₂ _)} {f} {g} p) uv xy = l≤ (λ n → ≤l n (sums n))
  where
  module L = F.Col _⊞_ _⊞_ x x (λ _ e → e)
    (λ x′ e → low x′ u (f e)) (λ x′ e → low x′ u (f e))
  module R = F.Col _⊞_ _⊞_ y y (λ _ e → e)
    (λ y′ e → low y′ v (g e)) (λ y′ e → low y′ v (g e))
  coordinates : ∀ n → L.ce n ≤ᵛ R.ce n
  outputs : ∀ n → L.oo n ≤ᵛ R.oo n
  coordinates zero = xy
  coordinates (suc n) = add-mono (coordinates n) (outputs n)
  outputs zero = lower (p x y xy) uv xy
  outputs (suc n) = lower (p _ _ (coordinates (suc n))) uv (coordinates (suc n))
  sums : ∀ n → L.oO n ≤ᵛ R.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))
lower {u = u} {v} {x} {y} (vo {κ = inj₂ _} {f} {g} p) uv xy = l≤ (λ n → ≤l n (sums n))
  where
  module L = F.Col _⊞_ _⊞_ u u (λ _ e → e)
    (λ b e → mid b (f e)) (λ b e → low x b (f e))
  module R = F.Col _⊞_ _⊞_ v v (λ _ e → e)
    (λ b e → mid b (g e)) (λ b e → low y b (g e))
  coordinates : ∀ n → Value hz (L.ce n) (R.ce n)
  advance : ∀ n → Value hz (mid (L.cw n) (f (L.ce n))) (mid (R.cw n) (g (R.ce n)))
  coordinates zero = uv
  coordinates (suc n) = add-rel (coordinates n) (advance n)
  advance zero = middle (p u v uv) uv
  advance (suc n) = middle (p _ _ (coordinates (suc n))) (coordinates (suc n))
  outputs : ∀ n → L.oo n ≤ᵛ R.oo n
  outputs zero = lower (p u v uv) uv xy
  outputs (suc n) = lower (p _ _ (coordinates (suc n))) (coordinates (suc n)) xy
  sums : ∀ n → L.oO n ≤ᵛ R.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))
lower (vor {κ = inj₁ (inj₁ ())} p) uv xy
lower {y = y} (vor {κ = inj₁ (inj₂ _)} p) uv xy = ≤l 0 (lower (p y) uv xy)
lower {v = v} (vor {κ = inj₂ _} p) uv xy = ≤l 0 (lower (p v) uv xy)

instance-joint : JointComparison
instance-joint = record { middle = middle ; lower = lower }
```

两种Ω各自的全部ce、oo、oO均在联合关系下比较，不只比较第零项。
结论不包含没有Value证据的任意高层输入，也不提供C或EBO上界。
