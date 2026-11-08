# 双槽比较的真实旧轨道及前缀闭包

所有自证从地板与原act生成；不会由有向关系擅取右端自证。特别是
旧第三地板的每个真实最高坐标、所有前缀阶段都能实例化联合比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TwoSlotValueClosure where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; prefix-rel; floor-value)
open import OCF.Align.BoundedWorldValueTwoSlot using (mid; low)
open import OCF.Align.BoundedWorldCoverIf using (act)
open import OCF.Lean.TwoSlotValueRun using (value-repeat; middle; lower)
import OCF.Align.BoundedWorldValueWhole as Whole

act-positive : ∀ c a → Value c (hs hz) (act a)
act-positive c hz = vs vz
act-positive c (hs a) = vli 0 (act-positive c a)
act-positive c (hl f) = vli 0 (act-positive c (f 0))
act-positive c (hΩ κ g) = vor (λ e → act-positive c (g e))

act-mono : ∀ {c a b} → Value c a b → Value c (act a) (act b)
act-mono {c} {b = b} vz = act-positive c b
act-mono (vs p) = value-repeat (act-mono p)
act-mono (vr p) = vli 0 (act-mono p)
act-mono (vl p) = vl (λ n → act-mono (p n))
act-mono (vli n p) = vli n (act-mono p)
act-mono (vo p) = vo (λ x y r → act-mono (p x y r))
act-mono (vor p) = vor (λ e → act-mono (p e))

act-inflate : ∀ {c a b} → Value c a b → Value c a (act b)
act-inflate vz = vz
act-inflate {c} {b = hs b} (vs p) = vli 1 (add-rel (act-inflate p) (act-positive c b))
act-inflate (vr p) = vli 0 (act-inflate p)
act-inflate (vl p) = vl (λ n → act-inflate (p n))
act-inflate (vli n p) = vli n (act-inflate p)
act-inflate (vo p) = vo (λ x y r → act-inflate (p x y r))
act-inflate (vor p) = vor (λ e → act-inflate (p e))

coordinate-self : ∀ n → Value (num 1) (Whole.Model.ce n) (Whole.Model.ce n)
coordinate-self zero = floor-value 1
coordinate-self (suc n) = add-rel (coordinate-self n) (act-mono (coordinate-self n))
coordinate-step : ∀ n → Value (num 1) (Whole.Model.ce n) (Whole.Model.ce (suc n))
coordinate-step n = prefix-rel (coordinate-self n) _

input-prefix : ∀ {a b p q u v x y} → Value (num 1) p q → Value (num 1) a b →
  Value hz u v → x ≤ᵛ y → low x u (p ⊞ a) ≤ᵛ low y v (q ⊞ b)
input-prefix pq ab uv xy = lower (add-rel pq ab) uv xy
middle-prefix : ∀ {a b p q u v} → Value (num 1) p q → Value (num 1) a b →
  Value hz u v → Value hz (mid u (p ⊞ a)) (mid v (q ⊞ b))
middle-prefix pq ab uv = middle (add-rel pq ab) uv

actual-lower : ∀ n {u v x y} → Value hz u v → x ≤ᵛ y →
  low x u (Whole.Model.ce n) ≤ᵛ low y v (Whole.Model.ce n)
actual-lower n uv xy = lower (coordinate-self n) uv xy
actual-middle : ∀ n {u v} → Value hz u v →
  Value hz (mid u (Whole.Model.ce n)) (mid v (Whole.Model.ce n))
actual-middle n uv = middle (coordinate-self n) uv
```

这些结论包括读取中槽的非零前缀，而不限于up输入；仍然只是同一双槽
解释器的联合单调与闭包，尚不等于被固定seed的Uniform解释覆盖。
