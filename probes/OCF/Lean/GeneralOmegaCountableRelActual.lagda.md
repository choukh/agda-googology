# 原Γ输入与目标零层的值消费

这里直接使用原累计地板、原观察器和原Γ输入。关系保持的结论只在
目标零层转成可数树同形及双向值比较；不把中间层普通Same当作
遗传坐标关系，也不把两个不同高度的Γ输入作比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableRelActual where
open import Data.Nat using (ℕ)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (rawΓ; stage)
open import OCF.Lean.GeneralOmegaCountableRelIf
open import OCF.Lean.GeneralOmegaCountableRelRun
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo; same-value; same-sym)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

zero-same : ∀ {a b} → Rel hz a b → Same a b
zero-same rz = zz
zero-same (rs p) = ss (zero-same p)
zero-same (rl p) = ll (λ n → zero-same (p n))
zero-same (ro {κ = ()} p)
observe-same : ∀ B lB pt {a b} → Rel B a b →
  Same (observe B lB hz pt a) (observe B lB hz pt b)
observe-same B lB pt r = zero-same (observe-related B lB hz pt r)
related-value : ∀ B lB pt {a b} → Rel B a b →
  observe B lB hz pt a ≤ᵛ observe B lB hz pt b
related-value B lB pt r = same-value (observe-same B lB pt r)
related-value-back : ∀ B lB pt {a b} → Rel B a b →
  observe B lB hz pt b ≤ᵛ observe B lB hz pt a
related-value-back B lB pt r = same-value (same-sym (observe-same B lB pt r))

Γ-input-related : ∀ c → Rel (leg c) (floor (leg c)) (floor (leg c))
Γ-input-related c = floor-related (leg c)
Γ-output-related : ∀ c → Rel hz (rawΓ c) (rawΓ c)
Γ-output-related c = observe-related (leg c) (Lg-leg c) hz (z⊲ᴮ (leg c)) (Γ-input-related c)
all-stage-inputs : ∀ n → Rel (leg (stage n))
  (floor (leg (stage n))) (floor (leg (stage n)))
all-stage-inputs n = Γ-input-related (stage n)

zero-prefix : ∀ {B a b} → Rel B a b → Rel B (hz ⊞ a) b
zero-prefix rz = rz
zero-prefix (rs p) = rs (zero-prefix p)
zero-prefix (rl p) = rl (λ n → zero-prefix (p n))
zero-prefix (ro p) = ro (λ r → zero-prefix (p r))
Γ-zero-prefix : ∀ c → Same
  (observe (leg c) (Lg-leg c) hz (z⊲ᴮ (leg c)) (hz ⊞ floor (leg c)))
  (rawΓ c)
Γ-zero-prefix c = observe-same (leg c) (Lg-leg c) (z⊲ᴮ (leg c))
  (zero-prefix (Γ-input-related c))
Γ-zero-prefix-value : ∀ c →
  observe (leg c) (Lg-leg c) hz (z⊲ᴮ (leg c)) (hz ⊞ floor (leg c)) ≤ᵛ rawΓ c
Γ-zero-prefix-value c = same-value (Γ-zero-prefix c)
Γ-zero-prefix-back : ∀ c → rawΓ c ≤ᵛ
  observe (leg c) (Lg-leg c) hz (z⊲ᴮ (leg c)) (hz ⊞ floor (leg c))
Γ-zero-prefix-back c = same-value (same-sym (Γ-zero-prefix c))
```

全高度地板证书实际用于每个Γ迭代输入。最后三条在原运行器内部
消去字面零前缀，经过完整反馈链，不使用高层值序的函数单调性。
这是可组合的结构/值接口，不是Γ提升强度、完成保值或EBO验收。
