# 保留实际前缀值的纯后缀双向验收

纯后缀不必把前缀降到常量1。对任意LH层、任意含Ω前缀A，实际run
的后缀值正是以run A为基值的纯解释P。结论只按纯后缀递归，因而
不要求任意Ω分支函数保值关系，也不把Same直接送过run。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaConsumeValueSuffix where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.HigherIndexConsumePositive using (mul-partial; add-mono)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.LHRecTy using (Lv)
open import OCF.Lean.LHRecLay using (ΛL; twL)
open import OCF.Lean.LHRecFl using (ΣF)
open import OCF.Align.FrozenAbsorbNegUpper using (P)
open import OCF.Align.GeneralOmegaConsumeValuePure using (Pure; pz; ps; pl)
open import OCF.Align.GeneralOmegaConsumeValueClosed using (encoded; encoded-pure)

partial-mul : ∀ {a b : Cd} → a ≤ᵛ b → ∀ n →
  Ops.partial S⊥ (λ _ → a) n ≤ᵛ mul b n
partial-mul p zero = p
partial-mul p (suc n) = add-mono (partial-mul p n) p

suffix-lower : ∀ x {d a} → Pure d a → ∀ A → P (run x A) d ≤ᵛ run x (A ⊞ a)
suffix-lower x pz A = ≤-refl _
suffix-lower x (ps p) A = l≤ (λ n → ≤l n (mul-partial (suffix-lower x p A) n))
suffix-lower x (pl p) A = l≤ (λ n → ≤l n (suffix-lower x (p n) A))
suffix-upper : ∀ x {d a} → Pure d a → ∀ A → run x (A ⊞ a) ≤ᵛ P (run x A) d
suffix-upper x pz A = ≤-refl _
suffix-upper x (ps p) A = l≤ (λ n → ≤l n (partial-mul (suffix-upper x p A) n))
suffix-upper x (pl p) A = l≤ (λ n → ≤l n (suffix-upper x (p n) A))

pure-proof : ∀ S d → Pure d (pure S d)
pure-proof S hz = pz
pure-proof S (hs d) = ps (pure-proof S d)
pure-proof S (hl f) = pl (λ n → pure-proof S (f n))
all-prefix-lower : ∀ x A d → P (run x A) d ≤ᵛ run x (A ⊞ pure (Lv x) d)
all-prefix-lower x A d = suffix-lower x (pure-proof (Lv x) d) A
all-prefix-upper : ∀ x A d → run x (A ⊞ pure (Lv x) d) ≤ᵛ P (run x A) d
all-prefix-upper x A d = suffix-upper x (pure-proof (Lv x) d) A

-- 前缀逐字取原完整源的第1个累加分量，包含真实Ω节点；非零纯样本不能替代它。
actual-prefix-lower : ∀ d → P (run ΛL (ΣF twL 1)) d ≤ᵛ
  run ΛL (ΣF twL 1 ⊞ encoded d)
actual-prefix-lower d = suffix-lower ΛL (encoded-pure d) (ΣF twL 1)
actual-prefix-upper : ∀ d → run ΛL (ΣF twL 1 ⊞ encoded d) ≤ᵛ
  P (run ΛL (ΣF twL 1)) d
actual-prefix-upper d = suffix-upper ΛL (encoded-pure d) (ΣF twL 1)
```

两向界覆盖全部d。actual-prefix的基值就是前篇已经证明覆盖整个
Old.TΩ1的原分量值，但本篇没有把这些纯后缀族定位为原第2站的全部
回灌，也没有证明EBO阶段覆盖。这是一条可供下一步分析真实高Ω
前缀时使用的结构定理，不是新强度的读法声明。
