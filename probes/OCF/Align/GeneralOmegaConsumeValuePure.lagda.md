# 新全Ω解释器的统一纯后缀下界

值验收专用。直接递归新run，而非借旧消费者的输出等式。任意LH层、
任意前缀都适用，包括前缀本身含Ω的情形。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaConsumeValuePure where
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; z≤; l≤; ≤l)
open import OCF.Lean.LHRecTy using (LH; Lv)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.HigherIndexConsumePositive using (old-act; mul-partial)

positive : ∀ x a → hs hz ≤ᵛ run x a
positive x hz = s≤s z≤
positive x (hs a) = ≤l 0 (positive x a)
positive x (hl f) = ≤l 0 (positive x (f 0))
positive x (hΩ κ f) = ≤l 0 (positive x (f (code x κ (hs hz))))

data Pure {S : KS} : Cd → HB S → Set where
  pz : Pure hz hz
  ps : ∀ {d a} → Pure d a → Pure (hs d) (hs a)
  pl : ∀ {f g} → (∀ n → Pure (f n) (g n)) → Pure (hl f) (hl g)

pure-suffix : ∀ x {d a} → Pure d a → ∀ A → old-act d ≤ᵛ run x (A ⊞ a)
pure-suffix x pz A = positive x A
pure-suffix x (ps p) A = l≤ (λ n → ≤l n (mul-partial (pure-suffix x p A) n))
pure-suffix x (pl p) A = l≤ (λ n → ≤l n (pure-suffix x (p n) A))
```

Pure只记录0/后继/ℕ极限结构，没有标签或阶段参数。原old-act是旧
TΩ1的真实纯坐标动作；整闭包覆盖须再模拟旧反馈，不能从一步界直接
宣称终点强度。
