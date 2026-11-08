# 原可数输出的独立合法化候选

保留原运行器与原闭项不变，另定义对整个输出取 leg 的候选。
这不是原输出合法性的证明，也不是 ψ₀Λ 的值验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedThetaRouteLeg where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (Σ₀; leg; Lg-leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Align.BoundedNativeValueFirst using (right≤)
open import OCF.Align.BoundedNativeValueStrict using (strict-old-lower)
import OCF.Align.BoundedNativeFloor as N
import OCF.Lean.Fold1 as Old

member-sum : ∀ (f : ℕ → Cd) n → f n ≤ᵛ Σ₀ f n
member-sum f zero = ≤-refl _
member-sum f (suc n) = right≤ _ _

raw-below-leg : ∀ c → c ≤ᵛ leg c
raw-below-leg hz = z≤
raw-below-leg (hs c) = s≤s (raw-below-leg c)
raw-below-leg (hl f) = l≤ (λ n → ≤l n
  (≤-trans (raw-below-leg (f n)) (member-sum (λ j → leg (f j)) n)))

candidate : Cd
candidate = leg N.countable-output

legal-candidate : LgB candidate
legal-candidate = Lg-leg N.countable-output

strict-lower : hs Old.TΩ1 ≤ᵛ candidate
strict-lower = ≤-trans strict-old-lower (raw-below-leg N.countable-output)

not-bounded-by-old : candidate ≤ᵛ Old.TΩ1 → ⊥
not-bounded-by-old p = ¬s≤ᵛ Old.TΩ1 (≤-trans strict-lower p)
```

候选本身是合法可数布劳威尔树，故内部 View 就是其树构造子。
所得值定理是严格超过旧 TΩ1 的下界，不给 EBO 下界或本候选的值上界。
leg 改变所有 ℕ 极限的分支为部分和，不能由上述单向不等式反推原输出合法，
也不能宣称值保持。实际输出结构的上界是下一验收义务。

翻译账：无记号新增规则；合法化由树自身的第一位置步进要求驱动，
代价是额外累加，当前未证明其值代价。此文件是独立备选数据，不替换主定义。
