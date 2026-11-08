# 全有限深度与轮数方格：不假设对角调度充分

每个外阶段 `k` 用同一个上轮可数输出，实际执行所有
`depth≤k`、`rounds≤k` 的配置。每格仍是原完整高源的输出驱动世界，
再经全部底下降；不是把给定数值表并起来。零轮也列入，用于精确覆盖
所有有限配置。方格比单条对角重复计算更多，但不需要深度、轮数或
输入种子的值单调性。公平枚举不等于 EBO 强度证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenGrid where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (FGH)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l; l≤)
open import OCF.Lean.NegFold1Base using (≤ᵛ-trans; ≤⊞)
open import OCF.Lean.OutputDrivenValue using (right)
import OCF.Lean.OutputDrivenFamily as Family
import OCF.Lean.OutputDrivenDown as Down

-- 长度为k的有限和；右递归使格点包含证明无需判等自然数。
sum : (ℕ → Cd) → ℕ → Cd
sum f zero = hz
sum f (suc k) = f zero ⊞ sum (λ n → f (suc n)) k

sum-legal : ∀ f → (∀ n → LgB (f n)) → ∀ k → LgB (sum f k)
sum-legal f lf zero = tt
sum-legal f lf (suc k) = Lg-⊞ _ _ (lf zero)
  (sum-legal (λ n → f (suc n)) (λ n → lf (suc n)) k)

item : ∀ f {n k} → n < k → f n ≤ᵛ sum f k
item f {n = zero} {k = suc k} (s≤s z≤n) = ≤⊞ (f zero) (sum (λ n → f (suc n)) k)
item f {n = suc n} {k = suc k} (s≤s p) = ≤ᵛ-trans
  (item (λ n → f (suc n)) p) (right (f zero) (sum (λ n → f (suc n)) k))

module At (c : Cd) (lc : LgB c) where
  cell : ℕ → ℕ → Cd
  cell depth rounds = Down.With.TN (Family.Family.worlds rounds (hs c) lc)
    (Family.Family.legal rounds (hs c) lc) depth

  cell-legal : ∀ depth rounds → LgB (cell depth rounds)
  cell-legal depth rounds = Down.With.legal-TN (Family.Family.worlds rounds (hs c) lc)
    (Family.Family.legal rounds (hs c) lc) depth

  row : ℕ → ℕ → Cd
  row k d = sum (cell d) (suc k)

  block : ℕ → Cd
  block k = sum (row k) (suc k)

  block-legal : ∀ k → LgB (block k)
  block-legal k = sum-legal (row k)
    (λ d → sum-legal (cell d) (cell-legal d) (suc k)) (suc k)

  cell-in-block : ∀ {d r k} → d ≤ k → r ≤ k → cell d r ≤ᵛ block k
  cell-in-block {d} {r} {k} pd pr = ≤ᵛ-trans
    (item (cell d) (s≤s pr)) (item (row k) (s≤s pd))

y : ℕ → Cd
legal-y : ∀ k → LgB (y k)
y zero = hz
y (suc k) = y k ⊞ At.block (y k) (legal-y k) k
legal-y zero = tt
legal-y (suc k) = Lg-⊞ _ _ (legal-y k) (At.block-legal (y k) (legal-y k) k)

closedGrid : Cd
closedGrid = hl y

legal-closedGrid : LgB closedGrid
legal-closedGrid = (λ k → ⊞-fst (y k) (At.block (y k) (legal-y k) k)) , legal-y

cell-in-closed : ∀ {d r k} → d ≤ k → r ≤ k →
  At.cell (y k) (legal-y k) d r ≤ᵛ closedGrid
cell-in-closed {d} {r} {k} pd pr = ≤l (suc k)
  (≤ᵛ-trans (At.cell-in-block (y k) (legal-y k) pd pr)
    (right (y k) (At.block (y k) (legal-y k) k)))

fghGrid : ℕ → ℕ
fghGrid = FGH closedGrid
```

包含定理里的格点保留其真实阶段种子 `y k`。没有把不同阶段或不同合法证的
格点视作相等，也没有据枚举推出固定种子下的全域支配。
