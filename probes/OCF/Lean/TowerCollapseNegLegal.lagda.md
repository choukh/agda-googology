# 逐支保留旧节点与部分和折叠不保合法

针对定稿 `TowerCollapseIf` 的实际方程。反例不使用最高新节点，
因此失败与回灌链选择无关；只用零、后继、ℕ-极限与保留旧节点四条律。
旧种类坐标在源目标中定义相同，问题是分支单调，不是坐标反变。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerCollapseNegLegal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf
open import OCF.Lean.NegCRwInst using (num; fI; Lg-fI; one⊲fI; module AccNMᶜ)

old-coordinate : ∀ (S : KS) (k : K S) → E (step S) (inj₁ k) ≡ E S k
old-coordinate S k = refl

module Failure (S : KS) (F : Collapse S) where
  open Collapse F
  open Ops S
  M : ℕ → HB S
  M = partial (λ _ → fold hz)
  G : ℕ → HB S
  G = partial (λ n → fold (fI n))

  M-num : ∀ n → M n ≡ num (suc n)
  M-num zero = at-zero
  M-num (suc n) = trans (cong (λ a → M n ⊞ a) at-zero) (cong hs (M-num n))

  not-first : ∀ {w} → fold (hs hz) ⊲[ w ] fold (hl fI) → ⊥
  not-first = AccNMᶜ.acc-not-mono
    (fold hz) (fold (hs hz)) (fold (hl fI)) M G
    at-zero (at-suc hz) M-num (at-lim fI) refl (λ n → refl)

S₁ = step S⊥
S₂ = step S₁

branch : Cd → HB S₂
branch hz = hs hz
branch (hs c) = hl fI
branch (hl f) = hl fI

branch-legal : ∀ c → LgB (branch c)
branch-legal hz = tt
branch-legal (hs c) = Lg-fI
branch-legal (hl f) = Lg-fI

branch-mono : ∀ {v c d} → c ⊲ d → branch c ⊲[ v ] branch d
branch-mono {c = hz} {d = hz} p = hself
branch-mono {c = hz} {d = hs d} p = one⊲fI
branch-mono {c = hz} {d = hl f} p = one⊲fI
branch-mono {c = hs c} {d = hz} ()
branch-mono {c = hs c} {d = hs d} p = hself
branch-mono {c = hs c} {d = hl f} p = hself
branch-mono {c = hl f} {d = hz} ()
branch-mono {c = hl f} {d = hs d} p = hself
branch-mono {c = hl f} {d = hl g} p = hself

input : HB S₂
input = hΩ (inj₁ (inj₂ tt)) branch

input-legal : LgB input
input-legal = (λ lw b c p → branch-mono p) , (λ { {c = c} lw b → branch-legal c })

no-preserves-legal : (F : Collapse S₁) → PreservesLegal S₁ F → ⊥
no-preserves-legal F P = Failure.not-first S₁ F bad
  where
  folded-legal : LgB (hΩ (inj₂ tt) (λ c → Collapse.fold F (branch c)))
  folded-legal = subst LgB (Collapse.keep F (inj₂ tt) branch)
    (PreservesLegal.legal P input input-legal)
  bad : Collapse.fold F (hs hz) ⊲[ tt , hs hz ] Collapse.fold F (hl fI)
  bad = proj₁ folded-legal {w = tt , hs hz} {c = hz} {c′ = hs hz}
    (tt , tt) (hsuc hself) hself (hsuc hself)
```

反例输入有完整合法证书。参与比较的坐标 0、1 在同一合法世界
`(tt,1)` 有字面公共界 1；没有裸下标上的比较假设。
`Collapse` 本身有构造路 `Run.instance-fold` 实例，否定仅针对
额外的 `PreservesLegal`，不否定总折叠存在，更不否定所有一步折叠。
翻译账：未改前三级定义；旧引理复用只看三个输出的部分和反例。
