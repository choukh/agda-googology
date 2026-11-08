# 实际一步降层：保留旧种类，消去新种类

接口定稿 2026-11-06。方向更正：HB(step S) → HB S 时，旧种类
inj₁ κ 的坐标就是 E S κ，不需要反向回缩；新种类的 HB S 坐标
由折叠输出回灌生成，不作为 Keep 保留。世界索引路线并未被固定为约束。

后继取 ω 次重复，零取一；这避免把恒等解释器冒充坍缩。
这些规则仍是候选选择，不宣称满足 ψ 的值规格。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TowerCollapseIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase

module Ops (S : KS) where
  partial : (ℕ → HB S) → ℕ → HB S
  partial f zero = f zero
  partial f (suc n) = partial f n ⊞ f (suc n)
  sum : (ℕ → HB S) → HB S
  sum f = hl (partial f)
  repeat : HB S → HB S
  repeat a = sum (λ _ → a)
  orbit : (HB S → HB S) → ℕ → HB S
  orbit h zero = hs hz
  orbit h (suc n) = orbit h n ⊞ h (orbit h n)
  collapse : (HB S → HB S) → HB S
  collapse h = sum (λ n → h (orbit h n))

record Collapse (S : KS) : Set₁ where
  open Ops S
  field
    fold : HB (step S) → HB S
    at-zero : fold hz ≡ hs hz
    at-suc : ∀ a → fold (hs a) ≡ repeat (fold a)
    at-lim : ∀ f → fold (hl f) ≡ sum (λ n → fold (f n))
    keep : ∀ κ g → fold (hΩ (inj₁ κ) g) ≡ hΩ κ (λ c → fold (g c))
    remove : ∀ g → fold (hΩ (inj₂ tt) g) ≡ collapse (λ c → fold (g c))

-- 输出合法性单列为待验证义务，不能由折叠方程自动宣称。
record PreservesLegal (S : KS) (F : Collapse S) : Set₁ where
  field
    legal : ∀ a → LgB a → LgB (Collapse.fold F a)
```

输入旧节点合法只保证源分支的第一位置单调；折叠后是否仍单调
是实质问题。所有输入比较律均由原 KS 携带公共世界的界证据。
