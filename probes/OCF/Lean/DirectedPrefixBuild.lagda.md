# 前缀定向律的全种类实例与完整可数反馈

实填共享算法，不改变 point/unary。高层结论使用全裸坐标的原树值关系；
不是世界观察保持。可数反馈只用 point 单调，未假定 unary 单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.DirectedPrefixBuild where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.DirectedPrefixIf
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω; mul)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans; ⊞≤ˡ; ⊞≤ʳ; mul≤)

module _ {S : KS} where
  right : ∀ (a b : HB S) → b ≤ᵛ (a ⊞ b)
  right a hz = z≤
  right a (hs b) = s≤s (right a b)
  right a (hl f) = l≤ (λ n → ≤l n (right a (f n)))
  right a (hΩ κ g) = Ω≤Ω (λ e → right a (g e))

  in-sums : ∀ (f : ℕ → HB S) n → f n ≤ᵛ sums f n
  in-sums f zero = ≤ᵛ-refl _
  in-sums f (suc n) = right (sums f n) (f (suc n))

  lower : ∀ (η A a : HB S) → η ≤ᵛ unary A → point η a ≤ᵛ unary (A ⊞ a)
  lower η A hz p = p
  lower η A (hs a) p = l≤ (λ n → ≤l n (mul≤ (lower η A a p) n))
  lower η A (hl f) p = l≤ (λ n → ≤l n
    (≤ᵛ-trans (lower η A (f n) p) (in-sums _ n)))
  lower η A (hΩ κ g) p = Ω≤Ω (λ e → lower η A (g e) p)

  positive : ∀ (a : HB S) → hs hz ≤ᵛ unary a
  positive hz = s≤s z≤
  positive (hs a) = ≤l zero (positive a)
  positive (hl f) = ≤l zero (positive (f zero))
  positive (hΩ κ g) = ≤Ω (bot S κ) (positive (g (bot S κ)))

  inflation : ∀ (a : HB S) → a ≤ᵛ unary a
  inflation hz = z≤
  inflation (hs a) = ≤l (suc zero)
    (≤ᵛ-trans (s≤s (inflation a)) (⊞≤ʳ (unary a) (positive a)))
  inflation (hl f) = l≤ (λ n → ≤l n
    (≤ᵛ-trans (inflation (f n)) (in-sums _ n)))
  inflation (hΩ κ g) = Ω≤Ω (λ e → inflation (g e))

instance-lower : PrefixLower
instance-lower = record { lower = lower }

base-point : ∀ (η a : Cd) → η ≤ᵛ point η a
base-point η hz = ≤ᵛ-refl η
base-point η (hs a) = ≤l zero (base-point η a)
base-point η (hl f) = ≤l zero (base-point η (f zero))

point-mono : ∀ (η : Cd) {a b} → a ≤ᵛ b → point η a ≤ᵛ point η b
point-mono η (z≤ {b}) = base-point η b
point-mono η (s≤s p) = l≤ (λ n → ≤l n (mul≤ (point-mono η p) n))
point-mono η (≤s p) = ≤l zero (point-mono η p)
point-mono η (l≤ p) = l≤ (λ n → point-mono η (p n))
point-mono η (≤l n p) = ≤l n (point-mono η p)
point-mono η (≤Ω {κ = ()} e p)
point-mono η (Ω≤Ω {κ = ()} p)

module Feedback (η A seed : Cd) (p : η ≤ᵛ unary A) where
  old new : ℕ → Cd
  old zero = seed
  old (suc n) = point η (old n)
  new zero = seed
  new (suc n) = unary (A ⊞ new n)

  coordinates : ∀ n → old n ≤ᵛ new n
  coordinates zero = ≤ᵛ-refl seed
  coordinates (suc n) = ≤ᵛ-trans (point-mono η (coordinates n))
    (lower η A (new n) p)

  whole : hl old ≤ᵛ hl new
  whole = l≤ (λ n → ≤l n (coordinates n))

-- 每棵实际 Cd 都填上前提，不仅零或固定样本。
module Actual (A seed : Cd) = Feedback A A seed (inflation A)
```

这里覆盖整个无界反馈列。point 在 Cd 上与旧验收纯算子 P 的逐构造子
规则相同；本树侧证明不导入该验收闭包。完整 same/above 折叠与 EBO
尚未由此改写，后续接原运行必须另证真实输出对应。
