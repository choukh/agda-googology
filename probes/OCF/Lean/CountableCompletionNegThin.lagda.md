# 固定原值不能给累加完成的统一上界

本篇检验冻结的 `CountableCompletionRun.instance-completion`，不是否定
该接口的所有实例，也不否定具体终点候选。把后继改成常值极限，得到
原值恒为 1 的树；累加完成仍能读出任意给定树的高度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CountableCompletionNegThin where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ˡ; ⊞-≤ʳ)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Lean.CountableCompletionRun using (inflation; item-sum)

thin : Cd → Cd
thin hz = hs hz
thin (hs x) = hl (λ _ → thin x)
thin (hl f) = hl (λ n → thin (f n))
thin (hΩ () _)

thin-upper : ∀ x → thin x ≤ᵛ hs hz
thin-upper hz = s≤s z≤
thin-upper (hs x) = l≤ (λ _ → thin-upper x)
thin-upper (hl f) = l≤ (λ n → thin-upper (f n))
thin-upper (hΩ () _)

thin-positive : ∀ x → hs hz ≤ᵛ thin x
thin-positive hz = s≤s z≤
thin-positive (hs x) = ≤l 0 (thin-positive x)
thin-positive (hl f) = ≤l 0 (thin-positive (f 0))
thin-positive (hΩ () _)

thin-position : ∀ {x y : Cd} → x ⊲ y → thin x ⊲ thin y
thin-position hself = hself
thin-position (hsuc p) = hlim 0 (thin-position p)
thin-position (hlim n p) = hlim n (thin-position p)
thin-position (hLim {κ = ()} _ _)

thin-legal : ∀ x → LgB x → LgB (thin x)
thin-legal hz lx = tt
thin-legal (hs x) lx = (λ _ → hself) , (λ _ → thin-legal x lx)
thin-legal (hl f) (st , lf) = (λ n → thin-position (st n)) ,
  (λ n → thin-legal (f n) (lf n))
thin-legal (hΩ () _) lx

completed-positive : ∀ x → hs hz ≤ᵛ leg (thin x)
completed-positive x = ≤-trans (thin-positive x) (inflation (thin x))

add-mono : ∀ {a b c d : Cd} → a ≤ᵛ b → c ≤ᵛ d → a ⊞ c ≤ᵛ b ⊞ d
add-mono {b = b} p q = ≤-trans (⊞-≤ˡ p _) (⊞-≤ʳ b q)

recover : ∀ x → x ≤ᵛ leg (thin x)
recover hz = z≤
recover (hs x) = ≤l 1 (add-mono (recover x) (completed-positive x))
recover (hl f) = l≤ (λ n → ≤l n
  (≤-trans (recover (f n)) (item-sum (λ k → leg (thin (f k))) n)))
recover (hΩ () _)
```

否定的前提不是空的：每个候选上界 U 都有下列具体合法见证；它与 1
互相值不超过，但完成后的值不在 U 以下。所有比较均为可数树的值关系，
没有不可数裸下标判等或比较。

```agda
witness : Cd → Cd
witness U = thin (leg (hs U))

witness-legal : ∀ U → LgB (witness U)
witness-legal U = thin-legal (leg (hs U)) (Lg-leg (hs U))

witness-value : ∀ U → (witness U ≤ᵛ hs hz) × (hs hz ≤ᵛ witness U)
witness-value U = thin-upper (leg (hs U)) , thin-positive (leg (hs U))

witness-escapes : ∀ U → leg (witness U) ≤ᵛ U → ⊥
witness-escapes U p = ¬s≤ᵛ U (≤-trans (inflation (hs U))
  (≤-trans (recover (leg (hs U))) p))

no-uniform-upper : ∀ U →
  (∀ a → LgB a → a ≤ᵛ hs hz → leg a ≤ᵛ U) → ⊥
no-uniform-upper U bound = witness-escapes U
  (bound (witness U) (witness-legal U) (thin-upper (leg (hs U))))
```

**范围。** 此结果排除仅凭输入的值界 1（即使加上输入合法性），给这一个
累加完成操作指定统一可数上界。它不排除读取输入结构的上界证明，不排除
其他完成操作，也不涉及具体 `leg Native.countable-output` 的终点上界。

**翻译账。** `thin` 只用树的零、后继、极限及常值分支；没有记号输入。
反例由树侧累加行为逼出，没有新增专属记号证书。
