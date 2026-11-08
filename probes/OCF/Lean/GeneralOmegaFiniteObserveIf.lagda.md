# 有限原step塔的直接无累加观察接口

实验规则受typed折叠启发：目标零点为目标地板（0层为1），后继列
从0份开始，旧低Ω保留，同/高Ω在节点自己的低层上作无累加反馈。
这里只使用有限塔路径Within，所有目标及反馈层均有字面公共界n；
不比较任意LH下标，也不改已有候选。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaFiniteObserveIf where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-step)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase

F : ℕ → KS
F zero = S⊥
F (suc n) = step (F n)
floor : ∀ n → HB (F n)
floor zero = hs hz
floor (suc n) = hΩ (inj₂ tt) up

data Within : ℕ → ℕ → Set where
  here : ∀ {n} → Within n n
  lower : ∀ {n m} → Within n m → Within (suc n) m
bound : ∀ {n m} → Within n m → m ≤ n
bound here = refl≤ where
  refl≤ : ∀ {n} → n ≤ n
  refl≤ {n = zero} = z≤n
  refl≤ {n = suc n} = s≤s refl≤
bound (lower p) = ≤-step (bound p)

-- A是当前源种类的原坐标类型；keep不换低层HB。
data View (n m : ℕ) (A : Set) : Set where
  keep : (κ : K (F m)) → (E (F m) κ → A) → View n m A
  collapse : (k : ℕ) → Within n k → (HB (F k) → A) → View n m A

raise : ∀ {n m A} → View n m A → View (suc n) m A
raise (keep κ fr) = keep κ fr
raise (collapse k p to) = collapse k (lower p) to
view : ∀ {n m} → Within n m → (κ : K (F n)) → View n m (E (F n) κ)
view here κ = keep κ (λ e → e)
view (lower p) (inj₁ κ) = raise (view p κ)
view (lower {n} p) (inj₂ _) = collapse n (lower here) (λ e → e)

iterate : ∀ {A : Set} → (A → A) → A → ℕ → A
iterate f a zero = a
iterate f a (suc n) = f (iterate f a n)
leftMul : ∀ {S : KS} → HB S → ℕ → HB S
leftMul a zero = hz
leftMul a (suc n) = a ⊞ leftMul a n

node : ∀ {n m A} (p : Within n m) → View n m A →
  (∀ k → Within n k → A → HB (F k)) → HB (F m)
node {m = m} p (keep κ fr) rec = hΩ κ (λ e → rec m p (fr e))
node {m = m} p (collapse k q to) rec = hl (λ i → rec m p
  (to (iterate (λ e → rec k q (to e)) (floor k) i)))

record Observer : Set₁ where
  field
    observe : ∀ {n m} → Within n m → HB (F n) → HB (F m)
    at-zero : ∀ {n m} (p : Within n m) → observe p hz ≡ floor m
    at-successor : ∀ {n m} (p : Within n m) a → observe p (hs a) ≡ hl (leftMul (observe p a))
    at-limit : ∀ {n m} (p : Within n m) f → observe p (hl f) ≡ hl (λ i → observe p (f i))
    at-node : ∀ {n m} (p : Within n m) κ f → observe p (hΩ κ f) ≡
      node p (view p κ) (λ k q e → observe q (f e))
```

Within n m本身是共同有限界证据，collapse还显式给反馈层k的同界证据。
没有坐标商、函数外延或世界单槽更新；完整实现与闭项另给。
