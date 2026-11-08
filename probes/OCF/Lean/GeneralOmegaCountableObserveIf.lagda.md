# 普通可数高度上的直接typed观察接口

高度只取Cd；目标t与种类秩r+1都在同一合法B中比较。复用CRwFold
已编译的分类、along与真实坐标回送，不复用它的两段折叠。

新实验的ℕ层地板取原分量的累计和：这由HB的ℕ合法性需要选择，
可直接保第一位置，不是假设不同sup分量逐点步进。它与原typed参照
逐点Ω地板的基本列不同，值桥须另证，不因验收方便改旧定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObserveIf where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
import OCF.Lean.CRwFold as Base
module C = Base I₁

F : Cd → KS
F = C.Tw S⊥
floor : ∀ B → HB (F B)
floor = C.topT S⊥ (hs hz)
classify : ∀ B → LgB B → ∀ t → t ⊲ B → (κ : K (F B)) → C.Dc F B t (E (F B) κ)
classify B lB t pt κ = C.dcl pt lB (C.cl B κ)

iterate : ∀ {A : Set} → (A → A) → A → ℕ → A
iterate f a zero = a
iterate f a (suc n) = f (iterate f a n)
leftMul : ∀ {S : KS} → HB S → ℕ → HB S
leftMul a zero = hz
leftMul a (suc n) = a ⊞ leftMul a n

node : ∀ {B t A} → t ⊲ B → C.Dc F B t A →
  (∀ r → r ⊲ B → A → HB (F r)) → HB (F t)
node {t = t} pt (C.keep κ fr) rec = hΩ κ (λ e → rec t pt (fr e))
node {t = t} pt (C.same to) rec = hl (λ n → rec t pt
  (to (iterate (λ e → rec t pt (to e)) (floor t) n)))
node {t = t} pt (C.above r pr tr to) rec = hl (λ n → rec t pt
  (to (iterate (λ e → rec r (⊲ᴮ-tr (hsuc hself) pr) (to e)) (floor r) n)))

record Observer : Set₁ where
  field
    observe : ∀ B → LgB B → ∀ t → t ⊲ B → HB (F B) → HB (F t)
    at-zero : ∀ B lB t pt → observe B lB t pt hz ≡ floor t
    at-successor : ∀ B lB t pt a → observe B lB t pt (hs a) ≡ hl (leftMul (observe B lB t pt a))
    at-limit : ∀ B lB t pt f → observe B lB t pt (hl f) ≡ hl (λ n → observe B lB t pt (f n))
    at-node : ∀ B lB t pt κ f → observe B lB t pt (hΩ κ f) ≡
      node pt (classify B lB t pt κ) (λ r pr e → observe B lB r pr (f e))
```

same与above的反馈均在当前节点自己的低层HB内；above只改变坐标
计算的目标，不把已折树再折一遍。rec始终处理同一原源分支f的子树。
分类不使不同第一位置证明无关；keep保留实际along所选拷贝。
