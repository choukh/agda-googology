# 保原注入与累计前缀的运行上下文

read可含左前缀，故不要求read 0=0。逐构造子整项等式与code-back
直接约束实际函数；原ι和左加法给refl实例，不用put与ι的Same替换。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaIndexOperationalIf where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.GeneralOmegaConsumeIf using (code)

record Context (x y : LH) : Set₁ where
  field
    read : HB (Lv x) → HB (Lv y)
    kind : K (Lv x) → K (Lv y)
    pull : ∀ κ → E (Lv y) (kind κ) → E (Lv x) κ
    r-s : ∀ a → read (hs a) ≡ hs (read a)
    r-l : ∀ f → read (hl f) ≡ hl (λ n → read (f n))
    r-Ω : ∀ κ f → read (hΩ κ f) ≡ hΩ (kind κ) (λ e → read (f (pull κ e)))
    back : ∀ κ d → pull κ (code y (kind κ) d) ≡ code x κ d
open Context public

identity : ∀ x → Context x x
identity x = record { read = λ a → a ; kind = λ κ → κ ; pull = λ κ e → e ;
  r-s = λ a → refl ; r-l = λ f → refl ; r-Ω = λ κ f → refl ; back = λ κ d → refl }
prefix : ∀ x → HB (Lv x) → Context x x
prefix x A = record { read = λ a → A ⊞ a ; kind = λ κ → κ ; pull = λ κ e → e ;
  r-s = λ a → refl ; r-l = λ f → refl ; r-Ω = λ κ f → refl ; back = λ κ d → refl }
sum : ∀ f n → Context (f n) (ll f)
sum f n = record { read = ι n ; kind = λ κ → n , κ ; pull = λ κ e → e ;
  r-s = λ a → refl ; r-l = λ g → refl ; r-Ω = λ κ g → refl ; back = λ κ d → refl }
  where open import Data.Product using (_,_)
compose : ∀ {x y z} → Context y z → Context x y → Context x z
compose k j = record
  { read = λ a → read k (read j a)
  ; kind = λ κ → kind k (kind j κ)
  ; pull = λ κ e → pull j κ (pull k (kind j κ) e)
  ; r-s = λ a → trans (cong (read k) (r-s j a)) (r-s k (read j a))
  ; r-l = λ f → trans (cong (read k) (r-l j f)) (r-l k (λ n → read j (f n)))
  ; r-Ω = λ κ f → trans (cong (read k) (r-Ω j κ f))
      (r-Ω k (kind j κ) (λ e → read j (f (pull j κ e))))
  ; back = λ κ d → trans (cong (pull j κ) (back k (kind j κ) d)) (back j κ d) }
```

任意原ΣF的末项上下文prefix ∘ sum已实例化。composition只复用整项
等式，不涉及函数外延或运行器对任意函数的同余。
