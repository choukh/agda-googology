# 否定: 黑箱闭包上没有最小的读位置

> 不含记号. 结论写在 [GuardTight](GuardTight.lagda.md). **`no-min`: 若每个合法闭包都有最小的读位置, 则 WLPO.** 反例族的分支是常数, 非平凡的只是下界 $c_y=\lim Y_y$. 读位置给出的 $a$ 模前序就是 $c_y$, 所以是 1 还是 2 就回答了 $y$ 全假与否. 所以**落地的规则不能代替读位置的证据**: `Tc` 必须是层号证书的一部分 (与 `WFˢ` 同档), 由闭包的结构给. 字面的闭包给得出 ([GuardTightRd](GuardTightRd.lagda.md)); 对任意的 `WFˢ` 给不出.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardTightNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Free.Level using (Ordᴵ; _<ᴵ_; _⊑ᴵ_; _≅ᴵ_; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑; ≅ᴵ-refl; ⊑ᴵ-trans; ⊑ᴵ-refl)
open import OCF.Align.GuardTightLv
open Lv Dom₀
open import OCF.Align.GuardTightBase
```

## §1 反例族

```agda
one two three : Ordᴵ
one = suc zero
two = suc one
three = suc two

any : (ℕ → Bool) → ℕ → Bool
any y zero    = y zero
any y (suc n) = any y n ∨ y (suc n)

sel : Bool → Ordᴵ
sel true  = two
sel false = one

Y : (ℕ → Bool) → ℕ → Ordᴵ
Y y n = sel (any y n)

one⊑two : one ⊑ᴵ two
one⊑two = s⊑ z≅ (suc zero)

⊑two : ∀ x → sel x ⊑ᴵ two
⊑two true = ⊑ᴵ-refl
⊑two false = one⊑two

one⊑sel : ∀ x → one ⊑ᴵ sel x
one⊑sel true = one⊑two
one⊑sel false = ⊑ᴵ-refl

sel-∨ : ∀ a b → sel a ⊑ᴵ sel (a ∨ b)
sel-∨ true b = ⊑ᴵ-refl
sel-∨ false b = one⊑sel b

Y-step : ∀ y n → Y y n ⊑ᴵ Y y (suc n)
Y-step y n = sel-∨ (any y n) (y (suc n))

cY : (ℕ → Bool) → Ordᴵ
cY y = lim (Y y) (Y-step y)

X : LG
X = suc (suc zero)

g₀ : (y : ℕ → Bool) (η : Ordᴵ) → cY y ⊑ᴵ η → LG
g₀ y η e = X

Cl : (ℕ → Bool) → LG
Cl y = lc (cY y) zero (g₀ y)

X≈ : X ≈ X
X≈ = s≈ (s≈ z≈)

Cf-Cl : ∀ y → Cfˢ (Cl y)
Cf-Cl y = ((λ η e → ⊴-zero) , (λ η e η′ e′ d → ≈→⊴ X≈) , tt , (λ η e → tt)) , o≈ (≅ᴵ-refl (cY y)) z≈ (λ η e η′ e′ k → X≈)

-- 最小的读位置
Min : (y : ℕ → Bool) → Rdr (cY y) zero (g₀ y) → Set
Min y rd = ∀ η e {k} (P : Cp k X) {rep} a ea l (d : Lk k rep) Q tr → rd η e P ≡ rdB a ea l d Q tr → ∀ η′ → cY y ⊑ᴵ η′ → a ⊑ᴵ η′
```

## §2 定理

```agda
¬two⊑one : two ⊑ᴵ one → ⊥
¬two⊑one (s⊑ () zero)
¬two⊑one (s⊑ e (suc ()))

¬three⊑one : three ⊑ᴵ one → ⊥
¬three⊑one (s⊑ () zero)
¬three⊑one (s⊑ e (suc ()))

any-true : ∀ y m → y m ≡ true → any y m ≡ true
any-true y zero e = e
any-true y (suc m) e = ∨-r (any y m) e
  where
  ∨-r : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
  ∨-r true r = refl
  ∨-r false r = r

any-false : ∀ y → (∀ n → y n ≡ false) → ∀ m → any y m ≡ false
any-false y h zero = h zero
any-false y h (suc m) = ∨-f (any-false y h m) (h (suc m))
  where
  ∨-f : ∀ {a b} → a ≡ false → b ≡ false → (a ∨ b) ≡ false
  ∨-f refl r = r

c⊑one : ∀ y → (∀ n → y n ≡ false) → cY y ⊑ᴵ one
c⊑one y h = l⊑ (λ n → subst (λ b → sel b ⊑ᴵ one) (sym (any-false y h n)) ⊑ᴵ-refl)

c⊑three : ∀ y → cY y ⊑ᴵ three
c⊑three y = l⊑ (λ n → go (any y n))
  where
  go : ∀ b → sel b ⊑ᴵ three
  go true = s⊑ (s≅ z≅) (suc zero)
  go false = s⊑ z≅ (suc (suc zero))

Dec′ : Set → Set
Dec′ A = A ⊎ (A → ⊥)

no-min : (∀ y → Σ (Rdr (cY y) zero (g₀ y)) (Min y)) → ∀ y → Dec′ (∀ n → y n ≡ false)
no-min H y with proj₁ (H y) three (c⊑three y) self | proj₂ (H y) three (c⊑three y) self
... | rdF (inj₁ ()) self _ | _
... | rdF (inj₂ ()) self _ | _
... | rdB a ea l d Q tr | m = decide a ea l (m a ea l d Q tr refl)
  where
  from-big : ∀ {a} → (a ⊑ᴵ one → ⊥) → (∀ η′ → cY y ⊑ᴵ η′ → a ⊑ᴵ η′) → Dec′ (∀ n → y n ≡ false)
  from-big no mn = inj₂ (λ h → no (mn one (c⊑one y h)))

  from-one : cY y ⊑ᴵ one → Dec′ (∀ n → y n ≡ false)
  from-one (l⊑ k) = inj₁ (λ n → go n (y n) refl)
    where
    go : ∀ n b → y n ≡ b → y n ≡ false
    go n false r = r
    go n true r = ⊥-elim (¬two⊑one (subst (λ b → sel b ⊑ᴵ one) (any-true y n r) (k n)))

  decide : ∀ a → cY y ⊑ᴵ a → a ⊲ three → (∀ η′ → cY y ⊑ᴵ η′ → a ⊑ᴵ η′) → Dec′ (∀ n → y n ≡ false)
  decide .three ea ⊲= mn = from-big ¬three⊑one mn
  decide zero (l⊑ k) (⊲ˢ h) mn with k zero
  ... | ek = ⊥-elim (abs (any y zero) ek)
    where
    abs : ∀ b → sel b ⊑ᴵ zero → ⊥
    abs true (s⊑ _ ())
    abs false (s⊑ _ ())
  decide (suc b) ea (⊲ˢ h) mn with h {three} (λ r → r)
  ... | zero = from-big ¬three⊑one mn
  ... | suc zero = from-big ¬two⊑one mn
  ... | suc (suc zero) = from-one ea
  ... | suc (suc (suc ()))
  decide (lim f s) ea (⊲ˢ h) mn with h {three} (λ r → r)
  ... | suc (suc (suc ()))
```
