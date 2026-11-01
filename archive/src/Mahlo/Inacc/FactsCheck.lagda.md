# `OTFacts` 的机器求值测试

关掉 `OTFacts` 之前先做的健全性检查：对 size ≤ k 的全部项（三分、传递对**全部 T′ 项**，其余对 OT 项），把每个字段的布尔版用 `refl` 跑一遍。这不是证明——只能揪出写错的陈述。每条一个 `_ = refl`，失败可定位。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.FactsCheck where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith
open import Mahlo.Inacc.Enum

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.ListAction using (all; any)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixr 2 _⇒_
_⇒_ : Bool → Bool → Bool
a ⇒ b = not a ∨ b

-- 测试范围
-- 规模（实测）：|enumT 3| = 9，|enumT 4| = 100，|enumT 5| = 11801；|ots 4| = 20，|ots 5| = 197。
-- 三重循环用小集合，二重与单重用大一号的集合。
T4 T5 : List Tm                   -- 全部 T′ 项
T4 = enumT 3
T5 = enumT 4
O5 O6 : List Tm                   -- OT 项
O5 = ots 4
O6 = ots 5

all2 : List Tm → (Tm → Tm → Bool) → Bool
all2 xs f = all (λ x → all (λ y → f x y) xs) xs

all3 : List Tm → (Tm → Tm → Tm → Bool) → Bool
all3 xs f = all (λ x → all (λ y → all (λ z → f x y z) xs) xs) xs

isψ : Tm → Bool                   -- ⟨ psi κ c ⟩ 形状
isψ (zer ▹ psi _ _) = true
isψ _ = false
```

## 检查器（布尔函数）

```agda
-- ψ_κ c ≺ κ；κ ≠ I 时 κ⁻ ≺ ψ_κ c 且 κ⁻ ≺ κ
chkψκ : Tm → Bool
chkψκ (zer ▹ psi (ΩR b) c) = lt (zer ▹ psi (ΩR b) c) ⟨ Om b ⟩ ∧ lt (κ⁻ (ΩR b)) (zer ▹ psi (ΩR b) c) ∧ lt (κ⁻ (ΩR b)) ⟨ Om b ⟩
chkψκ (zer ▹ psi IR c)     = lt (zer ▹ psi IR c) I′
chkψκ _ = true

-- κ⁻ ≺ κ、Ω₁ ⪯ κ（κ ∈ R′ ∩ OT）
chkR : Tm → Bool
chkR (zer ▹ Om a) = isRT (zer ▹ Om a) ⇒ (lt (κ⁻ (ΩR a)) (zer ▹ Om a) ∧ le Ω₁ (zer ▹ Om a))
chkR (zer ▹ I)    = le Ω₁ I′
chkR _ = true

-- 1 ⪯ 主元项
chk1 : Tm → Bool
chk1 (zer ▹ p) = le one (zer ▹ p)
chk1 _ = true

-- φ-cmp
chkφcmp : Tm → Tm → Bool
chkφcmp (zer ▹ phi d₁ d₂) (zer ▹ phi b c) =
  lt (zer ▹ phi d₁ d₂) (zer ▹ phi b c)
  ⇒ ((lt d₁ b ∧ lt d₂ (zer ▹ phi b c)) ∨ (eqT d₁ b ∧ lt d₂ c) ∨ (lt b d₁ ∧ le (zer ▹ phi d₁ d₂) c))
chkφcmp _ _ = true

-- ψ≺Car⇒κ⪯
chkψCar : Tm → Tm → Bool
chkψCar (zer ▹ psi (ΩR z) c) d = (isCarT d ∧ lt (zer ▹ psi (ΩR z) c) d) ⇒ le ⟨ Om z ⟩ d
chkψCar _ _ = true

-- 2.15 (c)
chk215c : Tm → Tm → Bool
chk215c (zer ▹ psi κ a) u =
  lt u (regTm κ) ⇒ ((inC̃ κ a u ⇒ lt u (zer ▹ psi κ a)) ∧ (lt u (zer ▹ psi κ a) ⇒ inC̃ κ a u))
chk215c _ _ = true

-- 2.15 (d)
chk215d : Tm → Tm → Bool
chk215d (zer ▹ psi π d) (zer ▹ psi IR a) =
  inC̃ IR a (zer ▹ psi π d) ⇒ (lt (zer ▹ psi π d) (zer ▹ psi IR a) ∨ (inC̃ IR a (regTm π) ∧ inC̃ IR a d ∧ lt d a))
chk215d _ _ = true

-- 2.15 (e)
chk215e : Tm → Tm → Bool
chk215e (zer ▹ psi π d) (zer ▹ psi (ΩR z) a) =
  inC̃ (ΩR z) a (zer ▹ psi π d) ⇒ (le (zer ▹ psi π d) (κ⁻ (ΩR z)) ∨ (inC̃ (ΩR z) a (regTm π) ∧ inC̃ (ΩR z) a d ∧ lt d a))
chk215e _ _ = true

-- ψκ-mono 与 ψI-cmp
chkψmono : Tm → Tm → Bool
chkψmono (zer ▹ psi κ b) (zer ▹ psi κ′ d) =
  eqR κ κ′ ⇒ ((lt b d ⇒ lt (zer ▹ psi κ b) (zer ▹ psi κ′ d)) ∧ (isI κ ⇒ (lt (zer ▹ psi κ b) (zer ▹ psi κ′ d) ⇒ lt b d)))
chkψmono _ _ = true

-- Car≺κ⇒⪯κ⁻
chkCarκ : Tm → Tm → Bool
chkCarκ c (zer ▹ Om z) = (isCarT c ∧ isRT (zer ▹ Om z) ∧ lt c (zer ▹ Om z)) ⇒ le c (κ⁻ (ΩR z))
chkCarκ _ _ = true

-- plus-κ⁻
chkplusκ : Tm → Bool
chkplusκ (zer ▹ Om z) = isRT (zer ▹ Om z) ⇒ eqT (plus (κ⁻ (ΩR z))) (zer ▹ Om z)
chkplusκ _ = true

-- κ⁻∘plus
chkκplus : Tm → Tm → Bool
chkκplus τ (zer ▹ Om z) = eqT (κ⁻ (ΩR z)) τ
chkκplus _ _ = false

-- Fi-form
chkFiform : Tm → Tm → Bool
chkFiform x (zer ▹ psi IR b) = isOT (zer ▹ psi IR b) ∧ eqT (pFi x) ⟨ psi IR (b + one) ⟩ ∧ lt x ⟨ psi IR (b + one) ⟩
chkFiform _ _ = false
```

## Lemma 2.4（对全部 T′ 项）

```agda
_ : all (λ x → not (lt x x)) T5 ≡ true
_ = refl

_ : all2 T5 (λ x y → lt x y ∨ eqT x y ∨ lt y x) ≡ true
_ = refl

_ : all3 T4 (λ x y z → (lt x y ∧ lt y z) ⇒ lt x z) ≡ true
_ = refl

_ : all (λ x → le zer x) T5 ≡ true
_ = refl
```

## Remark 2.12 (h)(a)、子项界

```agda
_ : all2 O5 (λ y z → (not (isZero z) ∧ isOT (app y z)) ⇒ le y (app y z)) ≡ true
_ = refl
_ : all2 O5 (λ y z → (not (isZero y) ∧ not (isZero z) ∧ isOT (app y z)) ⇒ le z (app y z)) ≡ true
_ = refl
_ : all2 O5 (λ b c → isOT ⟨ phi b c ⟩ ⇒ (le b ⟨ phi b c ⟩ ∧ le c ⟨ phi b c ⟩)) ≡ true
_ = refl
_ : all (λ b → isOT ⟨ Om b ⟩ ⇒ le b ⟨ Om b ⟩) O5 ≡ true
_ = refl
_ : all chkψκ O6 ≡ true
_ = refl
_ : all chkR O6 ≡ true
_ = refl
_ : all chk1 O6 ≡ true
_ = refl
_ : all2 O5 (λ x y → isOT (x + y) ∧ isOT (φ x y)) ≡ true
_ = refl
```

## (≺′i) 的读出、结构性质

```agda
-- between-app：b ≺ d ≺ b + c ⟹ d = b + d′，0 ≺ d′ ≺ c（在 T5 里找 d′）
_ : all3 O5 (λ b c d → (not (isZero b) ∧ not (isZero c) ∧ isOT (app b c) ∧ lt b d ∧ lt d (app b c))
                       ⇒ any (λ d′ → eqT d (app b d′) ∧ not (isZero d′) ∧ lt d′ c) T5) ≡ true
_ = refl
_ : all2 O6 chkφcmp ≡ true
_ = refl
-- φ≺G
_ : all3 O5 (λ b c d → (isGT d ∧ isOT ⟨ phi b c ⟩ ∧ lt b d ∧ lt c d) ⇒ lt ⟨ phi b c ⟩ d) ≡ true
_ = refl
-- Fi≺Ω⇒⪯；Ω-mono⁻
_ : all2 O6 (λ y b → (isFiT y ∧ isOT ⟨ Om b ⟩ ∧ lt y ⟨ Om b ⟩) ⇒ le y b) ≡ true
_ = refl
_ : all2 O5 (λ y b → (isOT ⟨ Om y ⟩ ∧ isOT ⟨ Om b ⟩ ∧ lt ⟨ Om y ⟩ ⟨ Om b ⟩) ⇒ lt y b) ≡ true
_ = refl
_ : all2 O6 chkψCar ≡ true
_ = refl
```

## Remark 2.15

```agda
_ : all2 O6 chk215c ≡ true
_ = refl
_ : all2 O6 chk215d ≡ true
_ = refl
_ : all2 O6 chk215e ≡ true
_ = refl
_ : all2 O6 chkψmono ≡ true
_ = refl
_ : all2 O6 chkCarκ ≡ true
_ = refl
_ : all chkplusκ O6 ≡ true
_ = refl
_ : all (λ τ → isCarT τ ⇒ chkκplus τ (plus τ)) O6 ≡ true
_ = refl
```

## Def 2.13 / Remark 2.14

```agda
_ : all (λ x → isOT (tilde x) ∧ le (tilde x) x ∧ (isCarT (tilde x) ∨ isZero (tilde x))
              ∧ eqT (tilde (tilde x)) (tilde x)
              ∧ isOT (plus x) ∧ lt x (plus x) ∧ isCarT (plus x)
              ∧ eqT (plus (tilde x)) (plus x) ∧ le (mFi x) x ∧ isOT (mFi x)
              ∧ (isFiT (mFi x) ∨ isZero (mFi x))) O6 ≡ true
_ = refl
_ : all2 O6 (λ x κ → (isCarT κ ∧ le κ x) ⇒ le κ (tilde x)) ≡ true
_ = refl
_ : all2 O6 (λ x κ → (isCarT κ ∧ lt x κ) ⇒ le (plus x) κ) ≡ true
_ = refl
_ : all (λ x → any (λ y → eqT (plus x) ⟨ Om (y ▹ phi zer zer) ⟩ ∧ eqT (Ω y) (tilde x)) T5) O5 ≡ true
_ = refl
```

## Ω、Fi′、+1

```agda
_ : all2 O5 (λ y a → (isOT ⟨ Om a ⟩ ∧ lt y a) ⇒ lt (Ω y) ⟨ Om a ⟩) ≡ true
_ = refl
_ : all2 O6 (λ f y → (isFiT f ∧ lt y f) ⇒ lt (Ω y) f) ≡ true
_ = refl
_ : all2 O6 (λ κ y → (isCarT κ ∧ lt y κ) ⇒ lt (y + one) κ) ≡ true
_ = refl
_ : all2 O5 (λ x y → le x y ⇒ (le (x + one) (y + one) ∧ le (Ωⁿ x 1) (Ωⁿ y 1) ∧ le (Ωⁿ x 2) (Ωⁿ y 2))) ≡ true
_ = refl
_ : all (λ x → isOT (Ωⁿ x 1) ∧ isOT (Ωⁿ x 2)) O5 ≡ true
_ = refl
_ : all (λ z → isFiT z ⇒ le ψI0 z) O6 ≡ true
_ = refl
_ : all2 O6 (λ z x → (isFiT z ∧ isOT ⟨ psi IR (x + one) ⟩ ∧ lt z ⟨ psi IR (x + one) ⟩) ⇒ le z ⟨ psi IR x ⟩) ≡ true
_ = refl
_ : all2 O5 (λ b c → lt b c ⇒ le (b + one) c) ≡ true
_ = refl
_ : all (λ x → lt x I′ ⇒ (lt x (Ωⁿ (mFi x + one) 0) ∨ lt x (Ωⁿ (mFi x + one) 1) ∨ lt x (Ωⁿ (mFi x + one) 2)
                          ∨ lt x (Ωⁿ (mFi x + one) 3) ∨ lt x (Ωⁿ (mFi x + one) 4))) O6 ≡ true
_ = refl
_ : all (λ x → (le ψI0 x ∧ lt x I′) ⇒ chkFiform x (mFi x)) O6 ≡ true
_ = refl
_ : all (λ x → lt x ψI0 ⇒ eqT (pFi x) ψI0) O6 ≡ true
_ = refl
```
