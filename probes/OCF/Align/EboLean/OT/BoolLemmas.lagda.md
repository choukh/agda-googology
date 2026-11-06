# 布尔与句法相等的平凡性质

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.BoolLemmas` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

`_≺_`、`_⪯_`、`OT` 都是 `… ≡ true`。这里放不依赖序理论的小引理：`∧` 的拆合、`eqT` 是自反的且蕴含相等、`≺ ⟹ ⪯`。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.BoolLemmas where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

∧-true : ∀ {x y} → x ∧ y ≡ true → x ≡ true × y ≡ true
∧-true {x = true} {y = true} refl = refl , refl

∧-intro : ∀ {x y} → x ≡ true → y ≡ true → x ∧ y ≡ true
∧-intro refl refl = refl

∨-true : ∀ {x y} → x ∨ y ≡ true → x ≡ true ⊎ y ≡ true
∨-true {x = true}             refl = inj₁ refl
∨-true {x = false} {y = true} refl = inj₂ refl

∨-introˡ : ∀ {x y} → x ≡ true → x ∨ y ≡ true
∨-introˡ refl = refl

∨-introʳ : ∀ {x y} → y ≡ true → x ∨ y ≡ true
∨-introʳ {x = true}  refl = refl
∨-introʳ {x = false} refl = refl

not-true : ∀ {x} → not x ≡ true → x ≡ false
not-true {x = false} refl = refl


not-≡false : ∀ {x} → x ≡ false → not x ≡ true
not-≡false refl = refl


true≢false : ¬ (true ≡ false)
true≢false ()

if-true : ∀ {ℓ} {A : Set ℓ} {b : Bool} {x y : A} → b ≡ true → (if b then x else y) ≡ x
if-true refl = refl

if-false : ∀ {ℓ} {A : Set ℓ} {b : Bool} {x y : A} → b ≡ false → (if b then x else y) ≡ y
if-false refl = refl
```

## 句法相等

```agda
mutual
  eqT-refl : ∀ a → eqT a a ≡ true
  eqT-refl zer     = refl
  eqT-refl (a ▹ p) = ∧-intro (eqT-refl a) (eqP-refl p)

  eqP-refl : ∀ p → eqP p p ≡ true
  eqP-refl (phi a b) = ∧-intro (eqT-refl a) (eqT-refl b)
  eqP-refl (psi π b) = ∧-intro (eqR-refl π) (eqT-refl b)
  eqP-refl (Om a)    = eqT-refl a
  eqP-refl I         = refl

  eqR-refl : ∀ π → eqR π π ≡ true
  eqR-refl (ΩR a) = eqT-refl a
  eqR-refl IR     = refl

mutual
  eqT-sound : ∀ a b → eqT a b ≡ true → a ≡ b
  eqT-sound zer     zer     _ = refl
  eqT-sound (a ▹ p) (b ▹ q) e with ∧-true e
  ... | e₁ , e₂ rewrite eqT-sound a b e₁ | eqP-sound p q e₂ = refl

  eqP-sound : ∀ p q → eqP p q ≡ true → p ≡ q
  eqP-sound (phi a b) (phi c d) e with ∧-true e
  ... | e₁ , e₂ rewrite eqT-sound a c e₁ | eqT-sound b d e₂ = refl
  eqP-sound (psi π b) (psi κ d) e with ∧-true e
  ... | e₁ , e₂ rewrite eqR-sound π κ e₁ | eqT-sound b d e₂ = refl
  eqP-sound (Om a)    (Om c)    e rewrite eqT-sound a c e = refl
  eqP-sound I         I         _ = refl

  eqR-sound : ∀ π κ → eqR π κ ≡ true → π ≡ κ
  eqR-sound (ΩR a) (ΩR c) e rewrite eqT-sound a c e = refl
  eqR-sound IR     IR     _ = refl

eqT-complete : ∀ {a b} → a ≡ b → eqT a b ≡ true
eqT-complete {a} refl = eqT-refl a
```

## ≺ 与 ⪯

```agda
≺⇒⪯ : ∀ {s t} → s ≺ t → s ⪯ t
≺⇒⪯ (lt! p) = le! (∨-introˡ p)

≡⇒⪯ : ∀ {s t} → s ≡ t → s ⪯ t
≡⇒⪯ e = le! (∨-introʳ (eqT-complete e))

⪯-refl : ∀ {s} → s ⪯ s
⪯-refl = ≡⇒⪯ refl

⪯⇒≺⊎≡ : ∀ {s t} → s ⪯ t → s ≺ t ⊎ s ≡ t
⪯⇒≺⊎≡ {s} {t} (le! p) with ∨-true p
... | inj₁ q = inj₁ (lt! q)
... | inj₂ q = inj₂ (eqT-sound s t q)
```
