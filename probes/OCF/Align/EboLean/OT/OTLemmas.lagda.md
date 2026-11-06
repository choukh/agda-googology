# `isOT` 的拆合

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.OTLemmas` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

`OT` 是布尔谓词的包装；这里把 `isOT` 各支的 `∧` 链拆成分量，供良序证明按 =NF 形状取子项的 OT 性（Remark 2.12 (d)）。不依赖序理论。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.OTLemmas where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.BoolLemmas

open import Data.Bool.Base using (Bool; true; false; _∧_; not)
open import Data.Product using (_×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 消去（子项在 OT）

```agda
OT-+⁻ : ∀ {a q p} → OT (a ▹ q ▹ p) → OT (a ▹ q) × OT ⟨ p ⟩ × ⟨ p ⟩ ⪯ ⟨ q ⟩
OT-+⁻ (ot! e) with ∧-true e
... | e₁ , e₂ with ∧-true e₂
... | e₃ , e₄ = ot! e₁ , ot! e₃ , le! e₄

OT-▹⁻ : ∀ {b r} → NZ b → OT (b ▹ r) → OT b × OT ⟨ r ⟩
OT-▹⁻ {b = _ ▹ _} _ o = let (ob , or , _) = OT-+⁻ o in ob , or

OT-φ⁻ : ∀ {b c} → OT ⟨ phi b c ⟩
      → OT b × OT c × inCr b c ≡ false × (isZero c ∧ isGT b) ≡ false
OT-φ⁻ (ot! e) with ∧-true e
... | e₁ , e₂ with ∧-true e₂
... | e₃ , e₄ with ∧-true e₄
... | e₅ , e₆ = ot! e₁ , ot! e₃ , not-true e₅ , not-true e₆

OT-ψ⁻ : ∀ {κ c} → OT ⟨ psi κ c ⟩
      → OT c × OT (regTm κ) × isRR κ ≡ true × allLt (G κ c) c ≡ true
OT-ψ⁻ {κ = ΩR a} (ot! e) with ∧-true e
... | e₁ , e₂ with ∧-true e₂
... | e₃ , e₄ with ∧-true e₄
... | e₅ , e₆ = ot! e₁ , ot! e₃ , e₅ , e₆
OT-ψ⁻ {κ = IR} (ot! e) with ∧-true e
... | e₁ , e₂ with ∧-true e₂
... | e₃ , e₄ with ∧-true e₄
... | e₅ , e₆ = ot! e₁ , ot! e₃ , e₅ , e₆

OT-Ω⁻ : ∀ {b} → OT ⟨ Om b ⟩ → OT b × isFiT b ≡ false × isZero b ≡ false
OT-Ω⁻ (ot! e) with ∧-true e
... | e₁ , e₂ with ∧-true e₂
... | e₃ , e₄ = ot! e₁ , not-true e₃ , not-true e₄
```

## 引入

```agda
OT-+⁺ : ∀ {a q p} → OT (a ▹ q) → OT ⟨ p ⟩ → ⟨ p ⟩ ⪯ ⟨ q ⟩ → OT (a ▹ q ▹ p)
OT-+⁺ (ot! e₁) (ot! e₂) (le! e₃) = ot! (∧-intro e₁ (∧-intro e₂ e₃))

OT-▹⁺ : ∀ {b r} → NZ b → OT b → OT ⟨ r ⟩ → le ⟨ r ⟩ ⟨ lastP b ⟩ ≡ true → OT (b ▹ r)
OT-▹⁺ {b = _ ▹ q} _ (ot! e₁) (ot! e₂) e₃ = ot! (∧-intro e₁ (∧-intro e₂ e₃))



OT-Ω⁺ : ∀ {b} → OT b → isFiT b ≡ false → isZero b ≡ false → OT ⟨ Om b ⟩
OT-Ω⁺ (ot! e₁) e₂ e₃ = ot! (∧-intro e₁ (∧-intro (not-≡false e₂) (not-≡false e₃)))

OT-0 : OT zer
OT-0 = ot! refl

OT-I : OT I′
OT-I = ot! refl
```
