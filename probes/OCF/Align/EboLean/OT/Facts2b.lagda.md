# OTFacts（二 b）：a^{−Fi}、a^{+Fi} 与 Remark 2.14 (i)

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.Facts2b` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

接 [Facts2](Facts2.lagda.md)。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.Facts2b where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.Arith
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OTLemmas
open import OCF.Align.EboLean.OT.OrderProps using (ltLx; lt-list)
open import OCF.Align.EboLean.OT.Unfold
open import OCF.Align.EboLean.OT.Linear
open import OCF.Align.EboLean.OT.Trans hiding (G)
open import OCF.Align.EboLean.OT.Lex
open import OCF.Align.EboLean.OT.Subterm
open import OCF.Align.EboLean.OT.Facts1
open import OCF.Align.EboLean.OT.Facts2

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (+-comm)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ; ∨-identityʳ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
```

## 5. a^{−Fi}、a^{+Fi}（Remark 2.14 (g)(i)）

```agda
mFi-view : ∀ x → FiView (mFi x) ⊎ mFi x ≡ zer
mFi-view zer         = inj₂ refl
mFi-view (a ▹ q ▹ p) = mFi-view (a ▹ q)
mFi-view (zer ▹ phi b c) with caseEq (lt b c)
... | inj₁ e = subst (λ v → FiView v ⊎ v ≡ zer) (sym (if-true {b = lt b c} {x = mFi c} {y = mFi b} e)) (mFi-view c)
... | inj₂ e = subst (λ v → FiView v ⊎ v ≡ zer) (sym (if-false {b = lt b c} {x = mFi c} {y = mFi b} e)) (mFi-view b)
mFi-view (zer ▹ psi (ΩR b) c) = mFi-view b
mFi-view (zer ▹ psi IR c)     = inj₁ (fiψ c)
mFi-view (zer ▹ Om b)         = mFi-view b
mFi-view (zer ▹ I)            = inj₁ fiI



OT-ψΩ-lev : ∀ b c → OT ⟨ psi (ΩR b) c ⟩ → OT b
OT-ψΩ-lev b c o = proj₁ (OT-Ω⁻ (proj₁ (proj₂ (OT-ψ⁻ o))))


Fi⪯b⇒≺ψΩ : ∀ f → (FiView f ⊎ f ≡ zer) → ∀ b c → le f b ≡ true → lt f ⟨ psi (ΩR b) c ⟩ ≡ true
Fi⪯b⇒≺ψΩ f (inj₂ refl) b c _ = lt-zer zer (psi (ΩR b) c)
Fi⪯b⇒≺ψΩ f (inj₁ (fiψ d)) b c l =
  unf⁻ (psi IR d) (psi (ΩR b) c) refl (∨ˡ (lt ⟨ psi IR d ⟩ ⟨ Om b ⟩) false (unf⁻ (psi IR d) (Om b) refl l))
Fi⪯b⇒≺ψΩ f (inj₁ fiI) b c l =
  unf⁻ I (psi (ΩR b) c) refl (not-≡false (cong (_∨ false) (trans (lt-unfold≠ (Om b) I refl) (⪯⇒¬≺ b ⟨ I ⟩ (le! l)))))

mFi⪯′ : ∀ x → OT x → le (mFi x) x ≡ true
mFi⪯′ zer _ = leʳ zer zer refl
mFi⪯′ (a ▹ q ▹ p) o = leˡ (mFi (a ▹ q)) (a ▹ q ▹ p) (lt≡ (⪯≺-trans {mFi (a ▹ q)} {a ▹ q} {a ▹ q ▹ p} (le! (mFi⪯′ (a ▹ q) (proj₁ (OT-+⁻ o)))) (lt! (≺-▹ (a ▹ q) p))))
mFi⪯′ (zer ▹ phi b c) o with OT-φ⁻ o | caseEq (lt b c)
... | ob , oc , _ , _ | inj₁ e = subst (λ v → le v ⟨ phi b c ⟩ ≡ true) (sym (if-true {b = lt b c} {x = mFi c} {y = mFi b} e))
                                    (leˡ (mFi c) ⟨ phi b c ⟩ (lt≡ (⪯≺-trans {mFi c} {c} {⟨ phi b c ⟩} (le! (mFi⪯′ c oc)) (lt! (≺-φʳ b c)))))
... | ob , oc , _ , _ | inj₂ e = subst (λ v → le v ⟨ phi b c ⟩ ≡ true) (sym (if-false {b = lt b c} {x = mFi c} {y = mFi b} e))
                                    (leˡ (mFi b) ⟨ phi b c ⟩ (lt≡ (⪯≺-trans {mFi b} {b} {⟨ phi b c ⟩} (le! (mFi⪯′ b ob)) (lt! (≺-φˡ b c)))))
mFi⪯′ (zer ▹ psi (ΩR b) c) o = leˡ (mFi b) ⟨ psi (ΩR b) c ⟩ (Fi⪯b⇒≺ψΩ (mFi b) (mFi-view b) b c (mFi⪯′ b (OT-ψΩ-lev b c o)))
mFi⪯′ (zer ▹ psi IR c) _ = leʳ ⟨ psi IR c ⟩ ⟨ psi IR c ⟩ (eqT-refl ⟨ psi IR c ⟩)
mFi⪯′ (zer ▹ Om b) o = leˡ (mFi b) ⟨ Om b ⟩ (lt≡ (⪯≺-trans {mFi b} {b} {⟨ Om b ⟩} (le! (mFi⪯′ b (proj₁ (OT-Ω⁻ o)))) (lt! (≺-Ωa b))))
mFi⪯′ (zer ▹ I) _ = leʳ ⟨ I ⟩ ⟨ I ⟩ refl

mFi⪯ : ∀ {x} → OT x → mFi x ⪯ x
mFi⪯ {x} o = le! (mFi⪯′ x o)

-- Fi′ 元素 f ⪯ x ⟹ f ⪯ x^{−Fi}（x^{−Fi} 是 x 以下最大的 Fi′ 元素）












ψΩ≺I : ∀ b c → lt ⟨ psi (ΩR b) c ⟩ ⟨ I ⟩ ≡ true → lt b ⟨ I ⟩ ≡ true
ψΩ≺I b c h with ∨-true (unf (psi (ΩR b) c) I h)
... | inj₁ g = unf (Om b) I g
... | inj₂ z = ⊥-elim (true≢false (sym z))


```

## 6. Remark 2.14 (i)：x ≺ Ωⁿ_{x^{−Fi}+1}

```agda












```
