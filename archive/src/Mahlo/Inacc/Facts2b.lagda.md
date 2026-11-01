# OTFacts（二 b）：a^{−Fi}、a^{+Fi} 与 Remark 2.14 (i)

接 [Facts2](Facts2.lagda.md)。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Facts2b where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith
open import Mahlo.Inacc.BoolLemmas
open import Mahlo.Inacc.OTLemmas
open import Mahlo.Inacc.OrderProps using (ltLx; lt-list)
open import Mahlo.Inacc.Unfold
open import Mahlo.Inacc.Linear
open import Mahlo.Inacc.Trans hiding (G)
open import Mahlo.Inacc.Lex
open import Mahlo.Inacc.Subterm
open import Mahlo.Inacc.Facts1
open import Mahlo.Inacc.Facts2

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

fiT : ∀ {X} → FiView X → isFiT X ≡ true
fiT (fiψ d) = refl
fiT fiI     = refl

mFi-Fi : ∀ {x} → OT x → isFiT (mFi x) ≡ true ⊎ mFi x ≡ zer
mFi-Fi {x} _ with mFi-view x
... | inj₁ f = inj₁ (fiT f)
... | inj₂ e = inj₂ e

-- OT ⟨ ψ_{Ω′_b} c ⟩ ⟹ OT b
OT-ψΩ-lev : ∀ b c → OT ⟨ psi (ΩR b) c ⟩ → OT b
OT-ψΩ-lev b c o = proj₁ (OT-Ω⁻ (proj₁ (proj₂ (OT-ψ⁻ o))))

mFi-OT : ∀ {x} → OT x → OT (mFi x)
mFi-OT {x = zer}         o = o
mFi-OT {x = a ▹ q ▹ p}   o = mFi-OT (proj₁ (OT-+⁻ o))
mFi-OT {x = zer ▹ phi b c} o with OT-φ⁻ o | caseEq (lt b c)
... | ob , oc , _ , _ | inj₁ e = subst OT (sym (if-true {b = lt b c} {x = mFi c} {y = mFi b} e)) (mFi-OT oc)
... | ob , oc , _ , _ | inj₂ e = subst OT (sym (if-false {b = lt b c} {x = mFi c} {y = mFi b} e)) (mFi-OT ob)
mFi-OT {x = zer ▹ psi (ΩR b) c} o = mFi-OT (OT-ψΩ-lev b c o)
mFi-OT {x = zer ▹ psi IR c}     o = o
mFi-OT {x = zer ▹ Om b}         o = mFi-OT (proj₁ (OT-Ω⁻ o))
mFi-OT {x = zer ▹ I}            o = OT-I

-- Fi′ 元素或 0，⪯ b ⟹ ≺ ψ_{Ω′_b} c
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
Fi-strict : ∀ {f} → FiView f → ∀ x → (f ≡ x → ⊥) → le f x ≡ true → lt f x ≡ true
Fi-strict f x ne l with ∨-true l
... | inj₁ g = g
... | inj₂ e = ⊥-elim (ne (eqT-sound _ x e))

mFi-max′ : ∀ f → FiView f → ∀ x → OT x → le f x ≡ true → le f (mFi x) ≡ true
mFi-max′ f v zer _ l = ⊥-elim (true≢false (trans (sym l) (NZ⇒¬⪯0 f (nz v))))
  where
    nz : ∀ {f} → FiView f → NZ f
    nz (fiψ d) = tt
    nz fiI     = tt
mFi-max′ f v (a ▹ q ▹ p) o l = mFi-max′ f v (a ▹ q) (proj₁ (OT-+⁻ o)) (sk v l)
  where
    sk : ∀ {f} → FiView f → le f (a ▹ q ▹ p) ≡ true → le f (a ▹ q) ≡ true
    sk (fiψ d) = sing-le-▹ (psi IR d) a q p
    sk fiI     = sing-le-▹ I a q p
mFi-max′ f v (zer ▹ phi b c) o l with OT-φ⁻ o | caseEq (lt b c) | Car⪯φ (fi⇒car v) b c l
... | ob , oc , _ , _ | inj₁ e | inj₁ fb = subst (λ w → le f w ≡ true) (sym (if-true {b = lt b c} {x = mFi c} {y = mFi b} e))
                                             (mFi-max′ f v c oc (leˡ f c (lt≡ (⪯≺-trans {f} {b} {c} (le! fb) (lt! e)))))
... | ob , oc , _ , _ | inj₁ e | inj₂ fc = subst (λ w → le f w ≡ true) (sym (if-true {b = lt b c} {x = mFi c} {y = mFi b} e)) (mFi-max′ f v c oc fc)
... | ob , oc , _ , _ | inj₂ e | inj₁ fb = subst (λ w → le f w ≡ true) (sym (if-false {b = lt b c} {x = mFi c} {y = mFi b} e)) (mFi-max′ f v b ob fb)
... | ob , oc , _ , _ | inj₂ e | inj₂ fc = subst (λ w → le f w ≡ true) (sym (if-false {b = lt b c} {x = mFi c} {y = mFi b} e))
                                             (mFi-max′ f v b ob (le≡ (⪯-trans {f} {c} {b} (le! fc) (¬≺⇒⪰ b c e))))
mFi-max′ f v (zer ▹ psi (ΩR b) c) o l =
  mFi-max′ f v b (OT-ψΩ-lev b c o) (Fi⪯ v (lt-trans f ⟨ psi (ΩR b) c ⟩ ⟨ Om b ⟩ (Fi-strict v ⟨ psi (ΩR b) c ⟩ (ne v) l) (lt≡ (ψ≺κ o))))
  where
    ne : ∀ {f} → FiView f → f ≡ ⟨ psi (ΩR b) c ⟩ → ⊥
    ne (fiψ d) ()
    ne fiI     ()
    Fi⪯ : ∀ {f} → FiView f → lt f ⟨ Om b ⟩ ≡ true → le f b ≡ true
    Fi⪯ (fiψ d) h = unf (psi IR d) (Om b) h
    Fi⪯ fiI     h = le≡ (¬≺⇒⪰ b ⟨ I ⟩ (not-true (unf I (Om b) h)))
mFi-max′ f v (zer ▹ psi IR c) _ l = l
mFi-max′ f v (zer ▹ Om b) o l = mFi-max′ f v b (proj₁ (OT-Ω⁻ o)) (Fi⪯ v (Fi-strict v ⟨ Om b ⟩ (ne v) l))
  where
    ne : ∀ {f} → FiView f → f ≡ ⟨ Om b ⟩ → ⊥
    ne (fiψ d) ()
    ne fiI     ()
    Fi⪯ : ∀ {f} → FiView f → lt f ⟨ Om b ⟩ ≡ true → le f b ≡ true
    Fi⪯ (fiψ d) h = unf (psi IR d) (Om b) h
    Fi⪯ fiI     h = le≡ (¬≺⇒⪰ b ⟨ I ⟩ (not-true (unf I (Om b) h)))
mFi-max′ f v (zer ▹ I) _ l = l

-- x^{−Fi} 单调
mFi-mono : ∀ b x → OT b → OT x → le b x ≡ true → le (mFi b) (mFi x) ≡ true
mFi-mono b x ob ox l with mFi-view b
... | inj₂ e = subst (λ v → le v (mFi x) ≡ true) (sym e) (0⪯′ (mFi x))
... | inj₁ f = mFi-max′ (mFi b) f x ox (le≡ (⪯-trans {mFi b} {b} {x} (le! (mFi⪯′ b ob)) (le! l)))

pFi-0′ : ∀ x → OT x → lt x ⟨ psi IR zer ⟩ ≡ true → pFi x ≡ ⟨ psi IR zer ⟩
pFi-0′ zer _ _ = refl
pFi-0′ (a ▹ q ▹ p) o h = pFi-0′ (a ▹ q) (proj₁ (OT-+⁻ o)) (prefix-lt a q p (psi IR zer) h)
pFi-0′ (zer ▹ phi b c) o h with caseEq (lt b c)
... | inj₁ e = trans (if-true {b = lt b c} {x = pFi c} {y = pFi b} e) (pFi-0′ c (proj₁ (proj₂ (OT-φ⁻ o))) (proj₂ (φ≺Car (carψ zer) b c h)))
... | inj₂ e = trans (if-false {b = lt b c} {x = pFi c} {y = pFi b} e) (pFi-0′ b (proj₁ (OT-φ⁻ o)) (proj₁ (φ≺Car (carψ zer) b c h)))
pFi-0′ (zer ▹ psi (ΩR b) c) o h =
  pFi-0′ b (OT-ψΩ-lev b c o) (trans (lt-lin′ b ⟨ psi IR zer ⟩) (unf (Om b) (psi IR zer) (unf (psi (ΩR b) c) (psi IR zer) h)))
pFi-0′ (zer ▹ psi IR c) o h = ⊥-elim (true≢false (trans (sym (trans (sym (sameRule IR c zer)) h)) (lt-zero c)))
pFi-0′ (zer ▹ Om b) o h = pFi-0′ b (proj₁ (OT-Ω⁻ o)) (trans (lt-lin′ b ⟨ psi IR zer ⟩) (unf (Om b) (psi IR zer) h))
pFi-0′ (zer ▹ I) o h = ⊥-elim (true≢false (trans (sym h) (lt-unfold≠ I (psi IR zer) refl)))

pFi-0 : ∀ {x} → OT x → x ≺ ⟨ psi IR zer ⟩ → pFi x ≡ ⟨ psi IR zer ⟩
pFi-0 {x} o (lt! h) = pFi-0′ x o h

-- Remark 2.14 (g)
FF : Tm → Set
FF x = ∃ λ b → OT ⟨ psi IR b ⟩ × mFi x ≡ ⟨ psi IR b ⟩ × pFi x ≡ ⟨ psi IR (b + one) ⟩ × lt x ⟨ psi IR (b + one) ⟩ ≡ true

ψ0 : Tm
ψ0 = ⟨ psi IR zer ⟩

-- 各情形的辅助（不用 with 抽象大项）
FF-sum : ∀ a q p → FF (a ▹ q) → FF (a ▹ q ▹ p)
FF-sum a q p (b , ob , me , pe , l) = b , ob , me , pe , ≺-sing-▹ (a ▹ q) p (psi IR (b + one)) tt l

FF-φ : ∀ b c → (le ψ0 b ≡ true) ⊎ (le ψ0 c ≡ true) → lt b ⟨ I ⟩ ≡ true × lt c ⟨ I ⟩ ≡ true
     → (le ψ0 b ≡ true → lt b ⟨ I ⟩ ≡ true → FF b) → (le ψ0 c ≡ true → lt c ⟨ I ⟩ ≡ true → FF c) → FF ⟨ phi b c ⟩
FF-φ b c sp (bI , cI) ihb ihc with caseEq (lt b c)
... | inj₁ e = finC (ihc (ψc sp) cI)
  where
    ψc : (le ψ0 b ≡ true) ⊎ (le ψ0 c ≡ true) → le ψ0 c ≡ true
    ψc (inj₁ ψb)  = leˡ ψ0 c (lt≡ (⪯≺-trans {ψ0} {b} {c} (le! ψb) (lt! e)))
    ψc (inj₂ ψc′) = ψc′
    finC : FF c → FF ⟨ phi b c ⟩
    finC (b₀ , ob₀ , me , pe , c≺) = b₀ , ob₀ , trans (if-true {b = lt b c} {x = mFi c} {y = mFi b} e) me
                                   , trans (if-true {b = lt b c} {x = pFi c} {y = pFi b} e) pe
                                   , trans (φG-lt b c (psi IR (b₀ + one)) refl)
                                           (∧ⁱ (lt b ⟨ psi IR (b₀ + one) ⟩) (lt c ⟨ psi IR (b₀ + one) ⟩) (lt-trans b c ⟨ psi IR (b₀ + one) ⟩ e c≺) c≺)
... | inj₂ e = finB (ihb (ψb sp) bI)
  where
    ψb : (le ψ0 b ≡ true) ⊎ (le ψ0 c ≡ true) → le ψ0 b ≡ true
    ψb (inj₁ ψb′) = ψb′
    ψb (inj₂ ψc)  = le≡ (⪯-trans {ψ0} {c} {b} (le! ψc) (¬≺⇒⪰ b c e))
    finB : FF b → FF ⟨ phi b c ⟩
    finB (b₀ , ob₀ , me , pe , b≺) = b₀ , ob₀ , trans (if-false {b = lt b c} {x = mFi c} {y = mFi b} e) me
                                   , trans (if-false {b = lt b c} {x = pFi c} {y = pFi b} e) pe
                                   , trans (φG-lt b c (psi IR (b₀ + one)) refl)
                                           (∧ⁱ (lt b ⟨ psi IR (b₀ + one) ⟩) (lt c ⟨ psi IR (b₀ + one) ⟩) b≺
                                               (lt≡ (⪯≺-trans {c} {b} {⟨ psi IR (b₀ + one) ⟩} (¬≺⇒⪰ b c e) (lt! b≺))))

FF-ψΩ : ∀ b c → FF b → FF ⟨ psi (ΩR b) c ⟩
FF-ψΩ b c (b₀ , ob₀ , me , pe , b≺) = b₀ , ob₀ , me , pe
    , unf⁻ (psi (ΩR b) c) (psi IR (b₀ + one)) refl
           (unf⁻ (Om b) (psi IR (b₀ + one)) refl (not-≡false (not-true (trans (sym (lt-lin′ b ⟨ psi IR (b₀ + one) ⟩)) b≺))))

FF-Ω : ∀ b → FF b → FF ⟨ Om b ⟩
FF-Ω b (b₀ , ob₀ , me , pe , b≺) = b₀ , ob₀ , me , pe
    , unf⁻ (Om b) (psi IR (b₀ + one)) refl (not-≡false (not-true (trans (sym (lt-lin′ b ⟨ psi IR (b₀ + one) ⟩)) b≺)))

-- ψ_I 0 ⪯ ψ_{Ω′_b} c ⟹ ψ_I 0 ⪯ b；ψ_{Ω′_b} c ≺ I ⟹ b ≺ I
ψ0⪯ψΩ : ∀ b c → le ψ0 ⟨ psi (ΩR b) c ⟩ ≡ true → le ψ0 b ≡ true
ψ0⪯ψΩ b c l with ∨-true (unf (psi IR zer) (psi (ΩR b) c) (Fi-strict (fiψ zer) ⟨ psi (ΩR b) c ⟩ (λ ()) l))
... | inj₁ g = unf (psi IR zer) (Om b) g
... | inj₂ z = ⊥-elim (true≢false (sym z))

ψΩ≺I : ∀ b c → lt ⟨ psi (ΩR b) c ⟩ ⟨ I ⟩ ≡ true → lt b ⟨ I ⟩ ≡ true
ψΩ≺I b c h with ∨-true (unf (psi (ΩR b) c) I h)
... | inj₁ g = unf (Om b) I g
... | inj₂ z = ⊥-elim (true≢false (sym z))

Fi-form′ : ∀ x → OT x → le ψ0 x ≡ true → lt x ⟨ I ⟩ ≡ true → FF x
Fi-form′ zer _ l _ = ⊥-elim (true≢false (trans (sym l) (NZ⇒¬⪯0 ψ0 tt)))
Fi-form′ (a ▹ q ▹ p) o l h = FF-sum a q p (Fi-form′ (a ▹ q) (proj₁ (OT-+⁻ o)) (sing-le-▹ (psi IR zer) a q p l) (prefix-lt a q p I h))
Fi-form′ (zer ▹ phi b c) o l h =
  FF-φ b c (Car⪯φ (carψ zer) b c l) (φ≺Car carI b c h) (Fi-form′ b (proj₁ (OT-φ⁻ o))) (Fi-form′ c (proj₁ (proj₂ (OT-φ⁻ o))))
Fi-form′ (zer ▹ psi (ΩR b) c) o l h = FF-ψΩ b c (Fi-form′ b (OT-ψΩ-lev b c o) (ψ0⪯ψΩ b c l) (ψΩ≺I b c h))
Fi-form′ (zer ▹ psi IR c) o l h = c , o , refl , refl , trans (sameRule IR c (c + one)) (x≺x+1 c)
Fi-form′ (zer ▹ Om b) o l h =
  FF-Ω b (Fi-form′ b (proj₁ (OT-Ω⁻ o)) (unf (psi IR zer) (Om b) (Fi-strict (fiψ zer) ⟨ Om b ⟩ (λ ()) l)) (unf (Om b) I h))
Fi-form′ (zer ▹ I) o l h = ⊥-elim (true≢false (trans (sym h) (lt-irrefl ⟨ I ⟩)))

Fi-form : ∀ {x} → OT x → ⟨ psi IR zer ⟩ ⪯ x → x ≺ I′
        → ∃ λ b → OT ⟨ psi IR b ⟩ × mFi x ≡ ⟨ psi IR b ⟩ × pFi x ≡ ⟨ psi IR (b + one) ⟩ × x ≺ ⟨ psi IR (b + one) ⟩
Fi-form {x} o (le! l) (lt! h) with Fi-form′ x o l h
... | b , ob , me , pe , l′ = b , ob , me , pe , lt! l′
```

## 6. Remark 2.14 (i)：x ≺ Ωⁿ_{x^{−Fi}+1}

```agda
NF : Tm → Set
NF y = NZ y × isFiT y ≡ false

Ω-NF : ∀ y → NF y → Ω y ≡ ⟨ Om y ⟩ × NF ⟨ Om y ⟩
Ω-NF y (nz , nf) with ωView y
... | Ω0        = ⊥-elim nz
... | ΩFi f _   = ⊥-elim (true≢false (trans (sym (fiT f)) nf))
... | ΩΩ _ _ e  = e , (tt , refl)

Ωⁿ-NF : ∀ y n → NF y → NF (Ωⁿ y n)
Ωⁿ-NF y zero    nf = nf
Ωⁿ-NF y (suc n) nf = subst NF (sym (proj₁ (Ω-NF (Ωⁿ y n) (Ωⁿ-NF y n nf)))) (proj₂ (Ω-NF (Ωⁿ y n) (Ωⁿ-NF y n nf)))

Ωⁿ-suc : ∀ y n → NF y → Ωⁿ y (suc n) ≡ ⟨ Om (Ωⁿ y n) ⟩
Ωⁿ-suc y n nf = proj₁ (Ω-NF (Ωⁿ y n) (Ωⁿ-NF y n nf))

Ωⁿ-step : ∀ y n → NF y → lt (Ωⁿ y n) (Ωⁿ y (suc n)) ≡ true
Ωⁿ-step y n nf = subst (λ v → lt (Ωⁿ y n) v ≡ true) (sym (Ωⁿ-suc y n nf)) (≺-Ωa (Ωⁿ y n))

Ωⁿ-mono-n : ∀ y → NF y → ∀ n k → le (Ωⁿ y n) (Ωⁿ y (k +ℕ n)) ≡ true
Ωⁿ-mono-n y nf n zero    = leʳ (Ωⁿ y n) (Ωⁿ y n) (eqT-refl (Ωⁿ y n))
Ωⁿ-mono-n y nf n (suc k) = le≡ (⪯-trans {Ωⁿ y n} {Ωⁿ y (k +ℕ n)} {Ωⁿ y (suc (k +ℕ n))}
                                 (le! (Ωⁿ-mono-n y nf n k)) (le! (leˡ (Ωⁿ y (k +ℕ n)) (Ωⁿ y (suc (k +ℕ n))) (Ωⁿ-step y (k +ℕ n) nf))))

-- 一般形式：x ≺ I，NF y，x^{−Fi} ⪯ y ⟹ ∃ n. x ≺ Ωⁿ_y
BB : Tm → Tm → Set
BB y x = ∃ λ n → lt x (Ωⁿ y n) ≡ true

BB-sum : ∀ y → NF y → ∀ a q p → BB y (a ▹ q) → BB y (a ▹ q ▹ p)
BB-sum y nf a q p (n , g) = suc n , subst (λ v → lt (a ▹ q ▹ p) v ≡ true) (sym (Ωⁿ-suc y n nf))
  (≺-sing-▹ (a ▹ q) p (Om (Ωⁿ y n)) tt (subst (λ v → lt (a ▹ q) v ≡ true) (Ωⁿ-suc y n nf) (lt-trans (a ▹ q) (Ωⁿ y n) (Ωⁿ y (suc n)) g (Ωⁿ-step y n nf))))

BB-φ : ∀ y → NF y → ∀ b c → BB y b → BB y c → BB y ⟨ phi b c ⟩
BB-φ y nf b c (n₁ , g₁) (n₂ , g₂) = suc M ,
  subst (λ v → lt ⟨ phi b c ⟩ v ≡ true) (sym (Ωⁿ-suc y M nf))
        (trans (φG-lt b c (Om (Ωⁿ y M)) refl) (∧ⁱ (lt b ⟨ Om (Ωⁿ y M) ⟩) (lt c ⟨ Om (Ωⁿ y M) ⟩) bM cM))
  where
    M = n₂ +ℕ n₁
    bM : lt b ⟨ Om (Ωⁿ y M) ⟩ ≡ true
    bM = lt-trans b (Ωⁿ y M) ⟨ Om (Ωⁿ y M) ⟩ (lt≡ (≺⪯-trans {b} {Ωⁿ y n₁} {Ωⁿ y M} (lt! g₁) (le! (Ωⁿ-mono-n y nf n₁ n₂)))) (≺-Ωa (Ωⁿ y M))
    cM : lt c ⟨ Om (Ωⁿ y M) ⟩ ≡ true
    cM = lt-trans c (Ωⁿ y M) ⟨ Om (Ωⁿ y M) ⟩
           (lt≡ (≺⪯-trans {c} {Ωⁿ y n₂} {Ωⁿ y M} (lt! g₂) (le! (subst (λ m → le (Ωⁿ y n₂) (Ωⁿ y m) ≡ true) (+-comm n₁ n₂) (Ωⁿ-mono-n y nf n₂ n₁)))))
           (≺-Ωa (Ωⁿ y M))

BB-ψΩ : ∀ y → NF y → ∀ b c → OT ⟨ psi (ΩR b) c ⟩ → BB y b → BB y ⟨ psi (ΩR b) c ⟩
BB-ψΩ y nf b c o (n , g) = suc n , subst (λ v → lt ⟨ psi (ΩR b) c ⟩ v ≡ true) (sym (Ωⁿ-suc y n nf))
  (lt-trans ⟨ psi (ΩR b) c ⟩ ⟨ Om b ⟩ ⟨ Om (Ωⁿ y n) ⟩ (lt≡ (ψ≺κ o))
            (unf⁻ (Om b) (Om (Ωⁿ y n)) (≺⇒eqT-false b (Ωⁿ y n) (AT-all b (Ωⁿ y n)) g) g))

BB-Ω : ∀ y → NF y → ∀ b → BB y b → BB y ⟨ Om b ⟩
BB-Ω y nf b (n , g) = suc n , subst (λ v → lt ⟨ Om b ⟩ v ≡ true) (sym (Ωⁿ-suc y n nf))
  (unf⁻ (Om b) (Om (Ωⁿ y n)) (≺⇒eqT-false b (Ωⁿ y n) (AT-all b (Ωⁿ y n)) g) g)

bound′ : ∀ x → OT x → lt x ⟨ I ⟩ ≡ true → ∀ y → NF y → le (mFi x) y ≡ true → BB y x
bound′ zer _ _ y (nz , _) _ = zero , nzlt y nz
  where
    nzlt : ∀ y → NZ y → lt zer y ≡ true
    nzlt (a ▹ p) _ = lt-zer a p
bound′ (a ▹ q ▹ p) o h y nf l = BB-sum y nf a q p (bound′ (a ▹ q) (proj₁ (OT-+⁻ o)) (prefix-lt a q p I h) y nf l)
bound′ (zer ▹ phi b c) o h y nf l =
  BB-φ y nf b c
    (bound′ b ob (proj₁ bcI) y nf (le≡ (⪯-trans {mFi b} {mFi ⟨ phi b c ⟩} {y} (le! (mFi-mono b ⟨ phi b c ⟩ ob o (leˡ b ⟨ phi b c ⟩ (≺-φˡ b c)))) (le! l))))
    (bound′ c oc (proj₂ bcI) y nf (le≡ (⪯-trans {mFi c} {mFi ⟨ phi b c ⟩} {y} (le! (mFi-mono c ⟨ phi b c ⟩ oc o (leˡ c ⟨ phi b c ⟩ (≺-φʳ b c)))) (le! l))))
  where
    ob = proj₁ (OT-φ⁻ o)
    oc = proj₁ (proj₂ (OT-φ⁻ o))
    bcI = φ≺Car carI b c h
bound′ (zer ▹ psi (ΩR b) c) o h y nf l = BB-ψΩ y nf b c o (bound′ b (OT-ψΩ-lev b c o) (ψΩ≺I b c h) y nf l)
bound′ (zer ▹ psi IR c) o h y nf l = 1 , lt≡ (⪯≺-trans {⟨ psi IR c ⟩} {y} {Ωⁿ y 1} (le! l) (lt! (Ωⁿ-step y 0 nf)))
bound′ (zer ▹ Om b) o h y nf l = BB-Ω y nf b (bound′ b (proj₁ (OT-Ω⁻ o)) (unf (Om b) I h) y nf l)
bound′ (zer ▹ I) o h y nf l = ⊥-elim (true≢false (trans (sym h) (lt-irrefl ⟨ I ⟩)))

Ωⁿ-bound : ∀ {x} → OT x → x ≺ I′ → ∃ λ n → x ≺ Ωⁿ (mFi x + one) n
Ωⁿ-bound {x} o (lt! h) with bound′ x o h (mFi x + one) nfm (leˡ (mFi x) (mFi x + one) (x≺x+1 (mFi x)))
  where
    nfm : NF (mFi x + one)
    nfm = subst NF (sym (+one (mFi x))) (tt , ▹1-notFi (mFi x))
... | n , g = n , lt! g
```
