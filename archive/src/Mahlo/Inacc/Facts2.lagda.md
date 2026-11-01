# OTFacts（二）：OT 的封闭性与 ã、a⁺

Remark 2.12 (a)（`+`、`φ` 保持 OT），Def 2.13／Remark 2.14 关于 `tilde`（ã）与 `plus`（a⁺）的字段。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Facts2 where

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

## 1. 工具

```agda
▹1-notFi : ∀ y → isFiT (y ▹ phi zer zer) ≡ false
▹1-notFi zer     = refl
▹1-notFi (a ▹ p) = refl

OT-▹1 : ∀ b → OT b → OT (b ▹ phi zer zer)
OT-▹1 zer     _ = ot! refl
OT-▹1 (a ▹ p) o = OT-▹⁺ tt o (ot! refl) (one⪯P′ p)

-- 单主元项 ⪯ 和 ⟹ ⪯ 去掉末分量的前缀
sing-le-▹ : ∀ k a q p → le ⟨ k ⟩ (a ▹ q ▹ p) ≡ true → le ⟨ k ⟩ (a ▹ q) ≡ true
sing-le-▹ k a q p l with ∨-true l
... | inj₁ g = sing-≺-▹ k (a ▹ q) p tt g
... | inj₂ e with eqT-sound ⟨ k ⟩ (a ▹ q ▹ p) e
...   | ()

-- 前缀 ≺ ⟨ k ⟩
prefix-lt : ∀ a q p k → lt (a ▹ q ▹ p) ⟨ k ⟩ ≡ true → lt (a ▹ q) ⟨ k ⟩ ≡ true
prefix-lt a q p k h = lt-trans (a ▹ q) (a ▹ q ▹ p) ⟨ k ⟩ (≺-▹ (a ▹ q) p) h

-- Ω′ 的单调
Ωle : ∀ w a → le w a ≡ true → le ⟨ Om w ⟩ ⟨ Om a ⟩ ≡ true
Ωle w a l with ∨-true l
... | inj₂ e with eqT-sound w a e
...   | refl = leʳ ⟨ Om w ⟩ ⟨ Om w ⟩ (eqT-refl ⟨ Om w ⟩)
Ωle w a l | inj₁ g = leˡ ⟨ Om w ⟩ ⟨ Om a ⟩ (unf⁻ (Om w) (Om a) (≺⇒eqT-false w a (AT-all w a) g) g)

-- if 的读出
if-lt : ∀ {A : Set} b c (x y : A) → (lt b c ≡ true → (if lt b c then x else y) ≡ x) × (lt b c ≡ false → (if lt b c then x else y) ≡ y)
if-lt b c x y = (λ e → if-true {b = lt b c} {x = x} {y = y} e) , (λ e → if-false {b = lt b c} {x = x} {y = y} e)

-- 首分量在 OT
OT-hd : ∀ t → NZ t → OT t → OT ⟨ hd t ⟩
OT-hd (zer ▹ p)   _ o = o
OT-hd (a ▹ q ▹ p) _ o = OT-hd (a ▹ q) tt (proj₁ (OT-+⁻ o))
```

## 2. Remark 2.12 (a)：`+`、`φ` 保持 OT

```agda
OT-pred : ∀ t → OT t → OT (pred t)
OT-pred zer         o = o
OT-pred (zer ▹ p)   _ = OT-0
OT-pred (a ▹ q ▹ p) o = proj₁ (OT-+⁻ o)

dropLt-OT : ∀ x q → OT x → OT (dropLt x q)
dropLt-OT zer     q o = o
dropLt-OT (a ▹ p) q o with caseEq (lt ⟨ p ⟩ ⟨ q ⟩)
... | inj₁ e = subst OT (sym (if-true {b = lt ⟨ p ⟩ ⟨ q ⟩} {x = dropLt a q} {y = a ▹ p} e)) (dropLt-OT a q (OT-pred (a ▹ p) o))
... | inj₂ e = subst OT (sym (if-false {b = lt ⟨ p ⟩ ⟨ q ⟩} {x = dropLt a q} {y = a ▹ p} e)) o

-- 剩下的末分量 ⪰ q
dropLt-last : ∀ x q → NZ (dropLt x q) → le ⟨ q ⟩ ⟨ lastP (dropLt x q) ⟩ ≡ true
dropLt-last zer     q ()
dropLt-last (a ▹ p) q nz with caseEq (lt ⟨ p ⟩ ⟨ q ⟩)
... | inj₁ e = subst (λ v → NZ v → le ⟨ q ⟩ ⟨ lastP v ⟩ ≡ true) (sym (if-true {b = lt ⟨ p ⟩ ⟨ q ⟩} {x = dropLt a q} {y = a ▹ p} e)) (dropLt-last a q) nz
... | inj₂ e = subst (λ v → le ⟨ q ⟩ ⟨ lastP v ⟩ ≡ true) (sym (if-false {b = lt ⟨ p ⟩ ⟨ q ⟩} {x = dropLt a q} {y = a ▹ p} e)) (le≡ (¬≺⇒⪰ ⟨ p ⟩ ⟨ q ⟩ e))

app-OT : ∀ x y → OT x → OT y → NZ y → (NZ x → le ⟨ hd y ⟩ ⟨ lastP x ⟩ ≡ true) → OT (app x y)
app-OT zer     (zer ▹ q) ox oy _ _ = oy
app-OT (a ▹ p) (zer ▹ q) ox oy _ h = OT-▹⁺ tt ox oy (h tt)
app-OT x (y ▹ q′ ▹ q) ox oy _ h =
  OT-+⁺ (app-OT x (y ▹ q′) ox (proj₁ (OT-+⁻ oy)) tt h) (proj₁ (proj₂ (OT-+⁻ oy))) (proj₂ (proj₂ (OT-+⁻ oy)))

+-OT : ∀ {x y} → OT x → OT y → OT (x + y)
+-OT {x} {y = zer}   ox oy = ox
+-OT {x} {y = y ▹ q} ox oy = app-OT (dropLt x (hd (y ▹ q))) (y ▹ q) (dropLt-OT x (hd (y ▹ q)) ox) oy tt (dropLt-last x (hd (y ▹ q)))

φ-OT : ∀ {x y} → OT x → OT y → OT (φ x y)
φ-OT {x} {y} ox oy with caseEq (inCr x y)
... | inj₁ e = subst OT (sym (if-true {b = inCr x y} {x = y} {y = if isZero y ∧ isGT x then x else ⟨ phi x y ⟩} e)) oy
... | inj₂ e with caseEq (isZero y ∧ isGT x)
...   | inj₁ f = subst OT (sym (trans (if-false {b = inCr x y} {x = y} e) (if-true {b = isZero y ∧ isGT x} {x = x} {y = ⟨ phi x y ⟩} f))) ox
...   | inj₂ f = subst OT (sym (trans (if-false {b = inCr x y} {x = y} e) (if-false {b = isZero y ∧ isGT x} {x = x} {y = ⟨ phi x y ⟩} f))) (OT-φ⁺ ox oy e f)
```

## 3. ã（Def 2.13）

```agda
tilde-fix : ∀ {x} → CarView x → tilde x ≡ x
tilde-fix (carΩ a) = refl
tilde-fix (carψ d) = refl
tilde-fix carI     = refl

fi⇒car : ∀ {x} → FiView x → CarView x
fi⇒car (fiψ d) = carψ d
fi⇒car fiI     = carI

car⇒isCar : ∀ {x} → CarView x → isCarT x ≡ true
car⇒isCar (carΩ a) = refl
car⇒isCar (carψ d) = refl
car⇒isCar carI     = refl

-- κ⁻ 的形状
Ω-view′ : ∀ y → CarView (Ω y) ⊎ Ω y ≡ zer
Ω-view′ y with ωView y
... | Ω0        = inj₂ refl
... | ΩFi f e   = inj₁ (subst CarView (sym e) (fi⇒car f))
... | ΩΩ _ _ e  = inj₁ (subst CarView (sym e) (carΩ y))

κ⁻-view : ∀ b → CarView (κ⁻ (ΩR b)) ⊎ κ⁻ (ΩR b) ≡ zer
κ⁻-view b = Ω-view′ (pred b)

tilde-view : ∀ x → CarView (tilde x) ⊎ tilde x ≡ zer
tilde-view zer                    = inj₂ refl
tilde-view (a ▹ q ▹ p)            = tilde-view (a ▹ q)
tilde-view (zer ▹ phi b c) with caseEq (lt b c)
... | inj₁ e = subst (λ v → CarView v ⊎ v ≡ zer) (sym (if-true {b = lt b c} {x = tilde c} {y = tilde b} e)) (tilde-view c)
... | inj₂ e = subst (λ v → CarView v ⊎ v ≡ zer) (sym (if-false {b = lt b c} {x = tilde c} {y = tilde b} e)) (tilde-view b)
tilde-view (zer ▹ psi (ΩR b) c)   = κ⁻-view b
tilde-view (zer ▹ psi IR c)       = inj₁ (carψ c)
tilde-view (zer ▹ Om b)           = inj₁ (carΩ b)
tilde-view (zer ▹ I)              = inj₁ carI

tilde-Car : ∀ {x} → OT x → isCarT (tilde x) ≡ true ⊎ tilde x ≡ zer
tilde-Car {x} _ with tilde-view x
... | inj₁ v = inj₁ (car⇒isCar v)
... | inj₂ e = inj₂ e

tilde-idem : ∀ {x} → OT x → tilde (tilde x) ≡ tilde x
tilde-idem {x} _ with tilde-view x
... | inj₁ v = tilde-fix v
... | inj₂ e = trans (cong tilde e) (sym e)

tilde-OT : ∀ {x} → OT x → OT (tilde x)
tilde-OT {x = zer} o = o
tilde-OT {x = a ▹ q ▹ p} o = tilde-OT (proj₁ (OT-+⁻ o))
tilde-OT {x = zer ▹ phi b c} o with OT-φ⁻ o | caseEq (lt b c)
... | ob , oc , _ , _ | inj₁ e = subst OT (sym (if-true {b = lt b c} {x = tilde c} {y = tilde b} e)) (tilde-OT oc)
... | ob , oc , _ , _ | inj₂ e = subst OT (sym (if-false {b = lt b c} {x = tilde c} {y = tilde b} e)) (tilde-OT ob)
tilde-OT {x = zer ▹ psi (ΩR b) c} o with OT-ψ⁻ o
... | _ , oΩ , r , _ with sucView b r
...   | suc! zer      = OT-0
...   | suc! (a ▹ p)  = Ω-OT (a ▹ p) (proj₁ (OT-▹⁻ tt (proj₁ (OT-Ω⁻ oΩ))))
tilde-OT {x = zer ▹ psi IR c} o = o
tilde-OT {x = zer ▹ Om b}     o = o
tilde-OT {x = zer ▹ I}        o = o

tilde⪯ : ∀ {x} → OT x → tilde x ⪯ x
tilde⪯ {x} o = le! (go x o)
  where
    go : ∀ x → OT x → le (tilde x) x ≡ true
    go zer         _ = refl
    go (a ▹ q ▹ p) o = leˡ (tilde (a ▹ q)) (a ▹ q ▹ p) (lt≡ (⪯≺-trans {tilde (a ▹ q)} {a ▹ q} {a ▹ q ▹ p} (le! (go (a ▹ q) (proj₁ (OT-+⁻ o)))) (lt! (≺-▹ (a ▹ q) p))))
    go (zer ▹ phi b c) o with OT-φ⁻ o | caseEq (lt b c)
    ... | ob , oc , _ , _ | inj₁ e = subst (λ v → le v ⟨ phi b c ⟩ ≡ true) (sym (if-true {b = lt b c} {x = tilde c} {y = tilde b} e))
                                        (leˡ (tilde c) ⟨ phi b c ⟩ (lt≡ (⪯≺-trans {tilde c} {c} {⟨ phi b c ⟩} (le! (go c oc)) (lt! (≺-φʳ b c)))))
    ... | ob , oc , _ , _ | inj₂ e = subst (λ v → le v ⟨ phi b c ⟩ ≡ true) (sym (if-false {b = lt b c} {x = tilde c} {y = tilde b} e))
                                        (leˡ (tilde b) ⟨ phi b c ⟩ (lt≡ (⪯≺-trans {tilde b} {b} {⟨ phi b c ⟩} (le! (go b ob)) (lt! (≺-φˡ b c)))))
    go (zer ▹ psi (ΩR b) c) o = leˡ (κ⁻ (ΩR b)) ⟨ psi (ΩR b) c ⟩ (lt≡ (κ⁻≺ψ o))
    go (zer ▹ psi IR c) _ = leʳ ⟨ psi IR c ⟩ ⟨ psi IR c ⟩ (eqT-refl ⟨ psi IR c ⟩)
    go (zer ▹ Om b)     _ = leʳ ⟨ Om b ⟩ ⟨ Om b ⟩ (eqT-refl ⟨ Om b ⟩)
    go (zer ▹ I)        _ = leʳ ⟨ I ⟩ ⟨ I ⟩ (eqT-refl ⟨ I ⟩)

-- Car′ 元素 κ ⪯ φ′_b c ⟹ κ ⪯ b 或 κ ⪯ c
Car⪯φ : ∀ {κ} → CarView κ → ∀ b c → le κ ⟨ phi b c ⟩ ≡ true → (le κ b ≡ true) ⊎ (le κ c ≡ true)
Car⪯φ {κ} v b c l = body (strict l)
  where
    strict : le κ ⟨ phi b c ⟩ ≡ true → lt κ ⟨ phi b c ⟩ ≡ true
    strict l′ with ∨-true l′
    ... | inj₁ g = g
    ... | inj₂ e = ⊥-elim (bad v (eqT-sound κ ⟨ phi b c ⟩ e))
      where
        bad : ∀ {κ} → CarView κ → κ ≡ ⟨ phi b c ⟩ → ⊥
        bad (carΩ a) ()
        bad (carψ d) ()
        bad carI     ()
    -- κ = ⟨ k ⟩，k ∈ G′：lt ⟨ k ⟩ ⟨ φ b c ⟩ = not (lt b κ ∧ lt c κ)
    body : lt κ ⟨ phi b c ⟩ ≡ true → (le κ b ≡ true) ⊎ (le κ c ≡ true)
    body g = split (not-true (trans (sym (Gφ-lt′ v)) g))
      where
        Gφ-lt′ : ∀ {κ} → CarView κ → lt κ ⟨ phi b c ⟩ ≡ not (lt b κ ∧ lt c κ)
        Gφ-lt′ (carΩ a) = Gφ-lt (Om a) b c refl
        Gφ-lt′ (carψ d) = Gφ-lt (psi IR d) b c refl
        Gφ-lt′ carI     = Gφ-lt I b c refl
        split : lt b κ ∧ lt c κ ≡ false → (le κ b ≡ true) ⊎ (le κ c ≡ true)
        split f with caseEq (lt b κ)
        ... | inj₂ z = inj₁ (le≡ (¬≺⇒⪰ b κ z))
        ... | inj₁ o = inj₂ (le≡ (¬≺⇒⪰ c κ (trans (sym (cong (_∧ lt c κ) o)) f)))

tilde-max : ∀ {x κ} → OT x → OT κ → isCarT κ ≡ true → κ ⪯ x → κ ⪯ tilde x
tilde-max {x} {κ} ox oκ ck (le! l) = le! (go x ox l)
  where
    v : CarView κ
    v = carView κ ck
    go : ∀ x → OT x → le κ x ≡ true → le κ (tilde x) ≡ true
    go zer _ l = ⊥-elim (true≢false (trans (sym l) (NZ⇒¬⪯0 κ (nzC v))))
      where
        nzC : ∀ {κ} → CarView κ → NZ κ
        nzC (carΩ a) = tt
        nzC (carψ d) = tt
        nzC carI     = tt
    go (a ▹ q ▹ p) o l = go (a ▹ q) (proj₁ (OT-+⁻ o)) (sing-le-▹′ l)
      where
        sing-le-▹′ : le κ (a ▹ q ▹ p) ≡ true → le κ (a ▹ q) ≡ true
        sing-le-▹′ l′ = sk v l′
          where
            sk : ∀ {κ} → CarView κ → le κ (a ▹ q ▹ p) ≡ true → le κ (a ▹ q) ≡ true
            sk (carΩ a′) = sing-le-▹ (Om a′) a q p
            sk (carψ d)  = sing-le-▹ (psi IR d) a q p
            sk carI      = sing-le-▹ I a q p
    go (zer ▹ phi b c) o l with OT-φ⁻ o | caseEq (lt b c) | Car⪯φ v b c l
    ... | ob , oc , _ , _ | inj₁ e | inj₁ κb = subst (λ w → le κ w ≡ true) (sym (if-true {b = lt b c} {x = tilde c} {y = tilde b} e)) (go c oc (le≡ (⪯≺-trans′ κb e)))
      where
        ⪯≺-trans′ : le κ b ≡ true → lt b c ≡ true → κ ⪯ c
        ⪯≺-trans′ kb bc = ≺⇒⪯ (⪯≺-trans {κ} {b} {c} (le! kb) (lt! bc))
    ... | ob , oc , _ , _ | inj₁ e | inj₂ κc = subst (λ w → le κ w ≡ true) (sym (if-true {b = lt b c} {x = tilde c} {y = tilde b} e)) (go c oc κc)
    ... | ob , oc , _ , _ | inj₂ e | inj₁ κb = subst (λ w → le κ w ≡ true) (sym (if-false {b = lt b c} {x = tilde c} {y = tilde b} e)) (go b ob κb)
    ... | ob , oc , _ , _ | inj₂ e | inj₂ κc = subst (λ w → le κ w ≡ true) (sym (if-false {b = lt b c} {x = tilde c} {y = tilde b} e))
                                               (go b ob (le≡ (⪯-trans {κ} {c} {b} (le! κc) (¬≺⇒⪰ b c e))))
    go (zer ▹ psi (ΩR b) c) o l with OT-ψ⁻ o
    ... | _ , oΩ , r , _ = le≡ (Car≺κ⇒⪯κ⁻ oκ ck r oΩ (≺-trans {κ} {⟨ psi (ΩR b) c ⟩} {⟨ Om b ⟩} (lt! (strict l)) (ψ≺κ o)))
      where
        strict : le κ ⟨ psi (ΩR b) c ⟩ ≡ true → lt κ ⟨ psi (ΩR b) c ⟩ ≡ true
        strict l′ with ∨-true l′
        ... | inj₁ g = g
        ... | inj₂ e = ⊥-elim (bad v (eqT-sound κ ⟨ psi (ΩR b) c ⟩ e))
          where
            bad : ∀ {κ} → CarView κ → κ ≡ ⟨ psi (ΩR b) c ⟩ → ⊥
            bad (carΩ a) ()
            bad (carψ d) ()
            bad carI     ()
    go (zer ▹ psi IR c) _ l = l
    go (zer ▹ Om b)     _ l = l
    go (zer ▹ I)        _ l = l
```

## 4. a⁺（Def 2.13 / Remark 2.14）

```agda
plus-form⁺ : ∀ x → OT x → ∃ λ y → OT y × plus x ≡ ⟨ Om (y ▹ phi zer zer) ⟩ × Ω y ≡ tilde x
plus-form⁺ zer         _ = zer , OT-0 , refl , refl
plus-form⁺ (a ▹ q ▹ p) o = plus-form⁺ (a ▹ q) (proj₁ (OT-+⁻ o))
plus-form⁺ (zer ▹ phi b c) o with OT-φ⁻ o | caseEq (lt b c)
... | ob , oc , _ , _ | inj₁ e with plus-form⁺ c oc
...   | y , oy , pe , te = y , oy , trans (if-true {b = lt b c} {x = plus c} {y = plus b} e) pe
                                   , trans te (sym (if-true {b = lt b c} {x = tilde c} {y = tilde b} e))
plus-form⁺ (zer ▹ phi b c) o | ob , oc , _ , _ | inj₂ e with plus-form⁺ b ob
...   | y , oy , pe , te = y , oy , trans (if-false {b = lt b c} {x = plus c} {y = plus b} e) pe
                                   , trans te (sym (if-false {b = lt b c} {x = tilde c} {y = tilde b} e))
plus-form⁺ (zer ▹ psi (ΩR b) c) o with OT-ψ⁻ o
... | _ , oΩ , r , _ with sucView b r
...   | suc! b′ = b′ , OT-pred (b′ ▹ phi zer zer) (proj₁ (OT-Ω⁻ oΩ)) , refl , refl
plus-form⁺ (zer ▹ psi IR c) o = ⟨ psi IR c ⟩ , o , trans (cong Ω (+one ⟨ psi IR c ⟩)) (Ω-suc ⟨ psi IR c ⟩) , refl
plus-form⁺ (zer ▹ Om b)     o = b , proj₁ (OT-Ω⁻ o) , trans (cong Ω (+one b)) (Ω-suc b) , Ω-of-OT b o
plus-form⁺ (zer ▹ I)        o = ⟨ I ⟩ , OT-I , trans (cong Ω (+one ⟨ I ⟩)) (Ω-suc ⟨ I ⟩) , refl

plus-form : ∀ {x} → OT x → ∃ λ y → plus x ≡ ⟨ Om (y ▹ phi zer zer) ⟩ × Ω y ≡ tilde x
plus-form {x} o with plus-form⁺ x o
... | y , _ , pe , te = y , pe , te

plus-OT : ∀ {x} → OT x → OT (plus x)
plus-OT {x} o with plus-form⁺ x o
... | y , oy , pe , _ = subst OT (sym pe) (OT-Ω⁺ (OT-▹1 y oy) (▹1-notFi y) refl)

plus-Car : ∀ {x} → OT x → isCarT (plus x) ≡ true
plus-Car {x} o with plus-form⁺ x o
... | y , _ , pe , _ = subst (λ v → isCarT v ≡ true) (sym pe) refl

plus-Ω : ∀ y → plus (Ω y) ≡ ⟨ Om (y ▹ phi zer zer) ⟩
plus-Ω y with ωView y
... | Ω0              = refl
... | ΩFi (fiψ d) e   = trans (cong plus e) (trans (cong Ω (+one ⟨ psi IR d ⟩)) (Ω-suc ⟨ psi IR d ⟩))
... | ΩFi fiI e       = trans (cong plus e) (trans (cong Ω (+one ⟨ I ⟩)) (Ω-suc ⟨ I ⟩))
... | ΩΩ _ _ e        = trans (cong plus e) (trans (cong Ω (+one y)) (Ω-suc y))

tilde-plus : ∀ {x} → OT x → plus (tilde x) ≡ plus x
tilde-plus {x} o with plus-form⁺ x o
... | y , _ , pe , te = trans (cong plus (sym te)) (trans (plus-Ω y) (sym pe))

≺plus′ : ∀ x → OT x → lt x (plus x) ≡ true
≺plus′ zer _ = lt-zer zer (Om one)
≺plus′ (a ▹ q ▹ p) o = sumCase a q p (plus-form⁺ (a ▹ q) (proj₁ (OT-+⁻ o))) (≺plus′ (a ▹ q) (proj₁ (OT-+⁻ o)))
  where
    sumCase : ∀ a q p → (∃ λ y → OT y × plus (a ▹ q) ≡ ⟨ Om (y ▹ phi zer zer) ⟩ × Ω y ≡ tilde (a ▹ q))
            → lt (a ▹ q) (plus (a ▹ q)) ≡ true → lt (a ▹ q ▹ p) (plus (a ▹ q)) ≡ true
    sumCase a q p (y , _ , pe , _) ih =
      subst (λ v → lt (a ▹ q ▹ p) v ≡ true) (sym pe)
            (≺-sing-▹ (a ▹ q) p (Om (y ▹ phi zer zer)) tt (subst (λ v → lt (a ▹ q) v ≡ true) pe ih))
≺plus′ (zer ▹ phi b c) o with OT-φ⁻ o | caseEq (lt b c)
... | ob , oc , _ , _ | inj₁ e with plus-form⁺ c oc
...   | y , _ , pe , _ = subst (λ v → lt ⟨ phi b c ⟩ v ≡ true) (sym (trans (if-true {b = lt b c} {x = plus c} {y = plus b} e) pe))
      (trans (φG-lt b c (Om (y ▹ phi zer zer)) refl)
             (∧ⁱ (lt b ⟨ Om (y ▹ phi zer zer) ⟩) (lt c ⟨ Om (y ▹ phi zer zer) ⟩) (lt-trans b c ⟨ Om (y ▹ phi zer zer) ⟩ e cw) cw))
  where
    cw : lt c ⟨ Om (y ▹ phi zer zer) ⟩ ≡ true
    cw = subst (λ v → lt c v ≡ true) pe (≺plus′ c oc)
≺plus′ (zer ▹ phi b c) o | ob , oc , _ , _ | inj₂ e with plus-form⁺ b ob
...   | y , _ , pe , _ = subst (λ v → lt ⟨ phi b c ⟩ v ≡ true) (sym (trans (if-false {b = lt b c} {x = plus c} {y = plus b} e) pe))
      (trans (φG-lt b c (Om (y ▹ phi zer zer)) refl)
             (∧ⁱ (lt b ⟨ Om (y ▹ phi zer zer) ⟩) (lt c ⟨ Om (y ▹ phi zer zer) ⟩) bw
                 (lt≡ (⪯≺-trans {c} {b} {⟨ Om (y ▹ phi zer zer) ⟩} (¬≺⇒⪰ b c e) (lt! bw)))))
  where
    bw : lt b ⟨ Om (y ▹ phi zer zer) ⟩ ≡ true
    bw = subst (λ v → lt b v ≡ true) pe (≺plus′ b ob)
≺plus′ (zer ▹ psi (ΩR b) c) o = lt≡ (ψ≺κ o)
≺plus′ (zer ▹ psi IR c) o =
  subst (λ v → lt ⟨ psi IR c ⟩ v ≡ true) (sym (trans (cong Ω (+one ⟨ psi IR c ⟩)) (Ω-suc ⟨ psi IR c ⟩)))
        (unf⁻ (psi IR c) (Om (⟨ psi IR c ⟩ ▹ phi zer zer)) refl
              (leˡ ⟨ psi IR c ⟩ (⟨ psi IR c ⟩ ▹ phi zer zer) (≺-▹ ⟨ psi IR c ⟩ (phi zer zer))))
≺plus′ (zer ▹ Om b) o =
  subst (λ v → lt ⟨ Om b ⟩ v ≡ true) (sym (trans (cong Ω (+one b)) (Ω-suc b)))
        (unf⁻ (Om b) (Om (b ▹ phi zer zer)) (≺⇒eqT-false b (b ▹ phi zer zer) (AT-all b (b ▹ phi zer zer)) (≺-▹ b (phi zer zer))) (≺-▹ b (phi zer zer)))
≺plus′ (zer ▹ I) o =
  subst (λ v → lt ⟨ I ⟩ v ≡ true) (sym (trans (cong Ω (+one ⟨ I ⟩)) (Ω-suc ⟨ I ⟩)))
        (unf⁻ I (Om (⟨ I ⟩ ▹ phi zer zer)) refl (not-≡false (lt-asym ⟨ I ⟩ (⟨ I ⟩ ▹ phi zer zer) (≺-▹ ⟨ I ⟩ (phi zer zer)))))

≺plus : ∀ {x} → OT x → x ≺ plus x
≺plus {x} o = lt! (≺plus′ x o)

-- φ′_b c ≺ κ（κ ∈ Car′）⟹ b ≺ κ 且 c ≺ κ
φ≺Car : ∀ {κ} → CarView κ → ∀ b c → lt ⟨ phi b c ⟩ κ ≡ true → lt b κ ≡ true × lt c κ ≡ true
φ≺Car (carΩ a) b c h = ∧₁ _ _ (trans (sym (φG-lt b c (Om a) refl)) h) , ∧₂ (lt b ⟨ Om a ⟩) _ (trans (sym (φG-lt b c (Om a) refl)) h)
φ≺Car (carψ d) b c h = ∧₁ _ _ (trans (sym (φG-lt b c (psi IR d) refl)) h) , ∧₂ (lt b ⟨ psi IR d ⟩) _ (trans (sym (φG-lt b c (psi IR d) refl)) h)
φ≺Car carI     b c h = ∧₁ _ _ (trans (sym (φG-lt b c I refl)) h) , ∧₂ (lt b ⟨ I ⟩) _ (trans (sym (φG-lt b c I refl)) h)

-- 单主元项 X 与 Ω′_a：X ≺ Ω′_a，a ∉ Fi′ ⟹ X ≺ a（X ∈ Fi′）
Fi≺Ωarg : ∀ {X} → FiView X → ∀ a → OT ⟨ Om a ⟩ → lt X ⟨ Om a ⟩ ≡ true → lt X a ≡ true
Fi≺Ωarg {X} f a oa h with ∨-true (Fi⪯ f)
  where
    Fi⪯ : FiView X → le X a ≡ true
    Fi⪯ (fiψ d) = unf (psi IR d) (Om a) h
    Fi⪯ fiI     = le≡ (¬≺⇒⪰ a ⟨ I ⟩ (not-true (unf I (Om a) h)))
... | inj₁ g = g
... | inj₂ e = ⊥-elim (true≢false (trans (sym (subst (λ v → isFiT v ≡ true) (eqT-sound X a e) (fiT f))) (proj₂ (Ω-arg a oa))))
  where
    fiT : ∀ {X} → FiView X → isFiT X ≡ true
    fiT (fiψ d) = refl
    fiT fiI     = refl

pl : ∀ x → OT x → ∀ κ → OT κ → CarView κ → lt x κ ≡ true → le (plus x) κ ≡ true
pl zer _ κ oκ (carΩ a) _ = Ωle one a (one⪯NZ a (proj₁ (Ω-arg a oκ)))
pl zer _ κ oκ (carψ d) _ = leˡ Ω₁ ⟨ psi IR d ⟩ (unf⁻ (Om one) (psi IR d) refl (not-≡false (cong₂ _∨_ (lt-P-one (psi IR d)) refl)))
pl zer _ κ oκ carI     _ = leˡ Ω₁ ⟨ I ⟩ (unf⁻ (Om one) I refl (one≺P I refl))
pl (a ▹ q ▹ p) o κ oκ v h = pl (a ▹ q) (proj₁ (OT-+⁻ o)) κ oκ v (lt-trans (a ▹ q) (a ▹ q ▹ p) κ (≺-▹ (a ▹ q) p) h)
pl (zer ▹ phi b c) o κ oκ v h with OT-φ⁻ o | caseEq (lt b c) | φ≺Car v b c h
... | ob , oc , _ , _ | inj₁ e | bκ , cκ = subst (λ w → le w κ ≡ true) (sym (if-true {b = lt b c} {x = plus c} {y = plus b} e)) (pl c oc κ oκ v cκ)
... | ob , oc , _ , _ | inj₂ e | bκ , cκ = subst (λ w → le w κ ≡ true) (sym (if-false {b = lt b c} {x = plus c} {y = plus b} e)) (pl b ob κ oκ v bκ)
pl (zer ▹ psi (ΩR b) c) o κ oκ (carΩ a) h = unf (psi (ΩR b) c) (Om a) h
pl (zer ▹ psi (ΩR b) c) o κ oκ (carψ d) h = leˡ ⟨ Om b ⟩ ⟨ psi IR d ⟩ (unf (psi (ΩR b) c) (psi IR d) h)
pl (zer ▹ psi (ΩR b) c) o κ oκ carI     h = unf (psi (ΩR b) c) I h
pl (zer ▹ psi IR c) o κ oκ v h =
  subst (λ w → le w κ ≡ true) (sym (trans (cong Ω (+one ⟨ psi IR c ⟩)) (Ω-suc ⟨ psi IR c ⟩))) (body v h)
  where
    X = ⟨ psi IR c ⟩
    W = X ▹ phi zer zer
    body : CarView κ → lt X κ ≡ true → le ⟨ Om W ⟩ κ ≡ true
    body (carΩ a) h′ = Ωle W a (subst (λ v → le v a ≡ true) (+one X) (+1-least′ X a (Fi≺Ωarg (fiψ c) a oκ h′)))
    body (carψ d) h′ = leˡ ⟨ Om W ⟩ ⟨ psi IR d ⟩
      (unf⁻ (Om W) (psi IR d) refl (not-≡false (not-true (trans (sym (lt-lin′ W ⟨ psi IR d ⟩)) (≺-sing-▹ X (phi zer zer) (psi IR d) tt h′)))))
    body carI     h′ = leˡ ⟨ Om W ⟩ ⟨ I ⟩ (unf⁻ (Om W) I refl (≺-sing-▹ X (phi zer zer) I tt h′))
pl (zer ▹ Om b) o κ oκ v h =
  subst (λ w → le w κ ≡ true) (sym (trans (cong Ω (+one b)) (Ω-suc b))) (body v h)
  where
    W = b ▹ phi zer zer
    -- b ≺ ⟨ k ⟩ ⟹ W ≺ ⟨ k ⟩（k ∈ Fi′：W ≠ ⟨ k ⟩）
    W≺ : ∀ k → (W ≡ ⟨ k ⟩ → ⊥) → lt b ⟨ k ⟩ ≡ true → lt W ⟨ k ⟩ ≡ true
    W≺ k ne bk with ∨-true (subst (λ v → le v ⟨ k ⟩ ≡ true) (+one b) (+1-least′ b ⟨ k ⟩ bk))
    ... | inj₁ g = g
    ... | inj₂ e = ⊥-elim (ne (eqT-sound W ⟨ k ⟩ e))
    body : CarView κ → lt ⟨ Om b ⟩ κ ≡ true → le ⟨ Om W ⟩ κ ≡ true
    body (carΩ a) h′ = Ωle W a (subst (λ v → le v a ≡ true) (+one b) (+1-least′ b a (unf (Om b) (Om a) h′)))
    body (carψ d) h′ = leˡ ⟨ Om W ⟩ ⟨ psi IR d ⟩
      (unf⁻ (Om W) (psi IR d) refl (not-≡false (not-true (trans (sym (lt-lin′ W ⟨ psi IR d ⟩))
        (W≺ (psi IR d) (λ ()) (trans (lt-lin′ b ⟨ psi IR d ⟩) (unf (Om b) (psi IR d) h′)))))))
    body carI     h′ = leˡ ⟨ Om W ⟩ ⟨ I ⟩ (unf⁻ (Om W) I refl (W≺ I (λ ()) (unf (Om b) I h′)))
pl (zer ▹ I) o κ oκ v h =
  subst (λ w → le w κ ≡ true) (sym (trans (cong Ω (+one ⟨ I ⟩)) (Ω-suc ⟨ I ⟩))) (body v h)
  where
    W = ⟨ I ⟩ ▹ phi zer zer
    body : CarView κ → lt ⟨ I ⟩ κ ≡ true → le ⟨ Om W ⟩ κ ≡ true
    body (carΩ a) h′ = Ωle W a (subst (λ v → le v a ≡ true) (+one ⟨ I ⟩) (+1-least′ ⟨ I ⟩ a (Fi≺Ωarg fiI a oκ h′)))
    body (carψ d) h′ = ⊥-elim (true≢false (trans (sym h′) (lt-unfold≠ I (psi IR d) refl)))
    body carI     h′ = ⊥-elim (true≢false (trans (sym h′) (lt-irrefl ⟨ I ⟩)))

plus-least : ∀ {x κ} → OT x → OT κ → isCarT κ ≡ true → x ≺ κ → plus x ⪯ κ
plus-least {x} {κ} ox oκ ck (lt! h) = le! (pl x ox κ oκ (carView κ ck) h)
```

