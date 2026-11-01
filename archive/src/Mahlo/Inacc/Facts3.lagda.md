# OTFacts（三）：Remark 2.15

`C̃_κ(a)` 的成员条件是 `allLt (G κ u) a`（Def 2.7）。本文件证 Remark 2.15 (c)(d)(e)：
(c) `u ≺ κ` 时 `u ∈ C̃_κ(a) ⟺ u ≺ ψ_κ a`（对 `u` 的结构归纳，κ 的两种形状分开）；
(d)(e) `ψ_π d ∈ C̃_κ(a)` 的分解。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Facts3 where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith
open import Mahlo.Inacc.BoolLemmas
open import Mahlo.Inacc.OTLemmas
open import Mahlo.Inacc.Unfold
open import Mahlo.Inacc.Linear
open import Mahlo.Inacc.Trans hiding (G)
open import Mahlo.Inacc.Lex
open import Mahlo.Inacc.Subterm
open import Mahlo.Inacc.Facts1
open import Mahlo.Inacc.Facts2
open import Mahlo.Inacc.Facts2b

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
```

## 1. allLt 的工具

```agda
allLt-++⁻ : ∀ xs ys b → allLt (xs ++ ys) b ≡ true → allLt xs b ≡ true × allLt ys b ≡ true
allLt-++⁻ []       ys b h = refl , h
allLt-++⁻ (x ∷ xs) ys b h with allLt-++⁻ xs ys b (∧₂ (lt x b) _ h)
... | p , q = ∧ⁱ (lt x b) (allLt xs b) (∧₁ (lt x b) _ h) p , q

allLt-++⁺ : ∀ xs ys b → allLt xs b ≡ true → allLt ys b ≡ true → allLt (xs ++ ys) b ≡ true
allLt-++⁺ []       ys b _ q = q
allLt-++⁺ (x ∷ xs) ys b p q = ∧ⁱ (lt x b) (allLt (xs ++ ys) b) (∧₁ (lt x b) _ p) (allLt-++⁺ xs ys b (∧₂ (lt x b) _ p) q)

allLt-mono : ∀ xs b b′ → allLt xs b ≡ true → lt b b′ ≡ true → allLt xs b′ ≡ true
allLt-mono []       b b′ _ _ = refl
allLt-mono (x ∷ xs) b b′ h l = ∧ⁱ (lt x b′) (allLt xs b′) (lt-trans x b b′ (∧₁ (lt x b) _ h) l) (allLt-mono xs b b′ (∧₂ (lt x b) _ h) l)

-- regTm κ 的形状
regView : ∀ κ → CarView (regTm κ)
regView (ΩR z) = carΩ z
regView IR     = carI

-- 末分量 ⪯ 整个和
last-le : ∀ b r → OT (b ▹ r) → le ⟨ r ⟩ (b ▹ r) ≡ true
last-le zer     r _ = leʳ ⟨ r ⟩ ⟨ r ⟩ (eqT-refl ⟨ r ⟩)
last-le (a ▹ q) r o = le≡ (⪯-app {a ▹ q} {⟨ r ⟩} tt tt o)

-- z ∈ Suc′ 时 z ≺ ψ_{Ω′_z} a（z ⪯ κ⁻ ≺ ψ，或 z = 1）
Suc≺ψ : ∀ z a → OT ⟨ psi (ΩR z) a ⟩ → lt z ⟨ psi (ΩR z) a ⟩ ≡ true
Suc≺ψ z a o with sucView z (proj₁ (proj₂ (proj₂ (OT-ψ⁻ o))))
... | suc! zer     = one≺P (psi (ΩR one) a) refl
... | suc! (b ▹ p) = ≺-sing-▹ (b ▹ p) (phi zer zer) (psi (ΩR (b ▹ p ▹ phi zer zer)) a) tt
                       (lt≡ (⪯≺-trans {b ▹ p} {Ω (b ▹ p)} {⟨ psi (ΩR (b ▹ p ▹ phi zer zer)) a ⟩} (le! (⪯Ω (b ▹ p))) (κ⁻≺ψ o)))

-- ⪯ 的反对称（Ω′ 情形）
Ω-antisym : ∀ z c → le ⟨ Om z ⟩ ⟨ Om c ⟩ ≡ true → le ⟨ Om c ⟩ ⟨ Om z ⟩ ≡ true → c ≡ z
Ω-antisym z c p q with ∨-true p | ∨-true q
... | inj₁ g | inj₁ h = ⊥-elim (true≢false (trans (sym h) (lt-asym ⟨ Om z ⟩ ⟨ Om c ⟩ g)))
... | inj₁ g | inj₂ e = Om-inj (eqT-sound ⟨ Om c ⟩ ⟨ Om z ⟩ e)
... | inj₂ e | _      = sym (Om-inj (eqT-sound ⟨ Om z ⟩ ⟨ Om c ⟩ e))
```

## 2. Remark 2.15 (c)

```agda
-- 语句
Cc : Reg → Tm → Tm → Set
Cc κ a u = (inC̃ κ a u ≡ true → lt u ⟨ psi κ a ⟩ ≡ true) × (lt u ⟨ psi κ a ⟩ ≡ true → inC̃ κ a u ≡ true)

CcP : Reg → Tm → PTm → Set
CcP κ a p = (allLt (GP κ p) a ≡ true → lt ⟨ p ⟩ ⟨ psi κ a ⟩ ≡ true) × (lt ⟨ p ⟩ ⟨ psi κ a ⟩ ≡ true → allLt (GP κ p) a ≡ true)

both : ∀ {A B : Set} → A → B → (A → B) × (B → A)
both a b = (λ _ → b) , (λ _ → a)

-- 析取消去（把大项作参数传入，不用 with 抽象）
∨-left : ∀ x y → x ∨ y ≡ true → (y ≡ true → ⊥) → x ≡ true
∨-left x y h ne with ∨-true {x} {y} h
... | inj₁ p = p
... | inj₂ q = ⊥-elim (ne q)

-- c ≡ z 的情形（把等式作参数传入）
ψΩ-same : ∀ c z d a → OT ⟨ psi (ΩR c) d ⟩ → OT ⟨ psi (ΩR z) a ⟩ → c ≡ z
        → (lt c ⟨ Om z ⟩ ≡ true → Cc (ΩR z) a c)
        → (allLt (d ∷ (G (ΩR z) c ++ G (ΩR z) d)) a ≡ true → lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true)
        × (lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true → allLt (d ∷ (G (ΩR z) c ++ G (ΩR z) d)) a ≡ true)
ψΩ-same c .c d a o oψ refl ih = fwd , bwd
  where
    fwd : allLt (d ∷ (G (ΩR c) c ++ G (ΩR c) d)) a ≡ true → lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR c) a ⟩ ≡ true
    fwd cc = trans (sameRule (ΩR c) d a) (∧₁ (lt d a) _ cc)
    bwd : lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR c) a ⟩ ≡ true → allLt (d ∷ (G (ΩR c) c ++ G (ΩR c) d)) a ≡ true
    bwd l = ∧ⁱ (lt d a) (allLt (G (ΩR c) c ++ G (ΩR c) d) a) da
               (allLt-++⁺ (G (ΩR c) c) (G (ΩR c) d) a cz (allLt-mono (G (ΩR c) d) d a (proj₂ (proj₂ (proj₂ (OT-ψ⁻ o)))) da))
      where
        da : lt d a ≡ true
        da = trans (sym (sameRule (ΩR c) d a)) l
        cz : allLt (G (ΩR c) c) a ≡ true
        cz = proj₂ (ih (≺-Ωa c)) (Suc≺ψ c a oψ)

-- 和的情形：两个归纳假设作参数传入（保持结构递减）
sumC : ∀ b p → OT (b ▹ p) → ∀ κ a → OT ⟨ psi κ a ⟩ → lt (b ▹ p) (regTm κ) ≡ true
     → (lt b (regTm κ) ≡ true → Cc κ a b) → (lt ⟨ p ⟩ (regTm κ) ≡ true → CcP κ a p) → Cc κ a (b ▹ p)
sumC (a′ ▹ q) p o κ a oψ h ihT ihP = fwd , bwd
  where
    pre : lt (a′ ▹ q) (regTm κ) ≡ true
    pre = prefix-lt′ (regView κ) h
      where
        prefix-lt′ : ∀ {κ} → CarView κ → lt (a′ ▹ q ▹ p) κ ≡ true → lt (a′ ▹ q) κ ≡ true
        prefix-lt′ (carΩ z) = prefix-lt a′ q p (Om z)
        prefix-lt′ (carψ d) = prefix-lt a′ q p (psi IR d)
        prefix-lt′ carI     = prefix-lt a′ q p I
    pκ : lt ⟨ p ⟩ (regTm κ) ≡ true
    pκ = lt≡ (⪯≺-trans {⟨ p ⟩} {a′ ▹ q ▹ p} {regTm κ} (le! (last-le (a′ ▹ q) p o)) (lt! h))
    ih₁ = ihT pre
    ih₂ = ihP pκ
    fwd : inC̃ κ a (a′ ▹ q ▹ p) ≡ true → lt (a′ ▹ q ▹ p) ⟨ psi κ a ⟩ ≡ true
    fwd c = ≺-sing-▹ (a′ ▹ q) p (psi κ a) tt (proj₁ ih₁ (proj₁ (allLt-++⁻ (G κ (a′ ▹ q)) (GP κ p) a c)))
    bwd : lt (a′ ▹ q ▹ p) ⟨ psi κ a ⟩ ≡ true → inC̃ κ a (a′ ▹ q ▹ p) ≡ true
    bwd l = allLt-++⁺ (G κ (a′ ▹ q)) (GP κ p) a (proj₂ ih₁ (prefix-lt a′ q p (psi κ a) l))
              (proj₂ ih₂ (lt≡ (⪯≺-trans {⟨ p ⟩} {a′ ▹ q ▹ p} {⟨ psi κ a ⟩} (le! (last-le (a′ ▹ q) p o)) (lt! l))))
sumC zer p o κ a oψ h ihT ihP = ihP h

mutual
  C̃-T : ∀ u → OT u → ∀ κ a → OT ⟨ psi κ a ⟩ → lt u (regTm κ) ≡ true → Cc κ a u
  C̃-T zer _ κ a _ _ = (λ _ → lt-zer zer (psi κ a)) , (λ _ → refl)
  C̃-T (zer ▹ p) o κ a oψ h = C̃-P p o κ a oψ h
  C̃-T (a′ ▹ q ▹ p) o κ a oψ h =
    sumC (a′ ▹ q) p o κ a oψ h (C̃-T (a′ ▹ q) (proj₁ (OT-+⁻ o)) κ a oψ) (C̃-P p (proj₁ (proj₂ (OT-+⁻ o))) κ a oψ)

  C̃-P : ∀ p → OT ⟨ p ⟩ → ∀ κ a → OT ⟨ psi κ a ⟩ → lt ⟨ p ⟩ (regTm κ) ≡ true → CcP κ a p
  -- φ
  C̃-P (phi b c) o κ a oψ h = fwd , bwd
    where
      bc = φ≺Car (regView κ) b c h
      ihb = C̃-T b (proj₁ (OT-φ⁻ o)) κ a oψ (proj₁ bc)
      ihc = C̃-T c (proj₁ (proj₂ (OT-φ⁻ o))) κ a oψ (proj₂ bc)
      fwd : allLt (G κ b ++ G κ c) a ≡ true → lt ⟨ phi b c ⟩ ⟨ psi κ a ⟩ ≡ true
      fwd cc with allLt-++⁻ (G κ b) (G κ c) a cc
      ... | cb , ccc = trans (φG-lt b c (psi κ a) refl) (∧ⁱ (lt b ⟨ psi κ a ⟩) (lt c ⟨ psi κ a ⟩) (proj₁ ihb cb) (proj₁ ihc ccc))
      bwd : lt ⟨ phi b c ⟩ ⟨ psi κ a ⟩ ≡ true → allLt (G κ b ++ G κ c) a ≡ true
      bwd l = allLt-++⁺ (G κ b) (G κ c) a (proj₂ ihb (∧₁ (lt b ⟨ psi κ a ⟩) (lt c ⟨ psi κ a ⟩) l′)) (proj₂ ihc (∧₂ (lt b ⟨ psi κ a ⟩) (lt c ⟨ psi κ a ⟩) l′))
        where
          l′ : lt b ⟨ psi κ a ⟩ ∧ lt c ⟨ psi κ a ⟩ ≡ true
          l′ = trans (sym (φG-lt b c (psi κ a) refl)) l
  -- Ω′_b，κ = Ω′_z：两边都真
  C̃-P (Om b) o (ΩR z) a oψ h = both cb bψ
    where
      bz : lt b z ≡ true
      bz = unf (Om b) (Om z) h
      -- Ω′_b ≺ ψ_{Ω′_z} a
      bψ : lt ⟨ Om b ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true
      bψ = unf⁻ (Om b) (psi (ΩR z) a) refl (not-≡false (cong₂ _∨_ (trans (lt-unfold≠ (Om z) (Om b) (eqT-false-sym b z ez)) (lt-asym b z bz)) (eqT-false-sym b z ez)))
        where
          ez : eqT b z ≡ false
          ez = ≺⇒eqT-false b z (AT-all b z) bz
      -- b ≺ ψ_{Ω′_z} a：b ≺ z = z′+1 ⟹ b ⪯ z′ ⪯ Ω z′ = κ⁻ ≺ ψ
      b≺ψ : lt b ⟨ psi (ΩR z) a ⟩ ≡ true
      b≺ψ with sucView z (proj₁ (proj₂ (proj₂ (OT-ψ⁻ oψ))))
      ... | suc! z′ = lt≡ (⪯≺-trans {b} {Ω z′} {⟨ psi (ΩR (z′ ▹ phi zer zer)) a ⟩}
                             (⪯-trans {b} {z′} {Ω z′} (le! (≺+1⇒⪯ b z′ (subst (λ v → lt b v ≡ true) (sym (+one z′)) bz))) (le! (⪯Ω z′)))
                             (κ⁻≺ψ oψ))
      cb : allLt (G (ΩR z) b) a ≡ true
      cb = proj₂ (C̃-T b (proj₁ (OT-Ω⁻ o)) (ΩR z) a oψ (lt-trans b ⟨ Om b ⟩ ⟨ Om z ⟩ (≺-Ωa b) h)) b≺ψ
  -- Ω′_b，κ = I
  C̃-P (Om b) o IR a oψ h = fwd , bwd
    where
      ih = C̃-T b (proj₁ (OT-Ω⁻ o)) IR a oψ (unf (Om b) I h)
      fwd : allLt (G IR b) a ≡ true → lt ⟨ Om b ⟩ ⟨ psi IR a ⟩ ≡ true
      fwd cb = unf⁻ (Om b) (psi IR a) refl (not-≡false (not-true (trans (sym (lt-lin′ b ⟨ psi IR a ⟩)) (proj₁ ih cb))))
      bwd : lt ⟨ Om b ⟩ ⟨ psi IR a ⟩ ≡ true → allLt (G IR b) a ≡ true
      bwd l = proj₂ ih (trans (lt-lin′ b ⟨ psi IR a ⟩) (unf (Om b) (psi IR a) l))
  -- I
  C̃-P I o (ΩR z) a oψ h = both refl (unf⁻ I (psi (ΩR z) a) refl (not-≡false (cong (_∨ false) (trans (lt-unfold≠ (Om z) I refl) (not-true (unf I (Om z) h))))))
  C̃-P I o IR a oψ h = ⊥-elim (true≢false (trans (sym h) (lt-irrefl ⟨ I ⟩)))
  -- ψ_I d
  C̃-P (psi IR d) o IR a oψ h = fwd , bwd
    where
      fwd : allLt (d ∷ G IR d) a ≡ true → lt ⟨ psi IR d ⟩ ⟨ psi IR a ⟩ ≡ true
      fwd c = trans (sameRule IR d a) (∧₁ (lt d a) _ c)
      bwd : lt ⟨ psi IR d ⟩ ⟨ psi IR a ⟩ ≡ true → allLt (d ∷ G IR d) a ≡ true
      bwd l = ∧ⁱ (lt d a) (allLt (G IR d) a) da (allLt-mono (G IR d) d a (proj₂ (proj₂ (proj₂ (OT-ψ⁻ o)))) da)
        where
          da : lt d a ≡ true
          da = trans (sym (sameRule IR d a)) l
  C̃-P (psi IR d) o (ΩR z) a oψ h = subst (λ gp → (allLt gp a ≡ true → lt ⟨ psi IR d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true) × (lt ⟨ psi IR d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true → allLt gp a ≡ true))
                                        (sym (if-false {b = le ⟨ Om z ⟩ ⟨ psi IR d ⟩} {x = d ∷ G (ΩR z) d} {y = []} nle))
                                        (both refl (unf⁻ (psi IR d) (psi (ΩR z) a) refl (∨ˡ (lt ⟨ psi IR d ⟩ ⟨ Om z ⟩) false h)))
    where
      nle : le ⟨ Om z ⟩ ⟨ psi IR d ⟩ ≡ false
      nle = not-true (trans (sym (lt-lin′ ⟨ psi IR d ⟩ ⟨ Om z ⟩)) h)
  -- ψ_{Ω′_c} d，κ = Ω′_z
  C̃-P (psi (ΩR c) d) o (ΩR z) a oψ h with caseEq (le ⟨ Om z ⟩ ⟨ Om c ⟩)
  ... | inj₁ e = subst (λ gp → (allLt gp a ≡ true → lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true) × (lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true → allLt gp a ≡ true))
                      (sym (if-true {b = le ⟨ Om z ⟩ ⟨ Om c ⟩} {x = d ∷ (G (ΩR z) c ++ G (ΩR z) d)} {y = []} e))
                      (ψΩ-same c z d a o oψ (Ω-antisym z c e (unf (psi (ΩR c) d) (Om z) h)) (C̃-T c (proj₁ (OT-Ω⁻ (proj₁ (proj₂ (OT-ψ⁻ o))))) (ΩR z) a oψ))
  C̃-P (psi (ΩR c) d) o (ΩR z) a oψ h | inj₂ e =
    subst (λ gp → (allLt gp a ≡ true → lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true) × (lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true → allLt gp a ≡ true))
          (sym (if-false {b = le ⟨ Om z ⟩ ⟨ Om c ⟩} {x = d ∷ (G (ΩR z) c ++ G (ΩR z) d)} {y = []} e))
          (both refl cψ)
    where
      -- Ω′_c ≺ Ω′_z
      cz : lt ⟨ Om c ⟩ ⟨ Om z ⟩ ≡ true
      cz = ∨-left (lt ⟨ Om c ⟩ ⟨ Om z ⟩) (eqT ⟨ Om c ⟩ ⟨ Om z ⟩) (unf (psi (ΩR c) d) (Om z) h)
                  (λ q → true≢false (trans (sym (leʳ ⟨ Om z ⟩ ⟨ Om c ⟩ (eqT-complete (sym (eqT-sound ⟨ Om c ⟩ ⟨ Om z ⟩ q))))) e))
      cψ : lt ⟨ psi (ΩR c) d ⟩ ⟨ psi (ΩR z) a ⟩ ≡ true
      cψ = unf⁻ (psi (ΩR c) d) (psi (ΩR z) a) (cong (_∧ eqT d a) ecz) (sh ecz cz)
        where
          ecz : eqT c z ≡ false
          ecz = ≺⇒eqT-false c z (AT-all c z) (unf (Om c) (Om z) cz)
          sh : ∀ {ea bd oo : Bool} → ea ≡ false → oo ≡ true → (ea ∧ bd) ∨ (oo ∨ (false ∨ false)) ≡ true
          sh refl refl = refl
  -- ψ_{Ω′_c} d，κ = I
  C̃-P (psi (ΩR c) d) o IR a oψ h =
    subst (λ gp → (allLt gp a ≡ true → lt ⟨ psi (ΩR c) d ⟩ ⟨ psi IR a ⟩ ≡ true) × (lt ⟨ psi (ΩR c) d ⟩ ⟨ psi IR a ⟩ ≡ true → allLt gp a ≡ true))
          (sym (if-false {b = le ⟨ I ⟩ ⟨ Om c ⟩} {x = d ∷ (G IR c ++ G IR d)} {y = G IR c} nle))
          (fwd , bwd)
    where
      cI : lt c ⟨ I ⟩ ≡ true
      cI = ψΩ≺I c d h
      nle : le ⟨ I ⟩ ⟨ Om c ⟩ ≡ false
      nle = not-true (trans (sym (lt-lin′ ⟨ Om c ⟩ ⟨ I ⟩)) (unf⁻ (Om c) I refl cI))
      ih = C̃-T c (proj₁ (OT-Ω⁻ (proj₁ (proj₂ (OT-ψ⁻ o))))) IR a oψ cI
      fwd : allLt (G IR c) a ≡ true → lt ⟨ psi (ΩR c) d ⟩ ⟨ psi IR a ⟩ ≡ true
      fwd cc = unf⁻ (psi (ΩR c) d) (psi IR a) refl (unf⁻ (Om c) (psi IR a) refl (not-≡false (not-true (trans (sym (lt-lin′ c ⟨ psi IR a ⟩)) (proj₁ ih cc)))))
      bwd : lt ⟨ psi (ΩR c) d ⟩ ⟨ psi IR a ⟩ ≡ true → allLt (G IR c) a ≡ true
      bwd l = proj₂ ih (trans (lt-lin′ c ⟨ psi IR a ⟩) (unf (Om c) (psi IR a) (unf (psi (ΩR c) d) (psi IR a) l)))
```

## 3. 字段

```agda
C̃⇒≺ψ : ∀ {κ a u} → OT ⟨ psi κ a ⟩ → OT u → u ≺ regTm κ → inC̃ κ a u ≡ true → u ≺ ⟨ psi κ a ⟩
C̃⇒≺ψ {κ} {a} {u} oψ ou (lt! h) c = lt! (proj₁ (C̃-T u ou κ a oψ h) c)

≺ψ⇒C̃ : ∀ {κ a u} → OT ⟨ psi κ a ⟩ → OT u → u ≺ ⟨ psi κ a ⟩ → inC̃ κ a u ≡ true
≺ψ⇒C̃ {κ} {a} {u} oψ ou (lt! h) = proj₂ (C̃-T u ou κ a oψ (lt-trans u ⟨ psi κ a ⟩ (regTm κ) h (lt≡ (ψ≺κ oψ)))) h

C̃-ψ-I : ∀ {π d a} → OT ⟨ psi π d ⟩ → OT ⟨ psi IR a ⟩ → inC̃ IR a ⟨ psi π d ⟩ ≡ true
       → ⟨ psi π d ⟩ ≺ ⟨ psi IR a ⟩ ⊎ (inC̃ IR a (regTm π) ≡ true × inC̃ IR a d ≡ true × d ≺ a)
C̃-ψ-I {π = IR} {d} {a} _ _ c = inj₂ (refl , ∧₂ (lt d a) _ c , lt! (∧₁ (lt d a) _ c))
C̃-ψ-I {π = ΩR c′} {d} {a} oψd oψa c with caseEq (le ⟨ I ⟩ ⟨ Om c′ ⟩)
... | inj₁ e = inj₂ (proj₁ (allLt-++⁻ (G IR c′) (G IR d) a rest) , proj₂ (allLt-++⁻ (G IR c′) (G IR d) a rest) , lt! (∧₁ (lt d a) _ c′′))
  where
    c′′ : allLt (d ∷ (G IR c′ ++ G IR d)) a ≡ true
    c′′ = trans (sym (cong (λ gp → allLt gp a) (if-true {b = le ⟨ I ⟩ ⟨ Om c′ ⟩} {x = d ∷ (G IR c′ ++ G IR d)} {y = G IR c′} e))) c
    rest : allLt (G IR c′ ++ G IR d) a ≡ true
    rest = ∧₂ (lt d a) _ c′′
... | inj₂ e = inj₁ (lt! (unf⁻ (psi (ΩR c′) d) (psi IR a) refl (unf⁻ (Om c′) (psi IR a) refl (not-≡false (not-true (trans (sym (lt-lin′ c′ ⟨ psi IR a ⟩)) c′ψ))))))
  where
    cc : allLt (G IR c′) a ≡ true
    cc = trans (sym (cong (λ gp → allLt gp a) (if-false {b = le ⟨ I ⟩ ⟨ Om c′ ⟩} {x = d ∷ (G IR c′ ++ G IR d)} {y = G IR c′} e))) c
    c′I : lt c′ ⟨ I ⟩ ≡ true
    c′I = unf (Om c′) I (trans (lt-lin′ ⟨ Om c′ ⟩ ⟨ I ⟩) (cong not e))
    c′ψ : lt c′ ⟨ psi IR a ⟩ ≡ true
    c′ψ = proj₁ (C̃-T c′ (proj₁ (OT-Ω⁻ (proj₁ (proj₂ (OT-ψ⁻ oψd))))) IR a oψa c′I) cc

C̃-ψ-Ω : ∀ {π d z a} → OT ⟨ psi π d ⟩ → OT ⟨ psi (ΩR z) a ⟩ → inC̃ (ΩR z) a ⟨ psi π d ⟩ ≡ true
       → ⟨ psi π d ⟩ ⪯ κ⁻ (ΩR z) ⊎ (inC̃ (ΩR z) a (regTm π) ≡ true × inC̃ (ΩR z) a d ≡ true × d ≺ a)
C̃-ψ-Ω {π = IR} {d} {z} {a} oψd oψa c with caseEq (le ⟨ Om z ⟩ ⟨ psi IR d ⟩)
... | inj₁ e = inj₂ (refl , ∧₂ (lt d a) _ c′′ , lt! (∧₁ (lt d a) _ c′′))
  where
    c′′ : allLt (d ∷ G (ΩR z) d) a ≡ true
    c′′ = trans (sym (cong (λ gp → allLt gp a) (if-true {b = le ⟨ Om z ⟩ ⟨ psi IR d ⟩} {x = d ∷ G (ΩR z) d} {y = []} e))) c
... | inj₂ e with sucView z (proj₁ (proj₂ (proj₂ (OT-ψ⁻ oψa))))
...   | suc! z′ = inj₁ (le! (Ω-mono′ ⟨ psi IR d ⟩ z′ (down (unf (psi IR d) (Om (z′ ▹ phi zer zer)) (trans (lt-lin′ ⟨ psi IR d ⟩ ⟨ Om (z′ ▹ phi zer zer) ⟩) (cong not e))))))
  where
    down : le ⟨ psi IR d ⟩ (z′ ▹ phi zer zer) ≡ true → le ⟨ psi IR d ⟩ z′ ≡ true
    down l with ∨-true l
    ... | inj₁ g = ≺+1⇒⪯ ⟨ psi IR d ⟩ z′ (subst (λ v → lt ⟨ psi IR d ⟩ v ≡ true) (sym (+one z′)) g)
    ... | inj₂ q with eqT-sound ⟨ psi IR d ⟩ (z′ ▹ phi zer zer) q
    ...   | ()
C̃-ψ-Ω {π = ΩR c} {d} {z} {a} oψd oψa cc with caseEq (le ⟨ Om z ⟩ ⟨ Om c ⟩)
... | inj₁ e = inj₂ (proj₁ (allLt-++⁻ (G (ΩR z) c) (G (ΩR z) d) a rest) , proj₂ (allLt-++⁻ (G (ΩR z) c) (G (ΩR z) d) a rest) , lt! (∧₁ (lt d a) _ c′′))
  where
    c′′ : allLt (d ∷ (G (ΩR z) c ++ G (ΩR z) d)) a ≡ true
    c′′ = trans (sym (cong (λ gp → allLt gp a) (if-true {b = le ⟨ Om z ⟩ ⟨ Om c ⟩} {x = d ∷ (G (ΩR z) c ++ G (ΩR z) d)} {y = []} e))) cc
    rest : allLt (G (ΩR z) c ++ G (ΩR z) d) a ≡ true
    rest = ∧₂ (lt d a) _ c′′
... | inj₂ e with sucView z (proj₁ (proj₂ (proj₂ (OT-ψ⁻ oψa))))
...   | suc! z′ = inj₁ (le! (le≡ (⪯-trans {⟨ psi (ΩR c) d ⟩} {⟨ Om c ⟩} {Ω z′} (≺⇒⪯ (ψ≺κ oψd))
                        (le! (subst (λ v → le v (Ω z′) ≡ true) (Ω-of-OT c oΩc) (Ω-mono′ c z′ (≺+1⇒⪯ c z′ (subst (λ v → lt c v ≡ true) (sym (+one z′)) cz))))))))
  where
    oΩc : OT ⟨ Om c ⟩
    oΩc = proj₁ (proj₂ (OT-ψ⁻ oψd))
    cz : lt c (z′ ▹ phi zer zer) ≡ true
    cz = unf (Om c) (Om (z′ ▹ phi zer zer)) (trans (lt-lin′ ⟨ Om c ⟩ ⟨ Om (z′ ▹ phi zer zer) ⟩) (cong not e))
```
