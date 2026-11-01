# OTFacts（一）：序的直接读出

`OTFacts` 里凡是「(≺′i) 的读出」「Ω 的单调性」「κ⁻」「+1」类的字段，本文件给出证明。名字与字段一致。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Facts1 where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith
open import Mahlo.Inacc.BoolLemmas
open import Mahlo.Inacc.OrderProps using (ltLx; lt-list)
open import Mahlo.Inacc.Unfold
open import Mahlo.Inacc.Linear
open import Mahlo.Inacc.Trans hiding (G)
open import Mahlo.Inacc.Lex
open import Mahlo.Inacc.Subterm

open import Data.Nat.Base using (ℕ; zero; suc)
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

## 1. 形状视图

```agda
data FiView : Tm → Set where
  fiψ : ∀ d → FiView ⟨ psi IR d ⟩
  fiI : FiView ⟨ I ⟩

fiView : ∀ y → isFiT y ≡ true → FiView y
fiView (zer ▹ psi IR d) _ = fiψ d
fiView (zer ▹ I)        _ = fiI

data CarView : Tm → Set where
  carΩ : ∀ a → CarView ⟨ Om a ⟩
  carψ : ∀ d → CarView ⟨ psi IR d ⟩
  carI : CarView ⟨ I ⟩

carView : ∀ d → isCarT d ≡ true → CarView d
carView (zer ▹ Om a)     _ = carΩ a
carView (zer ▹ psi IR d) _ = carψ d
carView (zer ▹ I)        _ = carI

data GView : Tm → Set where
  gψ : ∀ π b → GView ⟨ psi π b ⟩
  gΩ : ∀ a → GView ⟨ Om a ⟩
  gI : GView ⟨ I ⟩

gView : ∀ d → isGT d ≡ true → GView d
gView (zer ▹ psi π b) _ = gψ π b
gView (zer ▹ Om a)    _ = gΩ a
gView (zer ▹ I)       _ = gI

data SucView : Tm → Set where
  suc! : ∀ b′ → SucView (b′ ▹ phi zer zer)

sucView : ∀ b → isSuc b ≡ true → SucView b
sucView (b′ ▹ phi zer zer) _ = suc! b′

-- Ω 的三种情形
data ΩView : Tm → Set where
  Ω0  : ΩView zer
  ΩFi : ∀ {y} → FiView y → Ω y ≡ y → ΩView y
  ΩΩ  : ∀ {y} → NZ y → isFiT y ≡ false → Ω y ≡ ⟨ Om y ⟩ → ΩView y

ωView : ∀ y → ΩView y
ωView zer = Ω0
ωView (zer ▹ phi a b)      = ΩΩ tt refl refl
ωView (zer ▹ psi (ΩR a) b) = ΩΩ tt refl refl
ωView (zer ▹ psi IR b)     = ΩFi (fiψ b) refl
ωView (zer ▹ Om a)         = ΩΩ tt refl refl
ωView (zer ▹ I)            = ΩFi fiI refl
ωView (a ▹ q ▹ p)          = ΩΩ tt refl refl

-- 显式参数的合取消去（隐参从大合取推不出）
∧₁ : ∀ x y → x ∧ y ≡ true → x ≡ true
∧₁ x y h = proj₁ (∧-true {x} {y} h)
∧₂ : ∀ x y → x ∧ y ≡ true → y ≡ true
∧₂ x y h = proj₂ (∧-true {x} {y} h)

-- 非零项不 ⪯ 0
NZ⇒¬⪯0 : ∀ x → NZ x → le x zer ≡ false
NZ⇒¬⪯0 (a ▹ p) _ = cong₂ _∨_ (lt-zero (a ▹ p)) refl
```

## 2. Ω 的单调性

```agda
-- Fi′ 元素与 Ω′_y 的比较
Fi≺Ω : ∀ {x} → FiView x → ∀ y → le x y ≡ true → lt x ⟨ Om y ⟩ ≡ true
Fi≺Ω (fiψ d) y h = unf⁻ (psi IR d) (Om y) refl h
Fi≺Ω fiI     y h = unf⁻ I (Om y) refl (not-≡false (⪯⇒¬≺ y ⟨ I ⟩ (le! h)))

Ω≺Fi : ∀ {y} → FiView y → ∀ x → lt x y ≡ true → lt ⟨ Om x ⟩ y ≡ true
Ω≺Fi (fiψ d) x h = unf⁻ (Om x) (psi IR d) refl (not-≡false (not-true (trans (sym (lt-lin′ x ⟨ psi IR d ⟩)) h)))
Ω≺Fi fiI     x h = unf⁻ (Om x) I refl h

Ω-mono′ : ∀ x y → le x y ≡ true → le (Ω x) (Ω y) ≡ true
Ω-mono′ x y h with ωView x | ωView y
... | Ω0 | _ = 0⪯′ (Ω y)
... | ΩFi fx ex | Ω0 = ⊥-elim (true≢false (trans (sym h) (NZ⇒¬⪯0 x (nz fx))))
  where
    nz : ∀ {x} → FiView x → NZ x
    nz (fiψ d) = tt
    nz fiI     = tt
... | ΩFi fx ex | ΩFi fy ey = subst (λ u → le u (Ω y) ≡ true) (sym ex) (subst (λ v → le x v ≡ true) (sym ey) h)
... | ΩFi fx ex | ΩΩ _ _ ey = subst (λ u → le u (Ω y) ≡ true) (sym ex) (subst (λ v → le x v ≡ true) (sym ey) (leˡ x ⟨ Om y ⟩ (Fi≺Ω fx y h)))
... | ΩΩ nx _ ex | Ω0 = ⊥-elim (true≢false (trans (sym h) (NZ⇒¬⪯0 x nx)))
... | ΩΩ nx fx ex | ΩFi fy ey = subst (λ u → le u (Ω y) ≡ true) (sym ex) (subst (λ v → le ⟨ Om x ⟩ v ≡ true) (sym ey) (leˡ ⟨ Om x ⟩ y (Ω≺Fi fy x xy)))
  where
    xy : lt x y ≡ true
    xy with ∨-true h
    ... | inj₁ l = l
    ... | inj₂ e with eqT-sound x y e
    ...   | refl = ⊥-elim (true≢false (trans (sym (fi fy)) fx))
      where
        fi : ∀ {y} → FiView y → isFiT y ≡ true
        fi (fiψ d) = refl
        fi fiI     = refl
... | ΩΩ _ _ ex | ΩΩ _ _ ey = subst (λ u → le u (Ω y) ≡ true) (sym ex) (subst (λ v → le ⟨ Om x ⟩ v ≡ true) (sym ey) body)
  where
    body : le ⟨ Om x ⟩ ⟨ Om y ⟩ ≡ true
    body with ∨-true h
    ... | inj₂ e with eqT-sound x y e
    ...   | refl = leʳ ⟨ Om x ⟩ ⟨ Om x ⟩ (eqT-refl ⟨ Om x ⟩)
    body | inj₁ l = leˡ ⟨ Om x ⟩ ⟨ Om y ⟩ (unf⁻ (Om x) (Om y) (≺⇒eqT-false x y (AT-all x y) l) l)

Ω-mono< : ∀ x y → lt x y ≡ true → lt (Ω x) (Ω y) ≡ true
Ω-mono< x y h with ωView x | ωView y
... | _ | Ω0 = ⊥-elim (true≢false (trans (sym h) (lt-zero x)))
... | Ω0 | ΩFi (fiψ d) ey = subst (λ v → lt zer v ≡ true) (sym ey) (lt-zer zer (psi IR d))
... | Ω0 | ΩFi fiI ey     = subst (λ v → lt zer v ≡ true) (sym ey) (lt-zer zer I)
... | Ω0 | ΩΩ _ _ ey      = subst (λ v → lt zer v ≡ true) (sym ey) (lt-zer zer (Om y))
... | ΩFi fx ex | ΩFi fy ey = subst (λ u → lt u (Ω y) ≡ true) (sym ex) (subst (λ v → lt x v ≡ true) (sym ey) h)
... | ΩFi fx ex | ΩΩ _ _ ey = subst (λ u → lt u (Ω y) ≡ true) (sym ex) (subst (λ v → lt x v ≡ true) (sym ey) (Fi≺Ω fx y (leˡ x y h)))
... | ΩΩ _ _ ex | ΩFi fy ey = subst (λ u → lt u (Ω y) ≡ true) (sym ex) (subst (λ v → lt ⟨ Om x ⟩ v ≡ true) (sym ey) (Ω≺Fi fy x h))
... | ΩΩ _ _ ex | ΩΩ _ _ ey = subst (λ u → lt u (Ω y) ≡ true) (sym ex) (subst (λ v → lt ⟨ Om x ⟩ v ≡ true) (sym ey) (unf⁻ (Om x) (Om y) (≺⇒eqT-false x y (AT-all x y) h) h))

-- y ⪯ Ω y
⪯Ω : ∀ y → le y (Ω y) ≡ true
⪯Ω y with ωView y
... | Ω0 = refl
... | ΩFi _ ey = subst (λ v → le y v ≡ true) (sym ey) (leʳ y y (eqT-refl y))
... | ΩΩ _ _ ey = subst (λ v → le y v ≡ true) (sym ey) (leˡ y ⟨ Om y ⟩ (≺-Ωa y))

Ω-OT : ∀ x → OT x → OT (Ω x)
Ω-OT x (ot! ox) with ωView x
... | Ω0 = ot! refl
... | ΩFi _ ex = ot! (subst (λ v → isOT v ≡ true) (sym ex) ox)
... | ΩΩ nx fx ex = ot! (subst (λ v → isOT v ≡ true) (sym ex) (∧-intro ox (∧-intro (not-≡false fx) (not-≡false (nzF nx)))))
  where
    nzF : ∀ {x} → NZ x → isZero x ≡ false
    nzF {a ▹ p} _ = refl

-- OT ⟨ Ω′_a ⟩ 时 Ω a = ⟨ Ω′_a ⟩
Ω-of-OT : ∀ a → OT ⟨ Om a ⟩ → Ω a ≡ ⟨ Om a ⟩
Ω-of-OT a (ot! o) with ωView a
... | Ω0 = ⊥-elim (true≢false (sym o))
... | ΩFi (fiψ d) _ = ⊥-elim (true≢false (sym (∧₂ (isOT ⟨ psi IR d ⟩) false o)))
... | ΩFi fiI _     = ⊥-elim (true≢false (sym (∧₂ (isOT ⟨ I ⟩) false o)))
... | ΩΩ _ _ ea = ea
```

## 3. 字段

```agda
0⪯ : ∀ x → zer ⪯ x
0⪯ x = le! (0⪯′ x)

⪯-prefix : ∀ {y z} → NZ z → OT (app y z) → y ⪯ app y z
⪯-prefix {y} {z} nz _ = le! (leˡ y (app y z) (≺-prefix y z nz))

⪯-φˡ : ∀ {b c} → OT ⟨ phi b c ⟩ → b ⪯ ⟨ phi b c ⟩
⪯-φˡ {b} {c} _ = le! (leˡ b ⟨ phi b c ⟩ (≺-φˡ b c))

⪯-φʳ : ∀ {b c} → OT ⟨ phi b c ⟩ → c ⪯ ⟨ phi b c ⟩
⪯-φʳ {b} {c} _ = le! (leˡ c ⟨ phi b c ⟩ (≺-φʳ b c))

⪯-Ω : ∀ {b} → OT ⟨ Om b ⟩ → b ⪯ ⟨ Om b ⟩
⪯-Ω {b} _ = le! (leˡ b ⟨ Om b ⟩ (≺-Ωa b))

ψ≺κ : ∀ {κ c} → OT ⟨ psi κ c ⟩ → ⟨ psi κ c ⟩ ≺ regTm κ
ψ≺κ {κ = ΩR b} {c} _ = lt! (unf⁻ (psi (ΩR b) c) (Om b) refl (leʳ ⟨ Om b ⟩ ⟨ Om b ⟩ (eqT-refl ⟨ Om b ⟩)))
ψ≺κ {κ = IR}   {c} _ = lt! (unf⁻ (psi IR c) I refl refl)

-- OT ⟨ ψ_{Ω′_b} c ⟩ ⟹ b ∈ Suc′
ψΩ-Suc : ∀ b c → OT ⟨ psi (ΩR b) c ⟩ → isSuc b ≡ true
ψΩ-Suc b c (ot! o) = ∧₁ (isSuc b) (allLt (G (ΩR b) c) c) (∧₂ (isOTR (ΩR b)) _ (∧₂ (isOT c) _ o))

-- Ω′_b ∈ OT 的 b：非零、非 Fi′
Ω-arg : ∀ b → OT ⟨ Om b ⟩ → NZ b × isFiT b ≡ false
Ω-arg zer     (ot! o) = ⊥-elim (true≢false (sym o))
Ω-arg (a ▹ p) (ot! o) = tt , not-true (∧₁ (not (isFiT (a ▹ p))) true (∧₂ (isOT (a ▹ p)) (not (isFiT (a ▹ p)) ∧ true) o))

-- κ⁻ (Ω′_{b′+1}) = Ω b′ ≺ ψ_{Ω′_{b′+1}} c
κ⁻≺ψ : ∀ {b c} → OT ⟨ psi (ΩR b) c ⟩ → κ⁻ (ΩR b) ≺ ⟨ psi (ΩR b) c ⟩
κ⁻≺ψ {b} {c} o with sucView b (ψΩ-Suc b c o)
... | suc! b′ = lt! (body (ωView b′))
  where
    b′≺b : lt b′ (b′ ▹ phi zer zer) ≡ true
    b′≺b = ≺-▹ b′ (phi zer zer)
    body : ΩView b′ → lt (Ω b′) ⟨ psi (ΩR (b′ ▹ phi zer zer)) c ⟩ ≡ true
    body Ω0 = lt-zer zer (psi (ΩR (b′ ▹ phi zer zer)) c)
    body (ΩFi (fiψ d) e) = subst (λ u → lt u ⟨ psi (ΩR (b′ ▹ phi zer zer)) c ⟩ ≡ true) (sym e)
      (unf⁻ (psi IR d) (psi (ΩR (b′ ▹ phi zer zer)) c) refl
            (∨ˡ (lt ⟨ psi IR d ⟩ ⟨ Om (b′ ▹ phi zer zer) ⟩) false
                (unf⁻ (psi IR d) (Om (b′ ▹ phi zer zer)) refl (leˡ ⟨ psi IR d ⟩ (b′ ▹ phi zer zer) b′≺b))))
    body (ΩFi fiI e) = subst (λ u → lt u ⟨ psi (ΩR (b′ ▹ phi zer zer)) c ⟩ ≡ true) (sym e)
      (unf⁻ I (psi (ΩR (b′ ▹ phi zer zer)) c) refl
            (not-≡false (cong (_∨ false) (trans (lt-unfold≠ (Om (b′ ▹ phi zer zer)) I refl) (lt-asym ⟨ I ⟩ (b′ ▹ phi zer zer) b′≺b)))))
    body (ΩΩ _ _ e) = subst (λ u → lt u ⟨ psi (ΩR (b′ ▹ phi zer zer)) c ⟩ ≡ true) (sym e)
      (unf⁻ (Om b′) (psi (ΩR (b′ ▹ phi zer zer)) c) refl
            (not-≡false (cong₂ _∨_ (trans (lt-unfold≠ (Om (b′ ▹ phi zer zer)) (Om b′) ne) (lt-asym b′ (b′ ▹ phi zer zer) b′≺b)) ne)))
      where
        ne : eqT (b′ ▹ phi zer zer) b′ ≡ false
        ne = eqT-false-sym b′ (b′ ▹ phi zer zer) (≺⇒eqT-false b′ (b′ ▹ phi zer zer) (AT-all b′ _) b′≺b)

-- Ω (b′ ▹ 1) = ⟨ Om (b′ ▹ 1) ⟩
Ω-suc : ∀ b′ → Ω (b′ ▹ phi zer zer) ≡ ⟨ Om (b′ ▹ phi zer zer) ⟩
Ω-suc b′ with ωView (b′ ▹ phi zer zer)
... | ΩΩ _ _ e = e
... | ΩFi () _

κ⁻≺κ : ∀ {κ} → isRR κ ≡ true → OT (regTm κ) → κ⁻ κ ≺ regTm κ
κ⁻≺κ {κ = IR}   _ _ = lt! (lt-zer zer I)
κ⁻≺κ {κ = ΩR b} r _ with sucView b r
... | suc! b′ = lt! (subst (λ v → lt (Ω b′) v ≡ true) (Ω-suc b′) (Ω-mono< b′ (b′ ▹ phi zer zer) (≺-▹ b′ (phi zer zer))))

```

## 4. 更多字段

```agda
one⪯P : ∀ {p} → OT ⟨ p ⟩ → one ⪯ ⟨ p ⟩
one⪯P {p} _ = le! (one⪯P′ p)

between-app : ∀ {b c d} → NZ b → NZ c → OT (app b c) → OT d → b ≺ d → d ≺ app b c
            → ∃ λ d′ → d ≡ app b d′ × NZ d′ × d′ ≺ c
between-app {b} {c} {d} _ _ _ _ (lt! h₁) (lt! h₂) with between-app′ b c d h₁ h₂
... | d′ , eq , nz , l = d′ , eq , nz , lt! l

φ-cmp : ∀ {b c d₁ d₂} → OT ⟨ phi b c ⟩ → OT ⟨ phi d₁ d₂ ⟩ → ⟨ phi d₁ d₂ ⟩ ≺ ⟨ phi b c ⟩
      → (d₁ ≺ b × d₂ ≺ ⟨ phi b c ⟩) ⊎ (d₁ ≡ b × d₂ ≺ c) ⊎ (b ≺ d₁ × ⟨ phi d₁ d₂ ⟩ ⪯ c)
φ-cmp {b} {c} {d₁} {d₂} _ _ (lt! h) with ∨3-true (unf (phi d₁ d₂) (phi b c) h)
... | inj₁ x        = inj₁ (lt! (∧₁ (lt d₁ b) (lt d₂ ⟨ phi b c ⟩) x) , lt! (∧₂ (lt d₁ b) (lt d₂ ⟨ phi b c ⟩) x))
... | inj₂ (inj₁ x) = inj₂ (inj₁ (eqT-sound d₁ b (∧₁ (eqT d₁ b) (lt d₂ c) x) , lt! (∧₂ (eqT d₁ b) (lt d₂ c) x)))
... | inj₂ (inj₂ x) = inj₂ (inj₂ (lt! (∧₁ (lt b d₁) (le ⟨ phi d₁ d₂ ⟩ c) x) , le! (∧₂ (lt b d₁) (le ⟨ phi d₁ d₂ ⟩ c) x)))

φ≺G : ∀ {b c d} → isGT d ≡ true → OT d → OT ⟨ phi b c ⟩ → b ≺ d → c ≺ d → ⟨ phi b c ⟩ ≺ d
φ≺G {b} {c} {d} g _ _ (lt! hb) (lt! hc) with gView d g
... | gψ π e = lt! (trans (φG-lt b c (psi π e) refl) (∧ⁱ (lt b ⟨ psi π e ⟩) (lt c ⟨ psi π e ⟩) hb hc))
... | gΩ a   = lt! (trans (φG-lt b c (Om a) refl)    (∧ⁱ (lt b ⟨ Om a ⟩)    (lt c ⟨ Om a ⟩)    hb hc))
... | gI     = lt! (trans (φG-lt b c I refl)         (∧ⁱ (lt b ⟨ I ⟩)         (lt c ⟨ I ⟩)         hb hc))

Fi≺Ω⇒⪯ : ∀ {y b} → isFiT y ≡ true → OT y → OT ⟨ Om b ⟩ → y ≺ ⟨ Om b ⟩ → y ⪯ b
Fi≺Ω⇒⪯ {y} {b} f _ _ (lt! h) with fiView y f
... | fiψ d = le! (unf (psi IR d) (Om b) h)
... | fiI   = ¬≺⇒⪰ b ⟨ I ⟩ (not-true (unf I (Om b) h))

Ω-mono⁻ : ∀ {y b} → OT ⟨ Om y ⟩ → OT ⟨ Om b ⟩ → ⟨ Om y ⟩ ≺ ⟨ Om b ⟩ → y ≺ b
Ω-mono⁻ {y} {b} _ _ (lt! h) = lt! (unf (Om y) (Om b) h)

ψ≺Car⇒κ⪯ : ∀ {z c d} → isCarT d ≡ true → OT ⟨ psi (ΩR z) c ⟩ → OT d → ⟨ psi (ΩR z) c ⟩ ≺ d → ⟨ Om z ⟩ ⪯ d
ψ≺Car⇒κ⪯ {z} {c} {d} cd _ _ (lt! h) with carView d cd
... | carΩ a = le! (unf (psi (ΩR z) c) (Om a) h)
... | carψ e = le! (leˡ ⟨ Om z ⟩ ⟨ psi IR e ⟩ (unf (psi (ΩR z) c) (psi IR e) h))
... | carI   = le! (unf (psi (ΩR z) c) I h)

ψI-cmp : ∀ {b d} → OT ⟨ psi IR b ⟩ → OT ⟨ psi IR d ⟩ → ⟨ psi IR b ⟩ ≺ ⟨ psi IR d ⟩ → b ≺ d
ψI-cmp {b} {d} _ _ (lt! h) = lt! (trans (sym (sameRule IR b d)) h)

ψκ-mono : ∀ {κ b c} → OT ⟨ psi κ b ⟩ → OT ⟨ psi κ c ⟩ → b ≺ c → ⟨ psi κ b ⟩ ≺ ⟨ psi κ c ⟩
ψκ-mono {κ} {b} {c} _ _ (lt! h) = lt! (trans (sameRule κ b c) h)

ψI-mono : ∀ {b c} → OT ⟨ psi IR b ⟩ → OT ⟨ psi IR c ⟩ → b ≺ c → ⟨ psi IR b ⟩ ≺ ⟨ psi IR c ⟩
ψI-mono = ψκ-mono

+1-least : ∀ {b c} → OT b → OT c → b ≺ c → b + one ⪯ c
+1-least {b} {c} _ _ (lt! h) = le! (+1-least′ b c h)

+1-mono : ∀ {x y} → OT x → OT y → x ⪯ y → x + one ⪯ y + one
+1-mono {x} {y} _ _ (le! h) = le! (+1-mono′ x y h)

-- y ▹ 1 不是 Car′ 元素
▹1≢Car : ∀ {κ} → CarView κ → ∀ y → y ▹ phi zer zer ≡ κ → ⊥
▹1≢Car (carΩ a) y ()
▹1≢Car (carψ d) y ()
▹1≢Car carI     y ()

Car-closed-+1 : ∀ {κ y} → isCarT κ ≡ true → OT κ → OT y → y ≺ κ → y + one ≺ κ
Car-closed-+1 {κ} {y} ck _ _ (lt! h) with ∨-true (+1-least′ y κ h)
... | inj₁ l = lt! l
... | inj₂ e = ⊥-elim (▹1≢Car (carView κ ck) y (trans (sym (+one y)) (eqT-sound (y + one) κ e)))

-- 1 ⪯ 非零项
one⪯NZ : ∀ x → NZ x → le one x ≡ true
one⪯NZ x nz with toList-hd x nz | caseEq (eqP (phi zer zer) (hd x))
... | rest , eq | inj₂ e =
  leˡ one x (trans (lt-list one x) (subst (λ l → ltLx (phi zer zer ∷ []) l ≡ true) (sym eq)
              (ltLx-sing⁻ (phi zer zer) [] (hd x) rest (one≺P (hd x) e))))
... | [] , eq | inj₁ e = leʳ one x (eqT-complete (toList-inj one x (sym (trans eq (cong (_∷ []) (sym (eqP-sound (phi zer zer) (hd x) e)))))))
... | (r ∷ rs) , eq | inj₁ e =
  leˡ one x (trans (lt-list one x) (subst (λ l → ltLx (phi zer zer ∷ []) l ≡ true) (sym eq)
              (if-true {b = eqP (phi zer zer) (hd x)} {x = ltLx [] (r ∷ rs)} {y = lt one ⟨ hd x ⟩} e)))

Ω₁⪯R : ∀ {κ} → OT (regTm κ) → isRR κ ≡ true → Ω₁ ⪯ regTm κ
Ω₁⪯R {κ = IR}   _ _ = le! (leˡ Ω₁ ⟨ I ⟩ (unf⁻ (Om one) I refl (one≺P I refl)))
Ω₁⪯R {κ = ΩR b} _ r with sucView b r
... | suc! b′ = le! (subst (λ v → le Ω₁ v ≡ true) (Ω-suc b′) (Ω-mono′ one (b′ ▹ phi zer zer) (one⪯NZ (b′ ▹ phi zer zer) tt)))

-- Ω 在 Fi′ 上是恒等
Ω-Fi : ∀ f → isFiT f ≡ true → Ω f ≡ f
Ω-Fi f ff with ωView f
... | Ω0 = ⊥-elim (true≢false (sym ff))
... | ΩFi _ e = e
... | ΩΩ _ fx _ = ⊥-elim (true≢false (trans (sym ff) fx))

Ω≺Ω′ : ∀ {y a} → OT y → OT ⟨ Om a ⟩ → y ≺ a → Ω y ≺ ⟨ Om a ⟩
Ω≺Ω′ {y} {a} _ oa (lt! h) = lt! (subst (λ v → lt (Ω y) v ≡ true) (Ω-of-OT a oa) (Ω-mono< y a h))

Fi-closed-Ω : ∀ {f y} → isFiT f ≡ true → OT f → OT y → y ≺ f → Ω y ≺ f
Fi-closed-Ω {f} {y} ff _ _ (lt! h) = lt! (subst (λ v → lt (Ω y) v ≡ true) (Ω-Fi f ff) (Ω-mono< y f h))

Ωⁿ-mono : ∀ {x y} n → OT x → OT y → x ⪯ y → Ωⁿ x n ⪯ Ωⁿ y n
Ωⁿ-mono {x} {y} n _ _ (le! h) = le! (go n)
  where
    go : ∀ n → le (Ωⁿ x n) (Ωⁿ y n) ≡ true
    go zero    = h
    go (suc n) = Ω-mono′ (Ωⁿ x n) (Ωⁿ y n) (go n)

Ωⁿ-OT : ∀ {x} n → OT x → OT (Ωⁿ x n)
Ωⁿ-OT zero        o = o
Ωⁿ-OT {x} (suc n) o = Ω-OT (Ωⁿ x n) (Ωⁿ-OT n o)

ψI0-least : ∀ {z} → isFiT z ≡ true → OT z → ⟨ psi IR zer ⟩ ⪯ z
ψI0-least {z} f _ with fiView z f
... | fiψ zer     = le! (leʳ ⟨ psi IR zer ⟩ ⟨ psi IR zer ⟩ (eqT-refl ⟨ psi IR zer ⟩))
... | fiψ (a ▹ p) = le! (leˡ ⟨ psi IR zer ⟩ ⟨ psi IR (a ▹ p) ⟩ (trans (sameRule IR zer (a ▹ p)) (lt-zer a p)))
... | fiI         = le! (leˡ ⟨ psi IR zer ⟩ ⟨ I ⟩ (unf⁻ (psi IR zer) I refl refl))

Fi≺ψI+1⇒⪯ : ∀ {z x} → isFiT z ≡ true → OT z → OT ⟨ psi IR (x + one) ⟩
           → z ≺ ⟨ psi IR (x + one) ⟩ → z ⪯ ⟨ psi IR x ⟩
Fi≺ψI+1⇒⪯ {z} {x} f _ _ (lt! h) with fiView z f
... | fiI   = ⊥-elim (true≢false (trans (sym h) (lt-unfold≠ I (psi IR (x + one)) refl)))
... | fiψ d with ∨-true (≺+1⇒⪯ d x (trans (sym (sameRule IR d (x + one))) h))
...   | inj₁ l = le! (leˡ ⟨ psi IR d ⟩ ⟨ psi IR x ⟩ (trans (sameRule IR d x) l))
...   | inj₂ e = le! (leʳ ⟨ psi IR d ⟩ ⟨ psi IR x ⟩ (eqT-complete (cong (λ w → ⟨ psi IR w ⟩) (eqT-sound d x e))))

-- Car′ 元素 ≺ Ω′_{z′+1} ⟹ ⪯ Ω z′
Car≺κ⇒⪯κ⁻ : ∀ {c z} → OT c → isCarT c ≡ true → isRR (ΩR z) ≡ true → OT ⟨ Om z ⟩
           → c ≺ ⟨ Om z ⟩ → c ⪯ κ⁻ (ΩR z)
Car≺κ⇒⪯κ⁻ {c} {z} oc cc r oz (lt! h) with sucView z r
... | suc! z′ = le! (body (carView c cc))
  where
    z1 = z′ ▹ phi zer zer
    -- ⟨ p ⟩ ⪯ z′ ▹ 1 且 ⟨ p ⟩ ≠ z′ ▹ 1 ⟹ ⟨ p ⟩ ⪯ z′
    down : ∀ p → (⟨ p ⟩ ≡ z1 → ⊥) → le ⟨ p ⟩ z1 ≡ true → le ⟨ p ⟩ z′ ≡ true
    down p ne l with ∨-true l
    ... | inj₁ g = ≺+1⇒⪯ ⟨ p ⟩ z′ (subst (λ v → lt ⟨ p ⟩ v ≡ true) (sym (+one z′)) g)
    ... | inj₂ e = ⊥-elim (ne (eqT-sound ⟨ p ⟩ z1 e))
    body : CarView c → le c (Ω z′) ≡ true
    body (carΩ a) = subst (λ u → le u (Ω z′) ≡ true) (Ω-of-OT a oc)
      (Ω-mono′ a z′ (≺+1⇒⪯ a z′ (subst (λ v → lt a v ≡ true) (sym (+one z′)) (unf (Om a) (Om z1) h))))
    body (carψ d) = Ω-mono′ ⟨ psi IR d ⟩ z′ (down (psi IR d) (λ ()) (unf (psi IR d) (Om z1) h))
    body carI     = Ω-mono′ ⟨ I ⟩ z′ (down I (λ ()) (¬≺⇒⪰′ (not-true (unf I (Om z1) h))))
      where
        ¬≺⇒⪰′ : lt z1 ⟨ I ⟩ ≡ false → le ⟨ I ⟩ z1 ≡ true
        ¬≺⇒⪰′ g = le≡ (¬≺⇒⪰ z1 ⟨ I ⟩ g)

plus-κ⁻ : ∀ {z} → isRR (ΩR z) ≡ true → OT ⟨ Om z ⟩ → plus (κ⁻ (ΩR z)) ≡ ⟨ Om z ⟩
plus-κ⁻ {z} r _ with sucView z r
... | suc! z′ = body (ωView z′)
  where
    body : ΩView z′ → plus (Ω z′) ≡ ⟨ Om (z′ ▹ phi zer zer) ⟩
    body Ω0              = refl
    body (ΩFi (fiψ d) e) = trans (cong plus e) (trans (cong Ω (+one ⟨ psi IR d ⟩)) (Ω-suc ⟨ psi IR d ⟩))
    body (ΩFi fiI e)     = trans (cong plus e) (trans (cong Ω (+one ⟨ I ⟩)) (Ω-suc ⟨ I ⟩))
    body (ΩΩ _ _ e)      = trans (cong plus e) (trans (cong Ω (+one z′)) (Ω-suc z′))

Om-inj : ∀ {x y} → ⟨ Om x ⟩ ≡ ⟨ Om y ⟩ → x ≡ y
Om-inj refl = refl

κ⁻∘plus : ∀ {τ z} → isCarT τ ≡ true → OT τ → plus τ ≡ ⟨ Om z ⟩ → κ⁻ (ΩR z) ≡ τ
κ⁻∘plus {τ} {z} ct oτ e with carView τ ct
... | carΩ b = subst (λ w → κ⁻ (ΩR w) ≡ ⟨ Om b ⟩) (Om-inj (trans (sym (trans (cong Ω (+one b)) (Ω-suc b))) e)) (Ω-of-OT b oτ)
... | carψ d = subst (λ w → κ⁻ (ΩR w) ≡ ⟨ psi IR d ⟩) (Om-inj (trans (sym (trans (cong Ω (+one ⟨ psi IR d ⟩)) (Ω-suc ⟨ psi IR d ⟩))) e)) refl
... | carI   = subst (λ w → κ⁻ (ΩR w) ≡ ⟨ I ⟩) (Om-inj (trans (sym (trans (cong Ω (+one ⟨ I ⟩)) (Ω-suc ⟨ I ⟩))) e)) refl
```

## 5. 非递增和的后缀（Remark 2.12 (h) 的 `z ⪯ y + z`）

```agda
NonInc : List PTm → Set
NonInc []           = ⊤
NonInc (p ∷ [])     = ⊤
NonInc (p ∷ q ∷ ps) = (le ⟨ q ⟩ ⟨ p ⟩ ≡ true) × NonInc (q ∷ ps)

NonInc-tail : ∀ p ps → NonInc (p ∷ ps) → NonInc ps
NonInc-tail p []       _        = tt
NonInc-tail p (q ∷ ps) (_ , ni) = ni

NonInc-snoc : ∀ l q p → NonInc (l ++ q ∷ []) → le ⟨ p ⟩ ⟨ q ⟩ ≡ true → NonInc (l ++ q ∷ p ∷ [])
NonInc-snoc []            q p _         pq = pq , tt
NonInc-snoc (x ∷ [])      q p (qx , _)  pq = qx , pq , tt
NonInc-snoc (x ∷ x′ ∷ l′) q p (x′x , ni) pq = x′x , NonInc-snoc (x′ ∷ l′) q p ni pq

OT⇒NonInc : ∀ t → isOT t ≡ true → NonInc (toList t)
OT⇒NonInc zer         _ = tt
OT⇒NonInc (zer ▹ p)   _ = tt
OT⇒NonInc (a ▹ q ▹ p) o =
  subst NonInc (sym (trans (toList-▹ (a ▹ q) p) (trans (cong (_++ p ∷ []) (toList-▹ a q)) (++-assoc (toList a) (q ∷ []) (p ∷ [])))))
        (NonInc-snoc (toList a) q p (subst NonInc (toList-▹ a q) (OT⇒NonInc (a ▹ q) (∧₁ (isOT (a ▹ q)) _ o)))
                     (∧₂ (isOTP p) (le ⟨ p ⟩ ⟨ q ⟩) (∧₂ (isOT (a ▹ q)) _ o)))
  where open import Data.List.Properties using (++-assoc)

fromL-toList : ∀ t → fromL (toList t) ≡ t
fromL-toList t = toList-inj (fromL (toList t)) t (toList-fromL (toList t))

-- 表的比较化到项
ltL⇒lt : ∀ xs ys → ltLx xs ys ≡ true → lt (fromL xs) (fromL ys) ≡ true
ltL⇒lt xs ys h = trans (lt-list (fromL xs) (fromL ys)) (trans (cong₂ ltLx (toList-fromL xs) (toList-fromL ys)) h)

tail-le : ∀ z zs → NonInc (z ∷ zs) → (ltLx zs (z ∷ zs) ≡ true) ⊎ (zs ≡ [])
tail-le z []       _         = inj₂ refl
tail-le z (w ∷ zs) (wz , ni) with caseEq (eqP w z)
... | inj₂ e = inj₁ (trans (if-false e) wlt)
  where
    wlt : lt ⟨ w ⟩ ⟨ z ⟩ ≡ true
    wlt with ∨-true wz
    ... | inj₁ l = l
    ... | inj₂ q = ⊥-elim (true≢false (trans (sym q) e))
... | inj₁ e with eqP-sound w z e
...   | refl with tail-le w zs ni
...     | inj₁ l    = inj₁ (trans (if-true e) l)
...     | inj₂ refl = inj₁ (if-true {b = eqP w w} {x = ltLx [] (w ∷ [])} {y = lt ⟨ w ⟩ ⟨ w ⟩} e)

tail-le′ : ∀ z zs → NonInc (z ∷ zs) → le (fromL zs) (fromL (z ∷ zs)) ≡ true
tail-le′ z zs ni with tail-le z zs ni
... | inj₁ l    = leˡ (fromL zs) (fromL (z ∷ zs)) (ltL⇒lt zs (z ∷ zs) l)
... | inj₂ refl = leˡ (fromL []) (fromL (z ∷ [])) (ltL⇒lt [] (z ∷ []) refl)

suffix-le : ∀ ys zs → NonInc (ys ++ zs) → le (fromL zs) (fromL (ys ++ zs)) ≡ true
suffix-le []       zs _  = leʳ (fromL zs) (fromL zs) (eqT-refl (fromL zs))
suffix-le (y ∷ ys) zs ni =
  le≡ (⪯-trans {fromL zs} {fromL (ys ++ zs)} {fromL (y ∷ ys ++ zs)}
        (le! (suffix-le ys zs (NonInc-tail y (ys ++ zs) ni))) (le! (tail-le′ y (ys ++ zs) ni)))

⪯-app : ∀ {y z} → NZ y → NZ z → OT (app y z) → z ⪯ app y z
⪯-app {y} {z} _ _ (ot! o) =
  le! (subst₂ (λ u v → le u v ≡ true) (fromL-toList z)
              (toList-inj (fromL (toList y ++ toList z)) (app y z) (trans (toList-fromL _) (sym (toList-app y z))))
              (suffix-le (toList y) (toList z) (subst NonInc (toList-app y z) (OT⇒NonInc (app y z) o))))
  where open import Relation.Binary.PropositionalEquality using (subst₂)
```
