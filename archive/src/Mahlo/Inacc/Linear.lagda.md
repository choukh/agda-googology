# Lemma 2.4（一）：不可反与三分

对全部 T′ 项证 `lt` 是**反对称**且**全**的：`s ≺ t → ¬ (t ≺ s)`，`¬ (s ≺ t) → ¬ (t ≺ s) → s ≡ t`。
方法：对 `size s + size t` 强归纳；和的比较经 [`lt-list`](OrderProps.lagda.md) 化为字典序，主元项的比较经 [`lt-unfold`](Unfold.lagda.md) 化为 (≺′3)–(≺′11) 的右边。
跨形状的两个主元项（φ 对 G′，Ω′ 对 ψ，…）是 (≺′11) 直接定义的互否，逐字 `refl`；只有同形状对（φφ、ψψ、Ω′Ω′）要用归纳假设。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Linear where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.BoolLemmas
open import Mahlo.Inacc.OrderProps using (ltLx; lt-list)
open import Mahlo.Inacc.Unfold

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; <-≤-trans; <⇒≤; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤;
                                       +-mono-<-≤; +-mono-≤-<; +-mono-<; m≤m+n; m≤n+m; m≤n⇒m≤1+n; n≤1+n; +-comm)
open import Relation.Nullary using (¬_)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ; not-involutive)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
```

## 1. 基本工具

```agda
caseEq : ∀ (b : Bool) → b ≡ true ⊎ b ≡ false
caseEq true  = inj₁ refl
caseEq false = inj₂ refl

eqT-false-sym : ∀ s t → eqT s t ≡ false → eqT t s ≡ false
eqT-false-sym s t e with caseEq (eqT t s)
... | inj₂ f = f
... | inj₁ g with eqT-sound t s g
...   | refl = ⊥-elim (true≢false (trans (sym (eqT-refl s)) e))

eqP-false-sym : ∀ p q → eqP p q ≡ false → eqP q p ≡ false
eqP-false-sym p q e with caseEq (eqP q p)
... | inj₂ f = f
... | inj₁ g with eqP-sound q p g
...   | refl = ⊥-elim (true≢false (trans (sym (eqP-refl p)) e))

-- 反对称 + 全
Asym : Tm → Tm → Set
Asym s t = lt s t ≡ true → lt t s ≡ true → ⊥

Tot : Tm → Tm → Set
Tot s t = lt s t ≡ false → lt t s ≡ false → s ≡ t

AT : Tm → Tm → Set
AT s t = Asym s t × Tot s t

-- 由 AT 得到的三种「互否」等式
lin : ∀ s t → AT s t → eqT s t ≡ false → lt s t ≡ not (lt t s)
lin s t (as , to) e with caseEq (lt s t) | caseEq (lt t s)
... | inj₁ p | inj₁ q = ⊥-elim (as p q)
... | inj₁ p | inj₂ q = trans p (cong not (sym q))
... | inj₂ p | inj₁ q = trans p (cong not (sym q))
... | inj₂ p | inj₂ q = ⊥-elim (true≢false (trans (sym (eqT-complete (to p q))) e))

lin′ : ∀ s t → AT s t → lt s t ≡ not (le t s)
lin′ s t (as , to) with caseEq (lt s t) | caseEq (lt t s)
... | inj₁ p | inj₁ q = ⊥-elim (as p q)
... | inj₁ p | inj₂ q = trans p (cong not (sym (trans (cong (_∨ eqT t s) q) (ne p))))
  where
    ne : lt s t ≡ true → false ∨ eqT t s ≡ false
    ne p′ with caseEq (eqT t s)
    ... | inj₂ f = f
    ... | inj₁ g with eqT-sound t s g
    ...   | refl = ⊥-elim (as p′ p′)
... | inj₂ p | inj₁ q = trans p (cong not (sym (cong (_∨ eqT t s) q)))
... | inj₂ p | inj₂ q with to p q
...   | refl = trans p (cong not (sym (trans (cong (_∨ eqT s s) q) (eqT-refl s))))

lin″ : ∀ s t → AT s t → le t s ≡ not (lt s t)
lin″ s t h = sym (trans (cong not (lin′ s t h)) (not-involutive _))

AT-sym : ∀ s t → AT s t → AT t s
AT-sym s t (as , to) = (λ p q → as q p) , (λ p q → sym (to q p))

-- 主元项版本
ATP : PTm → PTm → Set
ATP p q = (lt ⟨ p ⟩ ⟨ q ⟩ ≡ true → lt ⟨ q ⟩ ⟨ p ⟩ ≡ true → ⊥)
        × (lt ⟨ p ⟩ ⟨ q ⟩ ≡ false → lt ⟨ q ⟩ ⟨ p ⟩ ≡ false → p ≡ q)
```

## 2. 字典序层

```agda
_∈_ : PTm → List PTm → Set
p ∈ ps = Any (p ≡_) ps

AsymL TotL : List PTm → List PTm → Set
AsymL ps qs = ltLx ps qs ≡ true → ltLx qs ps ≡ true → ⊥
TotL  ps qs = ltLx ps qs ≡ false → ltLx qs ps ≡ false → ps ≡ qs

listAT : ∀ ps qs → (∀ p q → p ∈ ps → q ∈ qs → ATP p q) → AsymL ps qs × TotL ps qs
listAT []       []       _ = (λ ()) , (λ _ _ → refl)
listAT []       (q ∷ qs) _ = (λ _ ()) , (λ ())
listAT (p ∷ ps) []       _ = (λ ()) , (λ _ ())
listAT (p ∷ ps) (q ∷ qs) H with caseEq (eqP p q)
... | inj₁ e with eqP-sound p q e
...   | refl = as , to
  where
    ih = listAT ps qs (λ p′ q′ i j → H p′ q′ (there i) (there j))
    e′ : eqP p p ≡ true
    e′ = eqP-refl p
    as : AsymL (p ∷ ps) (p ∷ qs)
    as h₁ h₂ = proj₁ ih (trans (sym (if-true e′)) h₁) (trans (sym (if-true e′)) h₂)
    to : TotL (p ∷ ps) (p ∷ qs)
    to h₁ h₂ = cong (p ∷_) (proj₂ ih (trans (sym (if-true e′)) h₁) (trans (sym (if-true e′)) h₂))
listAT (p ∷ ps) (q ∷ qs) H | inj₂ e = as , to
  where
    e′ : eqP q p ≡ false
    e′ = eqP-false-sym p q e
    hp = H p q (here refl) (here refl)
    as : AsymL (p ∷ ps) (q ∷ qs)
    as h₁ h₂ = proj₁ hp (trans (sym (if-false e)) h₁) (trans (sym (if-false e′)) h₂)
    to : TotL (p ∷ ps) (q ∷ qs)
    to h₁ h₂ = ⊥-elim (true≢false (trans (sym (eqP-complete (proj₂ hp (trans (sym (if-false e)) h₁) (trans (sym (if-false e′)) h₂)))) e))
      where
        eqP-complete : ∀ {p q} → p ≡ q → eqP p q ≡ true
        eqP-complete {p} refl = eqP-refl p

-- toList 单射
goL : Tm → List PTm → Tm
goL a []       = a
goL a (p ∷ ps) = goL (a ▹ p) ps

goL-acc : ∀ s acc → goL zer (toListAcc s acc) ≡ goL s acc
goL-acc zer     acc = refl
goL-acc (a ▹ p) acc = goL-acc a (p ∷ acc)

toList-inj : ∀ s t → toList s ≡ toList t → s ≡ t
toList-inj s t e = trans (sym (goL-acc s [])) (trans (cong (goL zer) e) (goL-acc t []))

-- 分量的大小不超过整体
∈-size : ∀ s acc p → p ∈ toListAcc s acc → p ∈ acc ⊎ size ⟨ p ⟩ ≤ size s
∈-size zer     acc p i = inj₁ i
∈-size (a ▹ q) acc p i with ∈-size a (q ∷ acc) p i
... | inj₁ (here refl) = inj₂ (+-monoˡ-≤ (sizeP q) (size≥1 a))
  where
    size≥1 : ∀ s → 1 ≤ size s
    size≥1 zer     = ≤-refl
    size≥1 (a ▹ p) = ≤-trans (size≥1 a) (m≤m+n (size a) (sizeP p))
... | inj₁ (there j) = inj₁ j
... | inj₂ h         = inj₂ (≤-trans h (m≤m+n (size a) (sizeP q)))

∈-size′ : ∀ s p → p ∈ toList s → size ⟨ p ⟩ ≤ size s
∈-size′ s p i with ∈-size s [] p i
... | inj₁ ()
... | inj₂ h = h
```

## 3. 同形状主元项对

归纳假设的形状：比 `size ⟨ p ⟩ + size ⟨ q ⟩` 小的一切项对都已反对称且全。

```agda
IH : ℕ → Set
IH m = ∀ s t → size s + size t < m → AT s t

-- 大小引理
sz-φˡ : ∀ a b → size a < size ⟨ phi a b ⟩
sz-φˡ a b = s≤s (m≤n⇒m≤1+n (m≤m+n (size a) (size b)))
sz-φʳ : ∀ a b → size b < size ⟨ phi a b ⟩
sz-φʳ a b = s≤s (m≤n⇒m≤1+n (m≤n+m (size b) (size a)))
sz-Ω : ∀ a → size a < size ⟨ Om a ⟩
sz-Ω a = s≤s (n≤1+n (size a))
sz-ψb : ∀ π b → size b < size ⟨ psi π b ⟩
sz-ψb π b = s≤s (m≤n⇒m≤1+n (m≤n+m (size b) (sizeR π)))
sz-ψΩ : ∀ a b → size ⟨ Om a ⟩ < size ⟨ psi (ΩR a) b ⟩
sz-ψΩ a b = s≤s (s≤s (s≤s (m≤m+n (size a) (size b))))

-- 互否等式的形状
Fl : PTm → PTm → Set
Fl p q = ltP′ p q ≡ not (ltP′ q p)

Fl-sym : ∀ p q → Fl p q → Fl q p
Fl-sym p q e = sym (trans (cong not e) (not-involutive _))

-- 布尔形状引理
φφ₁ : ∀ {ac ca ea ec bY Yb bd db Xd dX : Bool} → ac ≡ true → ca ≡ false → ea ≡ false → ec ≡ false → bY ≡ not Yb
    → (ac ∧ bY) ∨ (ea ∧ bd) ∨ (ca ∧ Xd) ≡ not ((ca ∧ dX) ∨ (ec ∧ db) ∨ (ac ∧ Yb))
φφ₁ refl refl refl refl h = trans (∨-identityʳ _) h

φφ₂ : ∀ {aa ea bY bd db Xd dX Yb : Bool} → aa ≡ false → ea ≡ true → bd ≡ not db
    → (aa ∧ bY) ∨ (ea ∧ bd) ∨ (aa ∧ Xd) ≡ not ((aa ∧ dX) ∨ (ea ∧ db) ∨ (aa ∧ Yb))
φφ₂ refl refl h = trans (∨-identityʳ _) (trans h (cong not (sym (∨-identityʳ _))))

φφ₃ : ∀ {ac ca ea ec bY Yb bd db Xd dX : Bool} → ac ≡ false → ca ≡ true → ea ≡ false → ec ≡ false → Xd ≡ not dX
    → (ac ∧ bY) ∨ (ea ∧ bd) ∨ (ca ∧ Xd) ≡ not ((ca ∧ dX) ∨ (ec ∧ db) ∨ (ac ∧ Yb))
φφ₃ refl refl refl refl h = trans h (cong not (sym (∨-identityʳ _)))

ψψ₁ : ∀ {ea ec bd db oo oo′ : Bool} → ea ≡ false → ec ≡ false → oo ≡ not oo′
    → (ea ∧ bd) ∨ (oo ∨ (false ∨ false)) ≡ not ((ec ∧ db) ∨ (oo′ ∨ (false ∨ false)))
ψψ₁ refl refl h = trans (∨-identityʳ _) (trans h (cong not (sym (∨-identityʳ _))))

ψψ₂ : ∀ {ea bd db oo : Bool} → ea ≡ true → oo ≡ false → bd ≡ not db
    → (ea ∧ bd) ∨ (oo ∨ (false ∨ false)) ≡ not ((ea ∧ db) ∨ (oo ∨ (false ∨ false)))
ψψ₂ refl refl h = trans (∨-identityʳ _) (trans h (cong not (sym (∨-identityʳ _))))

x∨false : ∀ {x y : Bool} → x ≡ not y → x ∨ false ≡ not (y ∨ false)
x∨false h = trans (∨-identityʳ _) (trans h (cong not (sym (∨-identityʳ _))))

x∨false′ : ∀ {x y : Bool} → x ≡ not y → x ∨ false ≡ not y
x∨false′ h = trans (∨-identityʳ _) h

x∨false″ : ∀ {x y : Bool} → x ≡ not y → x ≡ not (y ∨ false)
x∨false″ h = trans h (cong not (sym (∨-identityʳ _)))

-- 三分（由 AT）
tri : ∀ s t → AT s t → (lt s t ≡ true × lt t s ≡ false) ⊎ (s ≡ t) ⊎ (lt s t ≡ false × lt t s ≡ true)
tri s t (as , to) with caseEq (lt s t) | caseEq (lt t s)
... | inj₁ p | inj₁ q = ⊥-elim (as p q)
... | inj₁ p | inj₂ q = inj₁ (p , q)
... | inj₂ p | inj₁ q = inj₂ (inj₂ (p , q))
... | inj₂ p | inj₂ q = inj₂ (inj₁ (to p q))

irrefl : ∀ s → AT s s → lt s s ≡ false
irrefl s (as , _) with caseEq (lt s s)
... | inj₁ p = ⊥-elim (as p p)
... | inj₂ q = q

≺⇒eqT-false : ∀ s t → AT s t → lt s t ≡ true → eqT s t ≡ false
≺⇒eqT-false s t (as , _) h with caseEq (eqT s t)
... | inj₂ f = f
... | inj₁ g with eqT-sound s t g
...   | refl = ⊥-elim (as h h)
```

`core p q`：`p ≠ q` 时 `ltP′ p q ≡ not (ltP′ q p)`。

```agda
core : ∀ p q → eqP p q ≡ false → IH (size ⟨ p ⟩ + size ⟨ q ⟩) → Fl p q
-- φφ
core (phi a b) (phi c d) e ih with tri a c (ih a c (+-mono-<-≤ (sz-φˡ a b) (<⇒≤ (sz-φˡ c d))))
... | inj₁ (ac , ca) = φφ₁ ac ca ea (eqT-false-sym a c ea) (lin′ b ⟨ phi c d ⟩ (ih b ⟨ phi c d ⟩ (+-mono-<-≤ (sz-φʳ a b) (≤-refl {size ⟨ phi c d ⟩}))))
  where
    ea : eqT a c ≡ false
    ea = ≺⇒eqT-false a c (ih a c (+-mono-<-≤ (sz-φˡ a b) (<⇒≤ (sz-φˡ c d)))) ac
... | inj₂ (inj₂ (ac , ca)) = φφ₃ ac ca (eqT-false-sym c a ec) ec
                                  (lin″ d ⟨ phi a b ⟩ (ih d ⟨ phi a b ⟩ (subst (_< size ⟨ phi a b ⟩ + size ⟨ phi c d ⟩) (+-comm (size ⟨ phi a b ⟩) (size d)) (+-mono-≤-< (≤-refl {size ⟨ phi a b ⟩}) (sz-φʳ c d)))))
  where
    ec : eqT c a ≡ false
    ec = ≺⇒eqT-false c a (AT-sym a c (ih a c (+-mono-<-≤ (sz-φˡ a b) (<⇒≤ (sz-φˡ c d))))) ca
... | inj₂ (inj₁ refl) = φφ₂ (irrefl a (ih a a (+-mono-< (sz-φˡ a b) (sz-φˡ a d)))) (eqT-refl a)
                             (lin b d (ih b d (+-mono-< (sz-φʳ a b) (sz-φʳ a d))) (subst (λ z → z ∧ eqT b d ≡ false) (eqT-refl a) e))
-- φ 对 G′：(≺′11) 给的互否
core (phi a b) (psi κ d) e ih = Fl-sym (psi κ d) (phi a b) refl
core (phi a b) (Om c)    e ih = Fl-sym (Om c) (phi a b) refl
core (phi a b) I         e ih = Fl-sym I (phi a b) refl
core (psi π b) (phi c d) e ih = refl
core (Om a)    (phi c d) e ih = refl
core I         (phi c d) e ih = refl
-- ψψ
core (psi (ΩR a) b) (psi (ΩR c) d) e ih with caseEq (eqT a c)
... | inj₂ ea = ψψ₁ ea (eqT-false-sym a c ea) (lin ⟨ Om a ⟩ ⟨ Om c ⟩ (ih ⟨ Om a ⟩ ⟨ Om c ⟩ (+-mono-< (sz-ψΩ a b) (sz-ψΩ c d))) ea)
... | inj₁ ea with eqT-sound a c ea
...   | refl = ψψ₂ (eqT-refl a) (lt-refl-false (Om a))
                   (lin b d (ih b d (+-mono-< (sz-ψb (ΩR a) b) (sz-ψb (ΩR a) d))) (subst (λ z → z ∧ eqT b d ≡ false) (eqT-refl a) e))
core (psi IR b) (psi IR d) e ih = x∨false (lin b d (ih b d (+-mono-< (sz-ψb IR b) (sz-ψb IR d))) e)
core (psi IR b) (psi (ΩR c) d) e ih = x∨false′ (lin ⟨ psi IR b ⟩ ⟨ Om c ⟩ (ih ⟨ psi IR b ⟩ ⟨ Om c ⟩ (+-mono-≤-< (≤-refl {size ⟨ psi IR b ⟩}) (sz-ψΩ c d))) refl)
core (psi (ΩR a) b) (psi IR d) e ih = x∨false″ (lin ⟨ Om a ⟩ ⟨ psi IR d ⟩ (ih ⟨ Om a ⟩ ⟨ psi IR d ⟩ (+-mono-<-≤ (sz-ψΩ a b) (≤-refl {size ⟨ psi IR d ⟩}))) refl)
-- ψ 对 Ω′、I
core (psi (ΩR a) b) (Om c) e ih = Fl-sym (Om c) (psi (ΩR a) b) refl
core (psi IR b)     (Om c) e ih = Fl-sym (Om c) (psi IR b) refl
core (psi (ΩR a) b) I      e ih = Fl-sym I (psi (ΩR a) b) refl
core (psi IR b)     I      e ih = refl
core (Om a) (psi (ΩR z) d) e ih = refl
core (Om a) (psi IR d)     e ih = refl
core I (psi (ΩR z) d) e ih = refl
core I (psi IR d)     e ih = refl
-- Ω′Ω′、Ω′I、II
core (Om a) (Om c) e ih = lin a c (ih a c (+-mono-< (sz-Ω a) (sz-Ω c))) e
core (Om a) I      e ih = Fl-sym I (Om a) refl
core I      (Om c) e ih = refl
core I      I      e ih = ⊥-elim (true≢false e)
```

## 4. 组装：主元项对、和、强归纳

```agda
princ : ∀ p q → IH (size ⟨ p ⟩ + size ⟨ q ⟩) → ATP p q
princ p q ih with caseEq (eqP p q)
... | inj₁ e = (λ h _ → true≢false (trans (sym h) (trans (lt-unfold p q) (if-true e)))) , (λ _ _ → eqP-sound p q e)
... | inj₂ e = as , to
  where
    fl : ltP′ p q ≡ not (ltP′ q p)
    fl = core p q e ih
    u₁ : lt ⟨ p ⟩ ⟨ q ⟩ ≡ ltP′ p q
    u₁ = lt-unfold≠ p q e
    u₂ : lt ⟨ q ⟩ ⟨ p ⟩ ≡ ltP′ q p
    u₂ = lt-unfold≠ q p (eqP-false-sym p q e)
    chain : ∀ {v} → lt ⟨ q ⟩ ⟨ p ⟩ ≡ v → lt ⟨ p ⟩ ⟨ q ⟩ ≡ not v
    chain h = trans u₁ (trans fl (cong not (trans (sym u₂) h)))
    as : lt ⟨ p ⟩ ⟨ q ⟩ ≡ true → lt ⟨ q ⟩ ⟨ p ⟩ ≡ true → ⊥
    as h₁ h₂ = true≢false (trans (sym h₁) (chain h₂))
    to : lt ⟨ p ⟩ ⟨ q ⟩ ≡ false → lt ⟨ q ⟩ ⟨ p ⟩ ≡ false → p ≡ q
    to h₁ h₂ = ⊥-elim (true≢false (trans (sym (chain h₂)) h₁))

step : ∀ s t → IH (size s + size t) → AT s t
step s t ih = as , to
  where
    L = listAT (toList s) (toList t)
          (λ p q i j → princ p q (λ s′ t′ h → ih s′ t′ (<-≤-trans h (+-mono-≤ (∈-size′ s p i) (∈-size′ t q j)))))
    as : Asym s t
    as h₁ h₂ = proj₁ L (trans (sym (lt-list s t)) h₁) (trans (sym (lt-list t s)) h₂)
    to : Tot s t
    to h₁ h₂ = toList-inj s t (proj₂ L (trans (sym (lt-list s t)) h₁) (trans (sym (lt-list t s)) h₂))

IHn : ∀ n → IH n
IHn zero    s t ()
IHn (suc n) s t h = step s t (λ s′ t′ h′ → IHn n s′ t′ (<-≤-trans h′ (≤-pred h)))

AT-all : ∀ s t → AT s t
AT-all s t = IHn (suc (size s + size t)) s t ≤-refl
```

## 5. 导出：Lemma 2.4 的不可反、三分，及互否等式

```agda
lt-irrefl : ∀ s → lt s s ≡ false
lt-irrefl s = irrefl s (AT-all s s)

lt-asym : ∀ s t → lt s t ≡ true → lt t s ≡ false
lt-asym s t h with caseEq (lt t s)
... | inj₁ g = ⊥-elim (proj₁ (AT-all s t) h g)
... | inj₂ f = f

lt-tot : ∀ s t → lt s t ≡ false → lt t s ≡ false → s ≡ t
lt-tot s t = proj₂ (AT-all s t)

lt-lin : ∀ s t → eqT s t ≡ false → lt s t ≡ not (lt t s)
lt-lin s t = lin s t (AT-all s t)

lt-lin′ : ∀ s t → lt s t ≡ not (le t s)
lt-lin′ s t = lin′ s t (AT-all s t)

le-lin : ∀ s t → le t s ≡ not (lt s t)
le-lin s t = lin″ s t (AT-all s t)

≺-irrefl : ∀ {x} → ¬ (x ≺ x)
≺-irrefl {x} (lt! h) = true≢false (trans (sym h) (lt-irrefl x))

≺-asym : ∀ {x y} → x ≺ y → y ≺ x → ⊥
≺-asym {x} {y} (lt! h) (lt! g) = proj₁ (AT-all x y) h g

≺-trich : ∀ x y → x ≺ y ⊎ x ≡ y ⊎ y ≺ x
≺-trich x y with tri x y (AT-all x y)
... | inj₁ (p , _)        = inj₁ (lt! p)
... | inj₂ (inj₁ e)       = inj₂ (inj₁ e)
... | inj₂ (inj₂ (_ , q)) = inj₂ (inj₂ (lt! q))

-- ¬ (x ≺ y) 与 y ⪯ x 互换
¬≺⇒⪰ : ∀ x y → lt x y ≡ false → y ⪯ x
¬≺⇒⪰ x y h with caseEq (lt y x)
... | inj₁ g = le! (∨-introˡ g)
... | inj₂ f = le! (∨-introʳ (eqT-complete (sym (lt-tot x y h f))))

⪯⇒¬≺ : ∀ x y → y ⪯ x → lt x y ≡ false
⪯⇒¬≺ x y (le! h) with ∨-true h
... | inj₁ g = lt-asym y x g
... | inj₂ f with eqT-sound y x f
...   | refl = lt-irrefl x
```
