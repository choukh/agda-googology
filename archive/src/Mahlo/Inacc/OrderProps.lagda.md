# ≺′ 的燃料充分性与展开引理

[Order](Order.lagda.md) 里 `ltT n s t` 以燃料 n 递归。原文按 `length(a) + length(b)` 递归；(≺′11) 内联后每次递归调用都严格减小这个度量。本文件证：**燃料 ≥ 3·(len s + len t) 时结果稳定**，于是 `lt s t := ltT (fuel s t) s t` 可以按 (≺′1)–(≺′11) 逐条**展开**——这些展开引理是后面证 Lemma 2.4 与全部 `OTFacts` 的工具。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.OrderProps where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.BoolLemmas

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; m≤m+n; m≤n+m;
                                       +-comm; +-assoc; +-suc; n≤1+n; *-monoʳ-≤; +-cancelʳ-≤; m≤n⇒m≤1+n)
open import Data.List.Base using (List; []; _∷_)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
```

## 1. 度量

```agda
lenL′ : List PTm → ℕ
lenL′ []       = 0
lenL′ (p ∷ ps) = lenP p + lenL′ ps

μT : Tm → Tm → ℕ
μT s t = len s + len t

μL : List PTm → List PTm → ℕ
μL ps qs = lenL′ ps + lenL′ qs

μP : PTm → PTm → ℕ
μP p q = lenP p + lenP q

mutual
  len≥1 : ∀ s → 1 ≤ len s
  len≥1 zer         = s≤s z≤n
  len≥1 (zer ▹ p)   = lenP≥1 p
  len≥1 (a ▹ q ▹ p) = ≤-trans (len≥1 (a ▹ q)) (m≤m+n _ _)

  lenP≥1 : ∀ p → 1 ≤ lenP p
  lenP≥1 (phi a b) = ≤-trans (len≥1 a) (m≤m+n _ _)
  lenP≥1 (psi π b) = ≤-trans (lenR≥1 π) (m≤m+n _ _)
  lenP≥1 (Om a)    = ≤-trans (len≥1 a) (m≤m+n _ _)
  lenP≥1 I         = s≤s z≤n

  lenR≥1 : ∀ π → 1 ≤ lenR π
  lenR≥1 (ΩR a) = ≤-trans (len≥1 a) (m≤m+n _ _)
  lenR≥1 IR     = s≤s z≤n

-- toList 的分量长度之和 ≤ len
lenΣ : Tm → ℕ
lenΣ zer     = 0
lenΣ (a ▹ p) = lenΣ a + lenP p

toListAcc-len : ∀ a acc → lenL′ (toListAcc a acc) ≡ lenΣ a + lenL′ acc
toListAcc-len zer     acc = refl
toListAcc-len (a ▹ p) acc =
  trans (toListAcc-len a (p ∷ acc)) (trans (sym (+-assoc (lenΣ a) (lenP p) (lenL′ acc))) refl)

lenΣ≤len : ∀ s → lenΣ s ≤ len s
lenΣ≤len zer         = z≤n
lenΣ≤len (zer ▹ p)   = ≤-refl
lenΣ≤len (a ▹ q ▹ p) = +-monoˡ-≤ (lenP p) (lenΣ≤len (a ▹ q))

toList-len : ∀ s → lenL′ (toList s) ≤ len s
toList-len s = subst (λ m → m ≤ len s) (sym (trans (toListAcc-len s []) (+-comm (lenΣ s) 0))) (lenΣ≤len s)

lenR≡ : ∀ π → lenR π ≡ len (regTm π)
lenR≡ (ΩR a) = refl
lenR≡ IR     = refl

lenR≡P : ∀ π → lenR π ≡ lenP (regP π)
lenR≡P (ΩR a) = refl
lenR≡P IR     = refl
```

## 2. 稳定性

三个互相依赖的陈述，对 n 归纳：

- `ST n`：`3·μT s t ≤ n ⟹ ltT n s t ≡ ltT (suc n) s t`
- `SL n`：`3·μL ps qs ≤ n + 1 ⟹ ltL n ps qs ≡ ltL (suc n) ps qs`
- `SP n`：`3·μP p q ≤ n + 2 ⟹ ltP n p q ≡ ltP (suc n) p q`

ltP (suc n) 的每个子调用的度量 ≤ μP − 1，于是 `3·μsub ≤ n`，三个前提都满足。

```agda
open import Data.Nat.Properties using (*-suc; *-monoʳ-≤; +-cancelˡ-≤)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

ST SL SP : ℕ → Set
ST n = ∀ s t → 3 * μT s t ≤ n → ltT n s t ≡ ltT (suc n) s t
SL n = ∀ ps qs → 3 * μL ps qs ≤ n + 1 → ltL n ps qs ≡ ltL (suc n) ps qs
SP n = ∀ p q → 3 * μP p q ≤ n + 2 → ltP n p q ≡ ltP (suc n) p q

-- 3·μ ≤ n + 3，μ′ + 1 ≤ μ ⟹ 3·μ′ ≤ n
drop : ∀ {μ′ μ n} → suc μ′ ≤ μ → 3 * μ ≤ suc n + 2 → 3 * μ′ ≤ n
drop {μ′} {μ} {n} h₁ h₂ = +-cancelˡ-≤ 3 (3 * μ′) n step
  where
    step : 3 + 3 * μ′ ≤ 3 + n
    step = ≤-trans (subst (λ m → m ≤ 3 * μ) (*-suc 3 μ′) (*-monoʳ-≤ 3 h₁))
                   (subst (λ m → 3 * μ ≤ m) (cong suc (+-comm n 2)) h₂)

dropL : ∀ {μ′ μ n} → suc μ′ ≤ μ → 3 * μ ≤ suc n + 2 → 3 * μ′ ≤ n + 1
dropL h₁ h₂ = ≤-trans (drop h₁ h₂) (m≤m+n _ 1)

dropP : ∀ {μ′ μ n} → suc μ′ ≤ μ → 3 * μ ≤ suc n + 2 → 3 * μ′ ≤ n + 2
dropP h₁ h₂ = ≤-trans (drop h₁ h₂) (m≤m+n _ 2)

-- suc x ≤ x + y（1 ≤ y）；suc y ≤ x + y（1 ≤ x）
H1 : ∀ x {y} → 1 ≤ y → suc x ≤ x + y
H1 x {y} h = subst (λ m → m ≤ x + y) (+-comm x 1) (+-monoʳ-≤ x h)

H2 : ∀ {x} y → 1 ≤ x → suc y ≤ x + y
H2 y h = +-monoˡ-≤ y h

-- 一些重组恒等式
r1 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
r1 = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl
r2 : ∀ a b c d → (a + b) + (c + d) ≡ (b + d) + (a + c)
r2 = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (b :+ d) :+ (a :+ c)) refl
r3 : ∀ a b c → (a + b) + c ≡ (a + c) + b
r3 = solve 3 (λ a b c → (a :+ b) :+ c := (a :+ c) :+ b) refl
r4 : ∀ a b c → a + (b + c) ≡ (a + c) + b
r4 = solve 3 (λ a b c → a :+ (b :+ c) := (a :+ c) :+ b) refl
r5 : ∀ a b c → a + (b + c) ≡ (a + b) + c
r5 = solve 3 (λ a b c → a :+ (b :+ c) := (a :+ b) :+ c) refl
r6 : ∀ a b c → (a + b) + c ≡ (b + c) + a
r6 = solve 3 (λ a b c → (a :+ b) :+ c := (b :+ c) :+ a) refl
r7 : ∀ a b c → a + (b + c) ≡ (b + a) + c
r7 = solve 3 (λ a b c → a :+ (b :+ c) := (b :+ a) :+ c) refl
r8 : ∀ a b c → a + (b + c) ≡ (c + a) + b
r8 = solve 3 (λ a b c → a :+ (b :+ c) := (c :+ a) :+ b) refl
r9 : ∀ a b → (a + 1) + b ≡ (b + a) + 1
r9 = solve 2 (λ a b → (a :+ con 1) :+ b := (b :+ a) :+ con 1) refl
```

子调用度量的界（每条形如 `suc μsub ≤ μP p q`）：

```agda
-- 单元素表
lenL′1 : ∀ p → lenL′ (p ∷ []) ≡ lenP p
lenL′1 p = +-comm (lenP p) 0

-- μL (toList b) [q] ≤ len b + lenP q
μL-tp : ∀ b q → μL (toList b) (q ∷ []) ≤ len b + lenP q
μL-tp b q = +-mono-≤ (toList-len b) (subst (λ m → m ≤ lenP q) (sym (lenL′1 q)) ≤-refl)

μL-pt : ∀ p t → μL (p ∷ []) (toList t) ≤ lenP p + len t
μL-pt p t = +-mono-≤ (subst (λ m → m ≤ lenP p) (sym (lenL′1 p)) ≤-refl) (toList-len t)

-- 常用：x + 1 ≤ x + y 型的界，配合 ≤-trans
private
  ≤-both : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
  ≤-both = +-mono-≤
```

稳定性本体。每个 `ltP` 子句按子调用写；`h : 3 * μP p q ≤ suc n + 2`。

```agda
stab : ∀ n → ST n × SL n × SP n
stab zero = st0 , sl0 , sp0
  where
    st0 : ST zero
    st0 s t h = ⊥-elim (bad h)
      where
        bad : 3 * μT s t ≤ 0 → ⊥
        bad h′ with ≤-trans (*-monoʳ-≤ 3 (+-mono-≤ (len≥1 s) (len≥1 t))) h′
        ... | ()
    sl0 : SL zero
    sl0 []       []       h = refl
    sl0 []       (q ∷ qs) h = refl
    sl0 (p ∷ ps) []       h = refl
    sl0 (p ∷ ps) (q ∷ qs) h = ⊥-elim (bad h)
      where
        bad : 3 * μL (p ∷ ps) (q ∷ qs) ≤ 0 + 1 → ⊥
        bad h′ with ≤-trans (*-monoʳ-≤ 3 (+-mono-≤ (≤-trans (lenP≥1 p) (m≤m+n _ _)) (≤-trans (lenP≥1 q) (m≤m+n _ _)))) h′
        ... | s≤s ()
    sp0 : SP zero
    sp0 p q h = ⊥-elim (bad h)
      where
        bad : 3 * μP p q ≤ 0 + 2 → ⊥
        bad h′ with ≤-trans (*-monoʳ-≤ 3 (+-mono-≤ (lenP≥1 p) (lenP≥1 q))) h′
        ... | s≤s (s≤s ())
stab (suc n) with stab n
... | st , sl , sp = st′ , sl′ , sp′
  where
    st′ : ST (suc n)
    st′ s t h = sl (toList s) (toList t) (≤-trans (*-monoʳ-≤ 3 (+-mono-≤ (toList-len s) (toList-len t))) (subst (λ m → 3 * μT s t ≤ m) (+-comm 1 n) h))

    sl′ : SL (suc n)
    sl′ []       []       h = refl
    sl′ []       (q ∷ qs) h = refl
    sl′ (p ∷ ps) []       h = refl
    sl′ (p ∷ ps) (q ∷ qs) h with eqP p q
    ... | true  = sl ps qs (dropL μ< h′)
      where
        h′ : 3 * μL (p ∷ ps) (q ∷ qs) ≤ suc n + 2
        h′ = ≤-trans h (+-monoʳ-≤ (suc n) (s≤s z≤n))
        μ< : suc (μL ps qs) ≤ μL (p ∷ ps) (q ∷ qs)
        μ< = subst (λ m → suc (μL ps qs) ≤ m) (sym (r1 (lenP p) (lenL′ ps) (lenP q) (lenL′ qs)))
               (H2 (lenL′ ps + lenL′ qs) (≤-trans (lenP≥1 p) (m≤m+n _ _)))
    ... | false = sp p q (≤-trans (*-monoʳ-≤ 3 (+-mono-≤ (m≤m+n (lenP p) (lenL′ ps)) (m≤m+n (lenP q) (lenL′ qs))))
                                  (subst (λ m → 3 * μL (p ∷ ps) (q ∷ qs) ≤ m) (sym (+-suc n 1)) h))

    sp′ : SP (suc n)
    -- (≺′3)
    sp′ (phi a b) (phi c d) h =
      cong₂ _∨_ (cong₂ _∧_ (st a c (drop μ1 h)) (sl (toList b) (phi c d ∷ []) (dropL μ2 h)))
        (cong₂ _∨_ (cong (eqT a c ∧_) (st b d (drop μ3 h)))
                   (cong₂ _∧_ (st c a (drop μ4 h)) (cong (_∨ eqT ⟨ phi a b ⟩ d) (sl (phi a b ∷ []) (toList d) (dropL μ5 h)))))
      where
        la = len a ; lb = len b ; lc = len c ; ld = len d
        μ1 : suc (la + lc) ≤ (la + lb) + (lc + ld)
        μ1 = subst (λ m → suc (la + lc) ≤ m) (sym (r1 la lb lc ld)) (H1 (la + lc) (≤-trans (len≥1 b) (m≤m+n lb ld)))
        μ2 : suc (μL (toList b) (phi c d ∷ [])) ≤ (la + lb) + (lc + ld)
        μ2 = ≤-trans (s≤s (μL-tp b (phi c d))) (subst (λ m → suc (lb + (lc + ld)) ≤ m) (r5 la lb (lc + ld)) (H2 (lb + (lc + ld)) (len≥1 a)))
        μ3 : suc (lb + ld) ≤ (la + lb) + (lc + ld)
        μ3 = subst (λ m → suc (lb + ld) ≤ m) (sym (r2 la lb lc ld)) (H1 (lb + ld) (≤-trans (len≥1 a) (m≤m+n la lc)))
        μ4 : suc (lc + la) ≤ (la + lb) + (lc + ld)
        μ4 = subst (λ m → suc (lc + la) ≤ m) (trans (cong (_+ (lb + ld)) (+-comm lc la)) (sym (r1 la lb lc ld))) (H1 (lc + la) (≤-trans (len≥1 b) (m≤m+n lb ld)))
        μ5 : suc (μL (phi a b ∷ []) (toList d)) ≤ (la + lb) + (lc + ld)
        μ5 = ≤-trans (s≤s (μL-pt (phi a b) d)) (subst (λ m → suc ((la + lb) + ld) ≤ m) (sym (r4 (la + lb) lc ld)) (H1 ((la + lb) + ld) (len≥1 c)))

    -- (≺′4)：φ′_a b 对 G′
    sp′ (phi a b) (psi κ d) h = φG (psi κ d) h
      where
        φG : ∀ c → 3 * μP (phi a b) c ≤ suc n + 2
           → (ltTP n a c ∧ ltTP n b c) ≡ (ltTP (suc n) a c ∧ ltTP (suc n) b c)
        φG c h = cong₂ _∧_ (sl (toList a) (c ∷ []) (dropL μa h)) (sl (toList b) (c ∷ []) (dropL μb h))
          where
            μa : suc (μL (toList a) (c ∷ [])) ≤ (len a + len b) + lenP c
            μa = ≤-trans (s≤s (μL-tp a c)) (subst (λ m → suc (len a + lenP c) ≤ m) (sym (r3 (len a) (len b) (lenP c))) (H1 (len a + lenP c) (len≥1 b)))
            μb : suc (μL (toList b) (c ∷ [])) ≤ (len a + len b) + lenP c
            μb = ≤-trans (s≤s (μL-tp b c)) (subst (λ m → suc (len b + lenP c) ≤ m) (sym (r6 (len a) (len b) (lenP c))) (H1 (len b + lenP c) (len≥1 a)))
    sp′ (phi a b) (Om c) h = cong₂ _∧_ (sl (toList a) (Om c ∷ []) (dropL μa h)) (sl (toList b) (Om c ∷ []) (dropL μb h))
      where
        μa : suc (μL (toList a) (Om c ∷ [])) ≤ (len a + len b) + lenP (Om c)
        μa = ≤-trans (s≤s (μL-tp a (Om c))) (subst (λ m → suc (len a + lenP (Om c)) ≤ m) (sym (r3 (len a) (len b) (lenP (Om c)))) (H1 (len a + lenP (Om c)) (len≥1 b)))
        μb : suc (μL (toList b) (Om c ∷ [])) ≤ (len a + len b) + lenP (Om c)
        μb = ≤-trans (s≤s (μL-tp b (Om c))) (subst (λ m → suc (len b + lenP (Om c)) ≤ m) (sym (r6 (len a) (len b) (lenP (Om c)))) (H1 (len b + lenP (Om c)) (len≥1 a)))
    sp′ (phi a b) I h = cong₂ _∧_ (sl (toList a) (I ∷ []) (dropL μa h)) (sl (toList b) (I ∷ []) (dropL μb h))
      where
        μa : suc (μL (toList a) (I ∷ [])) ≤ (len a + len b) + 1
        μa = ≤-trans (s≤s (μL-tp a I)) (subst (λ m → suc (len a + 1) ≤ m) (sym (r3 (len a) (len b) 1)) (H1 (len a + 1) (len≥1 b)))
        μb : suc (μL (toList b) (I ∷ [])) ≤ (len a + len b) + 1
        μb = ≤-trans (s≤s (μL-tp b I)) (subst (λ m → suc (len b + 1) ≤ m) (sym (r6 (len a) (len b) 1)) (H1 (len b + 1) (len≥1 a)))
    -- (≺′5)
    sp′ (psi π b) (psi κ d) h =
      cong₂ _∨_ (cong (eqR π κ ∧_) (st b d (drop μ1 h)))
        (cong₂ _∨_ (cong (notI π ∧_) (cong (notI κ ∧_) (st (regTm π) (regTm κ) (drop μ2 h))))
          (cong₂ _∨_ (cong (isI π ∧_) (cong (notI κ ∧_) (sp (psi π b) (regP κ) (dropP μ3 h))))
                     (cong (notI π ∧_) (cong (isI κ ∧_) (sl (toList (regTm π)) (psi κ d ∷ []) (dropL μ4 h))))))
      where
        lπ = lenR π ; lκ = lenR κ ; lb = len b ; ld = len d
        μ1 : suc (lb + ld) ≤ (lπ + lb) + (lκ + ld)
        μ1 = subst (λ m → suc (lb + ld) ≤ m) (sym (r2 lπ lb lκ ld)) (H1 (lb + ld) (≤-trans (lenR≥1 π) (m≤m+n lπ lκ)))
        μ2 : suc (μT (regTm π) (regTm κ)) ≤ (lπ + lb) + (lκ + ld)
        μ2 = subst (λ m → suc m ≤ (lπ + lb) + (lκ + ld)) (cong₂ _+_ (lenR≡ π) (lenR≡ κ))
               (subst (λ m → suc (lπ + lκ) ≤ m) (sym (r1 lπ lb lκ ld)) (H1 (lπ + lκ) (≤-trans (len≥1 b) (m≤m+n lb ld))))
        μ3 : suc (μP (psi π b) (regP κ)) ≤ (lπ + lb) + (lκ + ld)
        μ3 = subst (λ m → suc ((lπ + lb) + m) ≤ (lπ + lb) + (lκ + ld)) (lenR≡P κ)
               (subst (λ m → suc ((lπ + lb) + lκ) ≤ m) (sym (r5 (lπ + lb) lκ ld)) (H1 ((lπ + lb) + lκ) (len≥1 d)))
        μ4 : suc (μL (toList (regTm π)) (psi κ d ∷ [])) ≤ (lπ + lb) + (lκ + ld)
        μ4 = ≤-trans (s≤s (μL-tp (regTm π) (psi κ d)))
               (subst (λ m → suc (m + (lκ + ld)) ≤ (lπ + lb) + (lκ + ld)) (lenR≡ π)
                 (subst (λ m → suc (lπ + (lκ + ld)) ≤ m) (sym (r3 lπ lb (lκ + ld))) (H1 (lπ + (lκ + ld)) (len≥1 b))))
    -- (≺′6)(≺′7)(≺′8)
    sp′ (psi (ΩR a) b) (Om c) h = cong (_∨ eqT ⟨ Om a ⟩ ⟨ Om c ⟩) (st ⟨ Om a ⟩ ⟨ Om c ⟩ (drop μ h))
      where
        μ : suc ((len a + 1) + (len c + 1)) ≤ ((len a + 1) + len b) + (len c + 1)
        μ = subst (λ m → suc ((len a + 1) + (len c + 1)) ≤ m) (sym (r3 (len a + 1) (len b) (len c + 1))) (H1 _ (len≥1 b))
    sp′ (psi IR b) (Om c) h = cong (_∨ eqT ⟨ psi IR b ⟩ c) (sl (psi IR b ∷ []) (toList c) (dropL μ h))
      where
        μ : suc (μL (psi IR b ∷ []) (toList c)) ≤ (1 + len b) + (len c + 1)
        μ = ≤-trans (s≤s (μL-pt (psi IR b) c)) (subst (λ m → suc ((1 + len b) + len c) ≤ m) (sym (r5 (1 + len b) (len c) 1)) (H1 _ ≤-refl))
    sp′ (psi (ΩR a) b) I h = cong (_∨ eqT ⟨ Om a ⟩ ⟨ I ⟩) (st ⟨ Om a ⟩ ⟨ I ⟩ (drop μ h))
      where
        μ : suc ((len a + 1) + 1) ≤ ((len a + 1) + len b) + 1
        μ = subst (λ m → suc ((len a + 1) + 1) ≤ m) (sym (r3 (len a + 1) (len b) 1)) (H1 _ (len≥1 b))
    sp′ (psi IR b) I h = refl
    -- (≺′11) ψ 对 φ
    sp′ (psi π b) (phi c d) h = cong not (cong₂ _∧_ (sl (toList c) (psi π b ∷ []) (dropL μc h)) (sl (toList d) (psi π b ∷ []) (dropL μd h)))
      where
        P = lenR π + len b
        μc : suc (μL (toList c) (psi π b ∷ [])) ≤ P + (len c + len d)
        μc = ≤-trans (s≤s (μL-tp c (psi π b))) (subst (λ m → suc (len c + P) ≤ m) (sym (r7 P (len c) (len d))) (H1 _ (len≥1 d)))
        μd : suc (μL (toList d) (psi π b ∷ [])) ≤ P + (len c + len d)
        μd = ≤-trans (s≤s (μL-tp d (psi π b))) (subst (λ m → suc (len d + P) ≤ m) (sym (r8 P (len c) (len d))) (H1 _ (len≥1 c)))
    -- (≺′9)(≺′10)
    sp′ (Om a) (Om c) h = st a c (drop μ h)
      where
        μ : suc (len a + len c) ≤ (len a + 1) + (len c + 1)
        μ = subst (λ m → suc (len a + len c) ≤ m) (sym (r1 (len a) 1 (len c) 1)) (H1 _ (s≤s z≤n))
    sp′ (Om a) I h = st a ⟨ I ⟩ (drop (H1 (len a + 1) ≤-refl) h)
    -- (≺′11) Ω′ 对 φ、ψ
    sp′ (Om a) (phi c d) h = cong not (cong₂ _∧_ (sl (toList c) (Om a ∷ []) (dropL μc h)) (sl (toList d) (Om a ∷ []) (dropL μd h)))
      where
        μc : suc (μL (toList c) (Om a ∷ [])) ≤ (len a + 1) + (len c + len d)
        μc = ≤-trans (s≤s (μL-tp c (Om a))) (subst (λ m → suc (len c + (len a + 1)) ≤ m) (sym (r7 (len a + 1) (len c) (len d))) (H1 _ (len≥1 d)))
        μd : suc (μL (toList d) (Om a ∷ [])) ≤ (len a + 1) + (len c + len d)
        μd = ≤-trans (s≤s (μL-tp d (Om a))) (subst (λ m → suc (len d + (len a + 1)) ≤ m) (sym (r8 (len a + 1) (len c) (len d))) (H1 _ (len≥1 c)))
    sp′ (Om a) (psi (ΩR z) d) h = cong not (cong (_∨ eqT ⟨ Om z ⟩ ⟨ Om a ⟩) (st ⟨ Om z ⟩ ⟨ Om a ⟩ (drop μ h)))
      where
        μ : suc ((len z + 1) + (len a + 1)) ≤ (len a + 1) + ((len z + 1) + len d)
        μ = subst (λ m → suc ((len z + 1) + (len a + 1)) ≤ m) (sym (r7 (len a + 1) (len z + 1) (len d))) (H1 _ (len≥1 d))
    sp′ (Om a) (psi IR d) h = cong not (cong (_∨ eqT ⟨ psi IR d ⟩ a) (sl (psi IR d ∷ []) (toList a) (dropL μ h)))
      where
        μ : suc (μL (psi IR d ∷ []) (toList a)) ≤ (len a + 1) + (1 + len d)
        μ = ≤-trans (s≤s (μL-pt (psi IR d) a)) (subst (λ m → suc ((1 + len d) + len a) ≤ m) (sym (r9 (len a) (1 + len d))) (H1 _ ≤-refl))
    -- I 对各项
    sp′ I I h = refl
    sp′ I (phi c d) h = cong not (cong₂ _∧_ (sl (toList c) (I ∷ []) (dropL μc h)) (sl (toList d) (I ∷ []) (dropL μd h)))
      where
        μc : suc (μL (toList c) (I ∷ [])) ≤ 1 + (len c + len d)
        μc = ≤-trans (s≤s (μL-tp c I)) (subst (λ m → suc (len c + 1) ≤ m) (sym (r7 1 (len c) (len d))) (H1 _ (len≥1 d)))
        μd : suc (μL (toList d) (I ∷ [])) ≤ 1 + (len c + len d)
        μd = ≤-trans (s≤s (μL-tp d I)) (subst (λ m → suc (len d + 1) ≤ m) (sym (r8 1 (len c) (len d))) (H1 _ (len≥1 c)))
    sp′ I (psi (ΩR z) d) h = cong not (cong (_∨ eqT ⟨ Om z ⟩ ⟨ I ⟩) (st ⟨ Om z ⟩ ⟨ I ⟩ (drop μ h)))
      where
        μ : suc ((len z + 1) + 1) ≤ 1 + ((len z + 1) + len d)
        μ = subst (λ m → suc ((len z + 1) + 1) ≤ m) (sym (r7 1 (len z + 1) (len d))) (H1 _ (len≥1 d))
    sp′ I (psi IR d) h = refl
    sp′ I (Om c) h = cong not (st c ⟨ I ⟩ (drop μ h))
      where
        μ : suc (len c + 1) ≤ 1 + (len c + 1)
        μ = subst (λ m → suc (len c + 1) ≤ m) (+-comm (len c + 1) 1) (H1 _ ≤-refl)
```

## 3. 推论：燃料够就稳定；`lt` 的展开

```agda
open import Data.Nat.Base using (_≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤⇒≤′; ≤′⇒≤; ≤-total; +-identityʳ; *-monoˡ-≤; ≤-reflexive; m≤n⇒m≤1+n; n≤1+n)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

stableT′ : ∀ {n m} s t → 3 * μT s t ≤ n → n ≤′ m → ltT n s t ≡ ltT m s t
stableT′ s t h ≤′-refl      = refl
stableT′ s t h (≤′-step le) = trans (stableT′ s t h le) (proj₁ (stab _) s t (≤-trans h (≤′⇒≤ le)))

stableP′ : ∀ {n m} p q → 3 * μP p q ≤ n + 2 → n ≤′ m → ltP n p q ≡ ltP m p q
stableP′ p q h ≤′-refl      = refl
stableP′ p q h (≤′-step le) = trans (stableP′ p q h le) (proj₂ (proj₂ (stab _)) p q (≤-trans h (+-monoˡ-≤ 2 (≤′⇒≤ le))))

stable-eq : ∀ n m s t → 3 * μT s t ≤ n → 3 * μT s t ≤ m → ltT n s t ≡ ltT m s t
stable-eq n m s t hn hm with ≤-total n m
... | inj₁ n≤m = stableT′ s t hn (≤⇒≤′ n≤m)
... | inj₂ m≤n = sym (stableT′ s t hm (≤⇒≤′ m≤n))

stableP-eq : ∀ n m p q → 3 * μP p q ≤ n + 2 → 3 * μP p q ≤ m + 2 → ltP n p q ≡ ltP m p q
stableP-eq n m p q hn hm with ≤-total n m
... | inj₁ n≤m = stableP′ p q hn (≤⇒≤′ n≤m)
... | inj₂ m≤n = sym (stableP′ p q hm (≤⇒≤′ m≤n))

-- len ≤ size
mutual
  len≤size : ∀ s → len s ≤ size s
  len≤size zer         = ≤-refl
  len≤size (zer ▹ p)   = ≤-trans (lenP≤sizeP p) (n≤1+n _)
  len≤size (a ▹ q ▹ p) = +-mono-≤ (len≤size (a ▹ q)) (lenP≤sizeP p)

  lenP≤sizeP : ∀ p → lenP p ≤ sizeP p
  lenP≤sizeP (phi a b) = m≤n⇒m≤1+n (+-mono-≤ (len≤size a) (len≤size b))
  lenP≤sizeP (psi π b) = m≤n⇒m≤1+n (+-mono-≤ (lenR≤sizeR π) (len≤size b))
  lenP≤sizeP (Om a)    = ≤-trans (+-monoˡ-≤ 1 (len≤size a)) (≤-reflexive (+-comm (size a) 1))
  lenP≤sizeP I         = ≤-refl

  lenR≤sizeR : ∀ π → lenR π ≤ sizeR π
  lenR≤sizeR (ΩR a) = ≤-trans (+-monoˡ-≤ 1 (len≤size a)) (≤-reflexive (+-comm (size a) 1))
  lenR≤sizeR IR     = ≤-refl

3μ≤8X : ∀ X μ → μ ≤ X → 3 * μ ≤ 13 + 8 * X
3μ≤8X X μ h = ≤-trans (*-monoʳ-≤ 3 h) (≤-trans (*-monoˡ-≤ X (s≤s (s≤s (s≤s (z≤n {5}))))) (m≤n+m (8 * X) 13))

fuel-ok : ∀ s t → 3 * μT s t ≤ fuel s t
fuel-ok s t = ≤-trans (3μ≤8X (size s + size t) (μT s t) (+-mono-≤ (len≤size s) (len≤size t)))
                      (subst (λ m → 13 + 8 * (size s + size t) ≤ m) (+-comm 16 (8 * (size s + size t))) (+-monoˡ-≤ (8 * (size s + size t)) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n {3}))))))))))))))))

-- 燃料够 ⟹ 等于 lt
ltT-fuel : ∀ n s t → 3 * μT s t ≤ n → ltT n s t ≡ lt s t
ltT-fuel n s t h = stable-eq n (fuel s t) s t h (fuel-ok s t)
```

主元项比较的展开：`lt ⟨p⟩ ⟨q⟩ = if eqP p q then false else ltP (suc M) p q`，其中 `M p q = 13 + 8·(size ⟨p⟩ + size ⟨q⟩)`；ltP 里每个子调用的度量 ≤ μP p q ≤ M，于是子调用都可换成 `lt`。

```agda
M : PTm → PTm → ℕ
M p q = 13 + 8 * (size ⟨ p ⟩ + size ⟨ q ⟩)

fuel-prin : ∀ p q → fuel ⟨ p ⟩ ⟨ q ⟩ ≡ suc (suc (suc (M p q)))
fuel-prin p q = +-comm (8 * (size ⟨ p ⟩ + size ⟨ q ⟩)) 16

lt-prin : ∀ p q → lt ⟨ p ⟩ ⟨ q ⟩ ≡ (if eqP p q then false else ltP (suc (M p q)) p q)
lt-prin p q = cong (λ m → ltT m ⟨ p ⟩ ⟨ q ⟩) (fuel-prin p q)

-- 子调用的燃料条件
μP≤X : ∀ p q → μP p q ≤ size ⟨ p ⟩ + size ⟨ q ⟩
μP≤X p q = +-mono-≤ (≤-trans (lenP≤sizeP p) (n≤1+n _)) (≤-trans (lenP≤sizeP q) (n≤1+n _))

subT : ∀ p q s t → μT s t ≤ μP p q → 3 * μT s t ≤ M p q
subT p q s t h = 3μ≤8X (size ⟨ p ⟩ + size ⟨ q ⟩) (μT s t) (≤-trans h (μP≤X p q))

subT′ : ∀ p q s t → μT s t ≤ μP p q → 3 * μT s t ≤ suc (M p q)
subT′ p q s t h = m≤n⇒m≤1+n (subT p q s t h)

subP : ∀ p q p′ q′ → μP p′ q′ ≤ μP p q → 3 * μP p′ q′ ≤ M p q + 2
subP p q p′ q′ h = ≤-trans (3μ≤8X (size ⟨ p ⟩ + size ⟨ q ⟩) (μP p′ q′) (≤-trans h (μP≤X p q))) (m≤m+n (M p q) 2)

-- 列表层：lt s t = ltLx (toList s) (toList t)
ltLx : List PTm → List PTm → Bool
ltLx []       []       = false
ltLx []       (_ ∷ _)  = true
ltLx (_ ∷ _)  []       = false
ltLx (p ∷ ps) (q ∷ qs) = if eqP p q then ltLx ps qs else lt ⟨ p ⟩ ⟨ q ⟩

ltL-x : ∀ m ps qs → 3 * μL ps qs ≤ m → ltL m ps qs ≡ ltLx ps qs
ltL-x m       []       []       h = refl
ltL-x m       []       (q ∷ qs) h = refl
ltL-x m       (p ∷ ps) []       h = refl
ltL-x zero    (p ∷ ps) (q ∷ qs) h = ⊥-elim (bad h)
  where
    bad : 3 * μL (p ∷ ps) (q ∷ qs) ≤ 0 → ⊥
    bad h′ with ≤-trans (*-monoʳ-≤ 3 (+-mono-≤ (≤-trans (lenP≥1 p) (m≤m+n _ _)) (≤-trans (lenP≥1 q) (m≤m+n _ _)))) h′
    ... | ()
ltL-x (suc m) (p ∷ ps) (q ∷ qs) h with eqP p q in e
... | true  = ltL-x m ps qs (drop μ< (≤-trans h (m≤m+n (suc m) 2)))
  where
    μ< : suc (μL ps qs) ≤ μL (p ∷ ps) (q ∷ qs)
    μ< = subst (λ k → suc (μL ps qs) ≤ k) (sym (r1 (lenP p) (lenL′ ps) (lenP q) (lenL′ qs)))
           (H2 (lenL′ ps + lenL′ qs) (≤-trans (lenP≥1 p) (m≤m+n _ _)))
... | false = trans (stableP-eq m (suc (M p q)) p q hm hM) (sym (trans (lt-prin p q) (if-false e)))
  where
    hm : 3 * μP p q ≤ m + 2
    hm = ≤-trans (*-monoʳ-≤ 3 (+-mono-≤ (m≤m+n (lenP p) (lenL′ ps)) (m≤m+n (lenP q) (lenL′ qs)))) (≤-trans h (subst (suc m ≤_) (+-comm 2 m) (s≤s (n≤1+n m))))
    hM : 3 * μP p q ≤ suc (M p q) + 2
    hM = ≤-trans (subP p q p q ≤-refl) (n≤1+n (M p q + 2))

lt-list : ∀ s t → lt s t ≡ ltLx (toList s) (toList t)
lt-list s t = trans (cong (λ m → ltT m s t) fuel-suc) (ltL-x _ (toList s) (toList t) hL)
  where
    fuel-suc : fuel s t ≡ suc (15 + 8 * (size s + size t))
    fuel-suc = +-comm (8 * (size s + size t)) 16
    hL : 3 * μL (toList s) (toList t) ≤ 15 + 8 * (size s + size t)
    hL = ≤-trans (*-monoʳ-≤ 3 (+-mono-≤ (toList-len s) (toList-len t)))
                 (≤-trans (3μ≤8X (size s + size t) (μT s t) (+-mono-≤ (len≤size s) (len≤size t))) (+-monoˡ-≤ (8 * (size s + size t)) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (z≤n {2}))))))))))))))))
```

