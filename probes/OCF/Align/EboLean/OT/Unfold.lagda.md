# ≺′ 的一步展开

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.Unfold` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

`ltP (suc n) p q` 的每个子调用都带燃料 `n`；当 `n ≥ 3·μP p q` 时（[OrderProps](OrderProps.lagda.md)），每个子调用都可以换成典范燃料的 `lt`／`le`。本文件把这件事做成一条等式 `lt-unfold`：主元项的比较**逐字**等于 (≺′3)–(≺′11) 的右边（以 `lt`、`le` 写出）。此后关于 `≺` 的所有推理都不再见到燃料。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.Unfold where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OrderProps

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤;
                                       m≤m+n; m≤n+m; m≤n⇒m≤1+n; +-comm; *-monoʳ-≤)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
```

## 1. 展开后的形状

```agda
ltP′ : PTm → PTm → Bool
-- (≺′3)
ltP′ (phi a b) (phi c d) = (lt a c ∧ lt b ⟨ phi c d ⟩) ∨ (eqT a c ∧ lt b d) ∨ (lt c a ∧ le ⟨ phi a b ⟩ d)
-- (≺′4)
ltP′ (phi a b) c         = lt a ⟨ c ⟩ ∧ lt b ⟨ c ⟩
-- (≺′5)
ltP′ (psi π b) (psi κ d) =
     (eqR π κ ∧ lt b d)
  ∨ (notI π ∧ notI κ ∧ lt (regTm π) (regTm κ))
  ∨ (isI π ∧ notI κ ∧ lt ⟨ psi π b ⟩ ⟨ regP κ ⟩)
  ∨ (notI π ∧ isI κ ∧ lt (regTm π) ⟨ psi κ d ⟩)
-- (≺′6)(≺′7)(≺′8)
ltP′ (psi (ΩR a) b) (Om c) = le ⟨ Om a ⟩ ⟨ Om c ⟩
ltP′ (psi IR b)     (Om c) = le ⟨ psi IR b ⟩ c
ltP′ (psi (ΩR a) b) I      = le ⟨ Om a ⟩ ⟨ I ⟩
ltP′ (psi IR b)     I      = true
ltP′ (psi π b) (phi c d)   = not (lt c ⟨ psi π b ⟩ ∧ lt d ⟨ psi π b ⟩)
-- (≺′9)(≺′10)
ltP′ (Om a) (Om c) = lt a c
ltP′ (Om a) I      = lt a ⟨ I ⟩
ltP′ (Om a) (phi c d)      = not (lt c ⟨ Om a ⟩ ∧ lt d ⟨ Om a ⟩)
ltP′ (Om a) (psi (ΩR z) d) = not (le ⟨ Om z ⟩ ⟨ Om a ⟩)
ltP′ (Om a) (psi IR d)     = not (le ⟨ psi IR d ⟩ a)
-- I
ltP′ I I              = false
ltP′ I (phi c d)      = not (lt c ⟨ I ⟩ ∧ lt d ⟨ I ⟩)
ltP′ I (psi (ΩR z) d) = not (le ⟨ Om z ⟩ ⟨ I ⟩)
ltP′ I (psi IR d)     = false
ltP′ I (Om c)         = not (lt c ⟨ I ⟩)
```

## 2. 各种子调用的燃料引理

`ltTP n t p`、`ltPT n p t` 按定义就是 `ltT (suc n) t ⟨ p ⟩`、`ltT (suc n) ⟨ p ⟩ t`。

```agda
sub : ∀ {n μ μ′} → μ′ ≤ μ → 3 * μ ≤ n → 3 * μ′ ≤ n
sub h k = ≤-trans (*-monoʳ-≤ 3 h) k

ltTP-fuel : ∀ n t p → 3 * μT t ⟨ p ⟩ ≤ n → ltTP n t p ≡ lt t ⟨ p ⟩
ltTP-fuel n t p h = ltT-fuel (suc n) t ⟨ p ⟩ (m≤n⇒m≤1+n h)

ltPT-fuel : ∀ n p t → 3 * μT ⟨ p ⟩ t ≤ n → ltPT n p t ≡ lt ⟨ p ⟩ t
ltPT-fuel n p t h = ltT-fuel (suc n) ⟨ p ⟩ t (m≤n⇒m≤1+n h)

lePT-fuel : ∀ n p t → 3 * μT ⟨ p ⟩ t ≤ n → lePT n p t ≡ le ⟨ p ⟩ t
lePT-fuel n p t h = cong (_∨ eqT ⟨ p ⟩ t) (ltPT-fuel n p t h)

leT-fuel : ∀ n s t → 3 * μT s t ≤ n → leT n s t ≡ le s t
leT-fuel n s t h = cong (_∨ eqT s t) (ltT-fuel n s t h)

-- p ≠ q 时 ltP n p q 就是 ltT (suc (suc n)) ⟨ p ⟩ ⟨ q ⟩
ltP-fuel : ∀ n p q → eqP p q ≡ false → 3 * μP p q ≤ n → ltP n p q ≡ lt ⟨ p ⟩ ⟨ q ⟩
ltP-fuel n p q e h =
  trans (sym (if-false {b = eqP p q} {x = ltL n [] []} e))
        (ltT-fuel (suc (suc n)) ⟨ p ⟩ ⟨ q ⟩ (m≤n⇒m≤1+n (m≤n⇒m≤1+n h)))

eqP-ψR : ∀ π b κ → eqP (psi π b) (regP κ) ≡ false
eqP-ψR π b (ΩR c) = refl
eqP-ψR π b IR     = refl
```

## 3. 逐子句展开

```agda
-- 交换律形式的测度界
swap≤ : ∀ x y z → x + y ≤ z → y + x ≤ z
swap≤ x y z h = subst (_≤ z) (+-comm x y) h

φG : ∀ n a b c → 3 * μP (phi a b) c ≤ n → (ltTP n a c ∧ ltTP n b c) ≡ (lt a ⟨ c ⟩ ∧ lt b ⟨ c ⟩)
φG n a b c h = cong₂ _∧_ (ltTP-fuel n a c (sub (+-monoˡ-≤ (lenP c) (m≤m+n (len a) (len b))) h))
                         (ltTP-fuel n b c (sub (+-monoˡ-≤ (lenP c) (m≤n+m (len b) (len a))) h))

Gφ : ∀ n g c d → 3 * μP g (phi c d) ≤ n
   → not (ltTP n c g ∧ ltTP n d g) ≡ not (lt c ⟨ g ⟩ ∧ lt d ⟨ g ⟩)
Gφ n g c d h = cong not (cong₂ _∧_
  (ltTP-fuel n c g (sub (swap≤ (lenP g) (len c) _ (+-monoʳ-≤ (lenP g) (m≤m+n (len c) (len d)))) h))
  (ltTP-fuel n d g (sub (swap≤ (lenP g) (len d) _ (+-monoʳ-≤ (lenP g) (m≤n+m (len d) (len c)))) h)))

ltP-unfold : ∀ n p q → 3 * μP p q ≤ n → ltP (suc n) p q ≡ ltP′ p q
ltP-unfold n (phi a b) (phi c d) h =
  cong₂ _∨_ (cong₂ _∧_ (ltT-fuel n a c (sub (+-mono-≤ (m≤m+n la lb) (m≤m+n lc ld)) h))
                       (ltTP-fuel n b (phi c d) (sub (+-monoˡ-≤ (lc + ld) (m≤n+m lb la)) h)))
   (cong₂ _∨_ (cong (eqT a c ∧_) (ltT-fuel n b d (sub (+-mono-≤ (m≤n+m lb la) (m≤n+m ld lc)) h)))
              (cong₂ _∧_ (ltT-fuel n c a (sub (swap≤ la lc _ (+-mono-≤ (m≤m+n la lb) (m≤m+n lc ld))) h))
                         (lePT-fuel n (phi a b) d (sub (+-monoʳ-≤ (la + lb) (m≤n+m ld lc)) h))))
  where la = len a ; lb = len b ; lc = len c ; ld = len d
ltP-unfold n (phi a b) (psi κ d) h = φG n a b (psi κ d) h
ltP-unfold n (phi a b) (Om c)    h = φG n a b (Om c) h
ltP-unfold n (phi a b) I         h = φG n a b I h
ltP-unfold n (psi π b) (psi κ d) h =
  cong₂ _∨_ (cong (eqR π κ ∧_) (ltT-fuel n b d (sub (+-mono-≤ (m≤n+m lb lπ) (m≤n+m ld lκ)) h)))
   (cong₂ _∨_ (cong (notI π ∧_) (cong (notI κ ∧_)
                 (ltT-fuel n (regTm π) (regTm κ)
                   (sub (subst (_≤ (lπ + lb) + (lκ + ld)) (cong₂ _+_ (lenR≡ π) (lenR≡ κ))
                                (+-mono-≤ (m≤m+n lπ lb) (m≤m+n lκ ld))) h))))
    (cong₂ _∨_ (cong (isI π ∧_) (cong (notI κ ∧_)
                 (ltP-fuel n (psi π b) (regP κ) (eqP-ψR π b κ)
                   (sub (subst (λ m → (lπ + lb) + m ≤ (lπ + lb) + (lκ + ld)) (lenR≡P κ)
                                (+-monoʳ-≤ (lπ + lb) (m≤m+n lκ ld))) h))))
               (cong (notI π ∧_) (cong (isI κ ∧_)
                 (ltTP-fuel n (regTm π) (psi κ d)
                   (sub (subst (λ m → m + (lκ + ld) ≤ (lπ + lb) + (lκ + ld)) (lenR≡ π)
                                (+-monoˡ-≤ (lκ + ld) (m≤m+n lπ lb))) h))))))
  where lπ = lenR π ; lκ = lenR κ ; lb = len b ; ld = len d
ltP-unfold n (psi (ΩR a) b) (Om c) h =
  leT-fuel n ⟨ Om a ⟩ ⟨ Om c ⟩ (sub (+-monoˡ-≤ (len c + 1) (m≤m+n (len a + 1) (len b))) h)
ltP-unfold n (psi IR b) (Om c) h =
  lePT-fuel n (psi IR b) c (sub (+-monoʳ-≤ (1 + len b) (m≤m+n (len c) 1)) h)
ltP-unfold n (psi (ΩR a) b) I h =
  leT-fuel n ⟨ Om a ⟩ ⟨ I ⟩ (sub (+-monoˡ-≤ 1 (m≤m+n (len a + 1) (len b))) h)
ltP-unfold n (psi IR b) I h = refl
ltP-unfold n (psi π b) (phi c d) h = Gφ n (psi π b) c d h
ltP-unfold n (Om a) (Om c) h = ltT-fuel n a c (sub (+-mono-≤ (m≤m+n (len a) 1) (m≤m+n (len c) 1)) h)
ltP-unfold n (Om a) I h = ltT-fuel n a ⟨ I ⟩ (sub (m≤m+n (len a + 1) 1) h)
ltP-unfold n (Om a) (phi c d) h = Gφ n (Om a) c d h
ltP-unfold n (Om a) (psi (ΩR z) d) h =
  cong not (leT-fuel n ⟨ Om z ⟩ ⟨ Om a ⟩
    (sub (swap≤ (len a + 1) (len z + 1) _ (+-monoʳ-≤ (len a + 1) (m≤m+n (len z + 1) (len d)))) h))
ltP-unfold n (Om a) (psi IR d) h =
  cong not (lePT-fuel n (psi IR d) a
    (sub (≤-trans (+-monoʳ-≤ (1 + len d) (m≤m+n (len a) 1)) (≤-reflexive (+-comm (1 + len d) (len a + 1)))) h))
ltP-unfold n I I h = refl
ltP-unfold n I (phi c d) h = Gφ n I c d h
ltP-unfold n I (psi (ΩR z) d) h =
  cong not (leT-fuel n ⟨ Om z ⟩ ⟨ I ⟩
    (sub (≤-trans (+-monoˡ-≤ 1 (m≤m+n (len z + 1) (len d))) (≤-reflexive (+-comm ((len z + 1) + len d) 1))) h))
ltP-unfold n I (psi IR d) h = refl
ltP-unfold n I (Om c) h = cong not (ltT-fuel n c ⟨ I ⟩ (sub (m≤n+m (len c + 1) 1) h))
```

## 4. 主定理

```agda
M≥ : ∀ p q → 3 * μP p q ≤ M p q
M≥ p q = 3μ≤8X (size ⟨ p ⟩ + size ⟨ q ⟩) (μP p q) (μP≤X p q)

lt-unfold : ∀ p q → lt ⟨ p ⟩ ⟨ q ⟩ ≡ (if eqP p q then false else ltP′ p q)
lt-unfold p q = trans (lt-prin p q)
                      (cong (λ x → if eqP p q then false else x) (ltP-unfold (M p q) p q (M≥ p q)))

-- p ≠ q（句法上）时
lt-unfold≠ : ∀ p q → eqP p q ≡ false → lt ⟨ p ⟩ ⟨ q ⟩ ≡ ltP′ p q
lt-unfold≠ p q e = trans (lt-unfold p q) (if-false e)

-- p = q 时 lt ⟨ p ⟩ ⟨ p ⟩ = false（主元项的不可反性是定义给的）
lt-refl-false : ∀ p → lt ⟨ p ⟩ ⟨ p ⟩ ≡ false
lt-refl-false p = trans (lt-unfold p p) (if-true (eqP-refl p))
```
