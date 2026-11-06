# 子项小于整项

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.Subterm` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Remark 2.12 (h) 的 φ／Ω′ 部分（`b ⪯ φ′_b c`，`c ⪯ φ′_b c`，`b ⪯ Ω′_b`），以及 ψ_{Ω′_a} b 的层 `a ≺ ψ_{Ω′_a} b`。
在全部 T′ 上成立，不需要 OT。

方法：定义「结构下降」`s ◁ t`——沿 φ 的两个参数、Ω′ 的参数、ψ 的层、和的**首分量**下降；
证 `s ◁ t ⟹ s ≺ t`，对 `size t` 外层强归纳、`size s` 内层强归纳，每一步只看 `s` 的首分量对 `t` 的主元怎么比。
注意 ψ_π b 的参数 b 不在下降关系里：b ≺ ψ_π b 一般不成立（ψ 是坍缩）。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module OCF.Align.EboLean.OT.Subterm where

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OrderProps using (ltLx; lt-list)
open import OCF.Align.EboLean.OT.Unfold
open import OCF.Align.EboLean.OT.Linear
open import OCF.Align.EboLean.OT.Trans
open import OCF.Align.EboLean.OT.Lex

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; <-≤-trans; ≤-<-trans; <⇒≤; <-irrefl; m≤m+n; m≤n+m; n≤1+n; m≤n⇒m≤1+n; m<m+n)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
```

## 1. 下降关系

```agda
data _◁_ : Tm → Tm → Set
_⊴_ : Tm → Tm → Set
s ⊴ t = (s ◁ t) ⊎ (s ≡ t)

data _◁_ where
  φˡ  : ∀ {s b c} → s ⊴ b → s ◁ ⟨ phi b c ⟩
  φʳ  : ∀ {s b c} → s ⊴ c → s ◁ ⟨ phi b c ⟩
  Ωa  : ∀ {s a}   → s ⊴ a → s ◁ ⟨ Om a ⟩
  ψl  : ∀ {s a b} → s ⊴ a → s ◁ ⟨ psi (ΩR a) b ⟩
  hd◁ : ∀ {s a q} → NZ a → s ◁ ⟨ hd (a ▹ q) ⟩ → s ◁ (a ▹ q)

-- 传递
◁-trans : ∀ {x s u} → x ◁ s → s ◁ u → x ◁ u
◁⊴-trans : ∀ {x s u} → x ◁ s → s ⊴ u → x ◁ u
◁⊴-trans d (inj₁ e)    = ◁-trans d e
◁⊴-trans d (inj₂ refl) = d
◁-trans d (φˡ e)     = φˡ (inj₁ (◁⊴-trans d e))
◁-trans d (φʳ e)     = φʳ (inj₁ (◁⊴-trans d e))
◁-trans d (Ωa e)     = Ωa (inj₁ (◁⊴-trans d e))
◁-trans d (ψl e)     = ψl (inj₁ (◁⊴-trans d e))
◁-trans d (hd◁ nz e) = hd◁ nz (◁-trans d e)

-- 首分量
hd-size≤ : ∀ a → NZ a → size ⟨ hd a ⟩ ≤ size a
hd-size≤ (zer ▹ p)   _ = ≤-refl
hd-size≤ (a ▹ q ▹ p) _ = ≤-trans (hd-size≤ (a ▹ q) tt) (m≤m+n (size (a ▹ q)) (sizeP p))

hd-size< : ∀ a q → NZ a → size ⟨ hd (a ▹ q) ⟩ < size (a ▹ q)
hd-size< (a ▹ q′) q _ = ≤-<-trans (hd-size≤ (a ▹ q′) tt) (m<m+n (size (a ▹ q′)) (sizeP≥1 q))
  where
    sizeP≥1 : ∀ p → 1 ≤ sizeP p
    sizeP≥1 (phi _ _) = s≤s z≤n
    sizeP≥1 (psi _ _) = s≤s z≤n
    sizeP≥1 (Om _)    = s≤s z≤n
    sizeP≥1 I         = s≤s z≤n

hd-le : ∀ a → NZ a → le ⟨ hd a ⟩ a ≡ true
hd-le (zer ▹ p)   _ = leʳ ⟨ p ⟩ ⟨ p ⟩ (eqT-refl ⟨ p ⟩)
hd-le (a ▹ q ▹ p) _ = leˡ ⟨ hd (a ▹ q) ⟩ (a ▹ q ▹ p) (lt≡ (⪯≺-trans {⟨ hd (a ▹ q) ⟩} {a ▹ q} {a ▹ q ▹ p} (le! (hd-le (a ▹ q) tt)) (lt! (≺-▹ (a ▹ q) p))))

hd-lt : ∀ a q → NZ a → lt ⟨ hd (a ▹ q) ⟩ (a ▹ q) ≡ true
hd-lt (a ▹ q′) q _ = lt≡ (⪯≺-trans {⟨ hd (a ▹ q′) ⟩} {a ▹ q′} {a ▹ q′ ▹ q} (le! (hd-le (a ▹ q′) tt)) (lt! (≺-▹ (a ▹ q′) q)))

-- toList s = hd s ∷ …
toList-hd : ∀ a → NZ a → ∃ λ rest → toList a ≡ hd a ∷ rest
toList-hd (zer ▹ p)   _ = [] , refl
toList-hd (a ▹ q ▹ p) _ with toList-hd (a ▹ q) tt
... | rest , eq = rest ++ p ∷ [] , trans (toList-▹ (a ▹ q) p) (cong (_++ p ∷ []) eq)

-- 首分量 ≺ p ⟹ 整项 ≺ ⟨ p ⟩
hd-lt⟨⟩ : ∀ s p → NZ s → lt ⟨ hd s ⟩ ⟨ p ⟩ ≡ true → lt s ⟨ p ⟩ ≡ true
hd-lt⟨⟩ s p nz h with toList-hd s nz
... | rest , eq = trans (lt-list s ⟨ p ⟩) (subst (λ l → ltLx l (p ∷ []) ≡ true) (sym eq) (ltLx-sing⁻ (hd s) rest p [] h))

-- 提升：x ◁ ⟨ hd s ⟩ ⟹ x ◁ s
hd-lift : ∀ s → NZ s → ∀ {x} → x ◁ ⟨ hd s ⟩ → x ◁ s
hd-lift (zer ▹ p)   _ d = d
hd-lift (a ▹ q ▹ p) _ d = hd◁ tt d

-- 大小
◁-size : ∀ {s t} → s ◁ t → size s < size t
⊴-size : ∀ {s t} → s ⊴ t → size s ≤ size t
⊴-size (inj₁ d)    = <⇒≤ (◁-size d)
⊴-size (inj₂ refl) = ≤-refl
◁-size (φˡ {s} {b} {c} e) = ≤-<-trans (⊴-size e) (sz-φˡ b c)
◁-size (φʳ {s} {b} {c} e) = ≤-<-trans (⊴-size e) (sz-φʳ b c)
◁-size (Ωa {s} {a} e)     = ≤-<-trans (⊴-size e) (sz-Ω a)
◁-size (ψl {s} {a} {b} e) = ≤-<-trans (⊴-size e) (sz-ψa a b)
◁-size (hd◁ {s} {a} {q} nz d) = <-≤-trans (◁-size d) (<⇒≤ (hd-size< a q nz))
```

## 2. 主元项对主元项的四种情形

`q₀` 是 `s` 的首分量；已知 `⟨ q₀ ⟩ ⪯ u`（`u` 是 `t` 的相应参数），`⟨ q₀ ⟩` 的下降项都 ≺ `⟨ q₀ ⟩`（外层归纳），`⟨ q₀ ⟩` 的下降项都 ≺ `t`（内层归纳）。

```agda
neq-size : ∀ p q → size ⟨ p ⟩ < size ⟨ q ⟩ → eqP p q ≡ false
neq-size p q h with caseEq (eqP p q)
... | inj₂ e = e
... | inj₁ e with eqP-sound p q e
...   | refl = ⊥-elim (<-irrefl refl h)

-- x ◁ ⟨ q₀ ⟩ 且 ⟨ q₀ ⟩ ⪯ u ⟹ x ≺ u
via-hd : ∀ x q₀ u → lt x ⟨ q₀ ⟩ ≡ true → le ⟨ q₀ ⟩ u ≡ true → lt x u ≡ true
via-hd x q₀ u h l = lt≡ (≺⪯-trans {x} {⟨ q₀ ⟩} {u} (lt! h) (le! l))

φˡ-case : ∀ b c q₀ → le ⟨ q₀ ⟩ b ≡ true → size ⟨ q₀ ⟩ < size ⟨ phi b c ⟩
        → (∀ x → x ◁ ⟨ q₀ ⟩ → lt x ⟨ q₀ ⟩ ≡ true)
        → (∀ y → y ◁ ⟨ q₀ ⟩ → lt y ⟨ phi b c ⟩ ≡ true)
        → lt ⟨ q₀ ⟩ ⟨ phi b c ⟩ ≡ true
φˡ-case b c (phi x y) l sz ihq ihy =
  unf⁻ (phi x y) (phi b c) (neq-size (phi x y) (phi b c) sz)
       (∨ˡ (lt x b ∧ lt y ⟨ phi b c ⟩) _ (∧ⁱ (lt x b) (lt y ⟨ phi b c ⟩) (via-hd x (phi x y) b (ihq x (φˡ (inj₂ refl))) l) (ihy y (φʳ (inj₂ refl)))))
φˡ-case b c (psi π d) l sz ihq ihy = trans (Gφ-lt (psi π d) b c refl) (not-≡false (cong (_∧ lt c ⟨ psi π d ⟩) (⪯⇒¬≺ b ⟨ psi π d ⟩ (le! l))))
φˡ-case b c (Om a)    l sz ihq ihy = trans (Gφ-lt (Om a) b c refl)    (not-≡false (cong (_∧ lt c ⟨ Om a ⟩)    (⪯⇒¬≺ b ⟨ Om a ⟩ (le! l))))
φˡ-case b c I         l sz ihq ihy = trans (Gφ-lt I b c refl)         (not-≡false (cong (_∧ lt c ⟨ I ⟩)         (⪯⇒¬≺ b ⟨ I ⟩ (le! l))))

φʳ-case : ∀ b c q₀ → le ⟨ q₀ ⟩ c ≡ true → size ⟨ q₀ ⟩ < size ⟨ phi b c ⟩
        → (∀ x → x ◁ ⟨ q₀ ⟩ → lt x ⟨ q₀ ⟩ ≡ true)
        → (∀ y → y ◁ ⟨ q₀ ⟩ → lt y ⟨ phi b c ⟩ ≡ true)
        → lt ⟨ q₀ ⟩ ⟨ phi b c ⟩ ≡ true
φʳ-case b c (phi x y) l sz ihq ihy = unf⁻ (phi x y) (phi b c) (neq-size (phi x y) (phi b c) sz) body
  where
    D₁ = lt x b ∧ lt y ⟨ phi b c ⟩ ; D₂ = eqT x b ∧ lt y c ; D₃ = lt b x ∧ le ⟨ phi x y ⟩ c
    body : D₁ ∨ D₂ ∨ D₃ ≡ true
    body with tri x b (AT-all x b)
    ... | inj₁ (xb , _)        = ∨ˡ D₁ (D₂ ∨ D₃) (∧ⁱ (lt x b) (lt y ⟨ phi b c ⟩) xb (ihy y (φʳ (inj₂ refl))))
    ... | inj₂ (inj₁ x≡b)      = ∨ʳ D₁ (D₂ ∨ D₃) (∨ˡ D₂ D₃ (∧ⁱ (eqT x b) (lt y c) (eqT-complete x≡b) (via-hd y (phi x y) c (ihq y (φʳ (inj₂ refl))) l)))
    ... | inj₂ (inj₂ (_ , bx)) = ∨ʳ D₁ (D₂ ∨ D₃) (∨ʳ D₂ D₃ (∧ⁱ (lt b x) (le ⟨ phi x y ⟩ c) bx l))
φʳ-case b c (psi π d) l sz ihq ihy = trans (Gφ-lt (psi π d) b c refl) (not-≡false (trans (cong (lt b ⟨ psi π d ⟩ ∧_) (⪯⇒¬≺ c ⟨ psi π d ⟩ (le! l))) (∧-zeroʳ _)))
φʳ-case b c (Om a)    l sz ihq ihy = trans (Gφ-lt (Om a) b c refl)    (not-≡false (trans (cong (lt b ⟨ Om a ⟩ ∧_)    (⪯⇒¬≺ c ⟨ Om a ⟩ (le! l))) (∧-zeroʳ _)))
φʳ-case b c I         l sz ihq ihy = trans (Gφ-lt I b c refl)         (not-≡false (trans (cong (lt b ⟨ I ⟩ ∧_)         (⪯⇒¬≺ c ⟨ I ⟩ (le! l))) (∧-zeroʳ _)))

Ω-case : ∀ a q₀ → le ⟨ q₀ ⟩ a ≡ true → size ⟨ q₀ ⟩ < size ⟨ Om a ⟩
       → (∀ x → x ◁ ⟨ q₀ ⟩ → lt x ⟨ q₀ ⟩ ≡ true)
       → (∀ y → y ◁ ⟨ q₀ ⟩ → lt y ⟨ Om a ⟩ ≡ true)
       → lt ⟨ q₀ ⟩ ⟨ Om a ⟩ ≡ true
Ω-case a (phi x y) l sz ihq ihy =
  trans (φG-lt x y (Om a) refl) (∧ⁱ (lt x ⟨ Om a ⟩) (lt y ⟨ Om a ⟩) (ihy x (φˡ (inj₂ refl))) (ihy y (φʳ (inj₂ refl))))
Ω-case a (psi (ΩR z) d) l sz ihq ihy =
  unf⁻ (psi (ΩR z) d) (Om a) refl (leˡ ⟨ Om z ⟩ ⟨ Om a ⟩ (trans (lt-unfold≠ (Om z) (Om a) ez) za))
  where
    za : lt z a ≡ true
    za = via-hd z (psi (ΩR z) d) a (ihq z (ψl (inj₂ refl))) l
    ez : eqT z a ≡ false
    ez = ≺⇒eqT-false z a (AT-all z a) za
Ω-case a (psi IR d) l sz ihq ihy = unf⁻ (psi IR d) (Om a) refl l
Ω-case a (Om z) l sz ihq ihy = unf⁻ (Om z) (Om a) ez za
  where
    za : lt z a ≡ true
    za = via-hd z (Om z) a (ihq z (Ωa (inj₂ refl))) l
    ez : eqT z a ≡ false
    ez = ≺⇒eqT-false z a (AT-all z a) za
Ω-case a I l sz ihq ihy = unf⁻ I (Om a) refl (not-≡false (⪯⇒¬≺ a ⟨ I ⟩ (le! l)))

ψ-case : ∀ a b q₀ → le ⟨ q₀ ⟩ a ≡ true → size ⟨ q₀ ⟩ < size ⟨ psi (ΩR a) b ⟩
       → (∀ x → x ◁ ⟨ q₀ ⟩ → lt x ⟨ q₀ ⟩ ≡ true)
       → (∀ y → y ◁ ⟨ q₀ ⟩ → lt y ⟨ psi (ΩR a) b ⟩ ≡ true)
       → lt ⟨ q₀ ⟩ ⟨ psi (ΩR a) b ⟩ ≡ true
ψ-case a b (phi x y) l sz ihq ihy =
  trans (φG-lt x y (psi (ΩR a) b) refl)
        (∧ⁱ (lt x ⟨ psi (ΩR a) b ⟩) (lt y ⟨ psi (ΩR a) b ⟩) (ihy x (φˡ (inj₂ refl))) (ihy y (φʳ (inj₂ refl))))
ψ-case a b (psi (ΩR z) d) l sz ihq ihy =
  unf⁻ (psi (ΩR z) d) (psi (ΩR a) b) (cong (_∧ eqT d b) ez) (sh ez (trans (lt-unfold≠ (Om z) (Om a) ez) za))
  where
    za : lt z a ≡ true
    za = via-hd z (psi (ΩR z) d) a (ihq z (ψl (inj₂ refl))) l
    ez : eqT z a ≡ false
    ez = ≺⇒eqT-false z a (AT-all z a) za
    sh : ∀ {ea bd oo : Bool} → ea ≡ false → oo ≡ true → (ea ∧ bd) ∨ (oo ∨ (false ∨ false)) ≡ true
    sh refl refl = refl
ψ-case a b (psi IR d) l sz ihq ihy =
  unf⁻ (psi IR d) (psi (ΩR a) b) refl (∨ˡ (lt ⟨ psi IR d ⟩ ⟨ Om a ⟩) false (trans (lt-unfold≠ (psi IR d) (Om a) refl) l))
ψ-case a b (Om z) l sz ihq ihy =
  unf⁻ (Om z) (psi (ΩR a) b) refl (not-≡false (cong₂ _∨_ (trans (lt-unfold≠ (Om a) (Om z) eaz) (lt-asym z a za)) eaz))
  where
    za : lt z a ≡ true
    za = via-hd z (Om z) a (ihq z (Ωa (inj₂ refl))) l
    eaz : eqT a z ≡ false
    eaz = eqT-false-sym z a (≺⇒eqT-false z a (AT-all z a) za)
ψ-case a b I l sz ihq ihy =
  unf⁻ I (psi (ΩR a) b) refl (not-≡false (cong (_∨ false) (trans (lt-unfold≠ (Om a) I refl) (⪯⇒¬≺ a ⟨ I ⟩ (le! l)))))
```

## 3. 双重强归纳

```agda
P◁ : Tm → Tm → Set
P◁ t s = s ◁ t → lt s t ≡ true

IHT : Tm → Set
IHT t = ∀ t′ s′ → size t′ < size t → P◁ t′ s′

IHS : Tm → Tm → Set
IHS t s = ∀ s′ → size s′ < size s → P◁ t s′

-- s ⊴ u ⟹ s ⪯ u（u 是比 t 小的容器）
⊴-le : ∀ t u s → IHT t → size u < size t → s ⊴ u → le s u ≡ true
⊴-le t u s ihT h (inj₁ d)    = leˡ s u (ihT u s h d)
⊴-le t u s ihT h (inj₂ refl) = leʳ s s (eqT-refl s)

zer-case : ∀ {t} → zer ◁ t → lt zer t ≡ true
zer-case (φˡ {b = b} {c = c} _) = lt-zer zer (phi b c)
zer-case (φʳ {b = b} {c = c} _) = lt-zer zer (phi b c)
zer-case (Ωa {a = a} _)         = lt-zer zer (Om a)
zer-case (ψl {a = a} {b = b} _) = lt-zer zer (psi (ΩR a) b)
zer-case (hd◁ {a = a} {q = q} _ _) = lt-zer a q

step◁ : ∀ {t s} → IHT t → IHS t s → s ◁ t → lt s t ≡ true
step◁ {t} {s = zer} ihT ihS d = zer-case d
step◁ {_} {s = a ▹ q} ihT ihS (φˡ {b = b} {c = c} sb) =
  hd-lt⟨⟩ s (phi b c) tt (φˡ-case b c (hd s) l sz (λ x d′ → ihT ⟨ hd s ⟩ x sz d′)
    (λ y d′ → ihS y (<-≤-trans (◁-size d′) (hd-size≤ s tt)) (φˡ (inj₁ (◁⊴-trans (hd-lift s tt d′) sb)))))
  where
    s = a ▹ q
    l : le ⟨ hd s ⟩ b ≡ true
    l = le≡ (⪯-trans {⟨ hd s ⟩} {s} {b} (le! (hd-le s tt)) (le! (⊴-le ⟨ phi b c ⟩ b s ihT (sz-φˡ b c) sb)))
    sz : size ⟨ hd s ⟩ < size ⟨ phi b c ⟩
    sz = ≤-<-trans (hd-size≤ s tt) (≤-<-trans (⊴-size sb) (sz-φˡ b c))
step◁ {_} {s = a ▹ q} ihT ihS (φʳ {b = b} {c = c} sc) =
  hd-lt⟨⟩ s (phi b c) tt (φʳ-case b c (hd s) l sz (λ x d′ → ihT ⟨ hd s ⟩ x sz d′)
    (λ y d′ → ihS y (<-≤-trans (◁-size d′) (hd-size≤ s tt)) (φʳ (inj₁ (◁⊴-trans (hd-lift s tt d′) sc)))))
  where
    s = a ▹ q
    l : le ⟨ hd s ⟩ c ≡ true
    l = le≡ (⪯-trans {⟨ hd s ⟩} {s} {c} (le! (hd-le s tt)) (le! (⊴-le ⟨ phi b c ⟩ c s ihT (sz-φʳ b c) sc)))
    sz : size ⟨ hd s ⟩ < size ⟨ phi b c ⟩
    sz = ≤-<-trans (hd-size≤ s tt) (≤-<-trans (⊴-size sc) (sz-φʳ b c))
step◁ {_} {s = a ▹ q} ihT ihS (Ωa {a = u} su) =
  hd-lt⟨⟩ s (Om u) tt (Ω-case u (hd s) l sz (λ x d′ → ihT ⟨ hd s ⟩ x sz d′)
    (λ y d′ → ihS y (<-≤-trans (◁-size d′) (hd-size≤ s tt)) (Ωa (inj₁ (◁⊴-trans (hd-lift s tt d′) su)))))
  where
    s = a ▹ q
    l : le ⟨ hd s ⟩ u ≡ true
    l = le≡ (⪯-trans {⟨ hd s ⟩} {s} {u} (le! (hd-le s tt)) (le! (⊴-le ⟨ Om u ⟩ u s ihT (sz-Ω u) su)))
    sz : size ⟨ hd s ⟩ < size ⟨ Om u ⟩
    sz = ≤-<-trans (hd-size≤ s tt) (≤-<-trans (⊴-size su) (sz-Ω u))
step◁ {_} {s = a ▹ q} ihT ihS (ψl {a = u} {b = b} su) =
  hd-lt⟨⟩ s (psi (ΩR u) b) tt (ψ-case u b (hd s) l sz (λ x d′ → ihT ⟨ hd s ⟩ x sz d′)
    (λ y d′ → ihS y (<-≤-trans (◁-size d′) (hd-size≤ s tt)) (ψl (inj₁ (◁⊴-trans (hd-lift s tt d′) su)))))
  where
    s = a ▹ q
    l : le ⟨ hd s ⟩ u ≡ true
    l = le≡ (⪯-trans {⟨ hd s ⟩} {s} {u} (le! (hd-le s tt)) (le! (⊴-le ⟨ psi (ΩR u) b ⟩ u s ihT (sz-ψa u b) su)))
    sz : size ⟨ hd s ⟩ < size ⟨ psi (ΩR u) b ⟩
    sz = ≤-<-trans (hd-size≤ s tt) (≤-<-trans (⊴-size su) (sz-ψa u b))
step◁ {_} {s = a ▹ q} ihT ihS (hd◁ {a = a′} {q = q′} nz d′) =
  lt-trans (a ▹ q) ⟨ hd (a′ ▹ q′) ⟩ (a′ ▹ q′) (ihT ⟨ hd (a′ ▹ q′) ⟩ (a ▹ q) (hd-size< a′ q′ nz) d′) (hd-lt a′ q′ nz)

inner◁ : ∀ t → IHT t → ∀ m s → size s < m → P◁ t s
inner◁ t ihT zero    s ()
inner◁ t ihT (suc m) s h = step◁ ihT (λ s′ h′ → inner◁ t ihT m s′ (<-≤-trans h′ (≤-pred h)))

outer◁ : ∀ n t → size t < n → ∀ s → P◁ t s
outer◁ zero    t ()
outer◁ (suc n) t h s = inner◁ t (λ t′ s′ h′ → outer◁ n t′ (<-≤-trans h′ (≤-pred h)) s′) (suc (size s)) s ≤-refl

◁-lt : ∀ t s → s ◁ t → lt s t ≡ true
◁-lt t s = outer◁ (suc (size t)) t ≤-refl s
```

## 4. 导出

```agda
≺-φˡ : ∀ b c → lt b ⟨ phi b c ⟩ ≡ true
≺-φˡ b c = ◁-lt ⟨ phi b c ⟩ b (φˡ (inj₂ refl))

≺-φʳ : ∀ b c → lt c ⟨ phi b c ⟩ ≡ true
≺-φʳ b c = ◁-lt ⟨ phi b c ⟩ c (φʳ (inj₂ refl))

≺-Ωa : ∀ a → lt a ⟨ Om a ⟩ ≡ true
≺-Ωa a = ◁-lt ⟨ Om a ⟩ a (Ωa (inj₂ refl))

```
