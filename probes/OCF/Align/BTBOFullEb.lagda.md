# 累加层号的分块嵌入

> 接 [BTBOFullEmb](BTBOFullEmb.lagda.md). `Eb A Bd` 是从 `Ordᴰ` 的 $A$ 的字面前驱到一个抽象严格序 (`Tgt`) 的映射, 像都在 `Bd` 之下. `blocks`: 累加 $\sum_n O_n$ 的前驱按块映射, 块 $n$ 的元素形如 $\Sigma_{n-1}+d$, 只看 $d$.
>
> `V2`: $x\preccurlyeq y$ 且两边 `St`, 则 `ordᴰ x` 的前驱保序映到 `ordᴰ y` 的前驱. 这里用到目标是累加: 偏移 $\Sigma+z$ 字面就在目标里, 所以任何块都放得下, 不用算术.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFullEb where

open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (≤⇒≤′; m≤m+n; m≤n+m)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; module Trich; injᵃ; injᵇ; injᶜ)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum; cumsum-mono) renaming (_+_ to _+ᴰ_)
open S using (ordᴰ; zero; suc; lim; limᵢ)
open import OCF.Align.Level using (Ordᶜ)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValAbsorb using (St; st-s⁻; st-l₁; st-l₂; lim-≼⁻)
open import OCF.Align.BTBOFullQ using (<ᴰ-irrefl; clash-lt)
open import OCF.Align.Value using (_≼_; s≼s; s≼s⁻; s≼0; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≼lim⁻)
```

## §1 累加的字面性质

```agda
lt-add : ∀ {x a} → x B.< a → ∀ z → x B.< a +ᴰ z
lt-add p B.zero      = p
lt-add p (B.suc z)   = B.suc (lt-add p z)
lt-add p (B.lim f m) = B.lim 0 (lt-add p (f 0))

add-not< : ∀ a d → ¬ (a +ᴰ d B.< a)
add-not< a B.zero      p = <ᴰ-irrefl p
add-not< a (B.suc d)   p = add-not< a d (B.<-trans B.zero p)
add-not< a (B.lim f m) p = add-not< a (f 0) (B.<-trans (B.f<l 0) p)

data Inv (a b c : Ordᴰ) : Set where
  inl : c B.< a → Inv a b c
  inr : ∀ d → d B.< b → c ≡ a +ᴰ d → Inv a b c

inv : ∀ {a b c} → c B.< a +ᴰ b → Inv a b c
inv {b = B.zero}    q = inl q
inv {a} {b = B.suc b} B.zero = inr b B.zero refl
inv {a} {b = B.suc b} (B.suc q) with inv {a} {b} q
... | inl r     = inl r
... | inr d r e = inr d (B.suc r) e
inv {a} {b = B.lim f m} (B.lim n q) with inv {a} {f n} q
... | inl r     = inl r
... | inr d r e = inr d (B.lim n r) e

cancel< : ∀ {a d₁ d₂ b} → d₁ B.< b → d₂ B.< b → a +ᴰ d₁ B.< a +ᴰ d₂ → d₁ B.< d₂
cancel< p q r with B.<-dec p q
... | injᵃ x    = x
... | injᵇ x    = ⊥-elim (clash-lt r (B.+-mono x))
... | injᶜ refl = ⊥-elim (<ᴰ-irrefl r)

cancel≡ : ∀ {a d₁ d₂ b} → d₁ B.< b → d₂ B.< b → a +ᴰ d₁ ≡ a +ᴰ d₂ → d₁ ≡ d₂
cancel≡ p q e with B.<-dec p q
... | injᵃ x = ⊥-elim (<ᴰ-irrefl (subst (B._< _) e (B.+-mono x)))
... | injᵇ x = ⊥-elim (<ᴰ-irrefl (subst (_ B.<_) e (B.+-mono x)))
... | injᶜ x = x
```

## §2 抽象目标与分块

```agda
record Tgt : Set₁ where
  infix 4 _≺_ _≈_
  field
    C   : Set
    _≺_ : C → C → Set
    _≈_ : C → C → Set
    ≈r  : ∀ a → a ≈ a
    ≈s  : ∀ {a b} → a ≈ b → b ≈ a
    ≈t  : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
    ≺t  : ∀ {a b c} → a ≺ b → b ≺ c → a ≺ c
    ≺l  : ∀ {a a′ b} → a ≈ a′ → a ≺ b → a′ ≺ b
    ≺r  : ∀ {a b b′} → a ≺ b → b ≈ b′ → a ≺ b′

module Blocks (𝕋 : Tgt) where
  open Tgt 𝕋

  record Eb (A : Ordᴰ) (Bd : C) : Set where
    field
      map   : ∀ {c} → c B.< A → C
      below : ∀ {c} (p : c B.< A) → map p ≺ Bd
      mono  : ∀ {c d} (p : c B.< A) (q : d B.< A) → c B.< d → map p ≺ map q
      coh   : ∀ {c d} (p : c B.< A) (q : d B.< A) → c ≡ d → map p ≈ map q
  open Eb public

  Eb-zero : ∀ {Bd} → Eb B.zero Bd
  Eb-zero = record { map = λ () ; below = λ () ; mono = λ () ; coh = λ () }

  Eb-wk : ∀ {A Bd Bd′} → Eb A Bd → (∀ {x} → x ≺ Bd → x ≺ Bd′) → Eb A Bd′
  Eb-wk e k = record { map = map e ; below = λ p → k (below e p) ; mono = mono e ; coh = coh e }

  Eb-suc : ∀ {A Bd T} → Eb A Bd → (top : C) → (∀ {x} → x ≺ Bd → x ≺ top) → top ≺ T → Eb (B.suc A) T
  Eb-suc {A} e top fl lt = record { map = m ; below = bl ; mono = mn ; coh = ch }
    where
    m : ∀ {c} → c B.< B.suc A → C
    m B.zero    = top
    m (B.suc p) = map e p
    bl : ∀ {c} (p : c B.< B.suc A) → m p ≺ _
    bl B.zero    = lt
    bl (B.suc p) = ≺t (fl (below e p)) lt
    mn : ∀ {c d} (p : c B.< B.suc A) (q : d B.< B.suc A) → c B.< d → m p ≺ m q
    mn B.zero    B.zero    r = ⊥-elim (<ᴰ-irrefl r)
    mn B.zero    (B.suc q) r = ⊥-elim (clash-lt r q)
    mn (B.suc p) B.zero    r = fl (below e p)
    mn (B.suc p) (B.suc q) r = mono e p q r
    ch : ∀ {c d} (p : c B.< B.suc A) (q : d B.< B.suc A) → c ≡ d → m p ≈ m q
    ch B.zero    B.zero    e′ = ≈r top
    ch B.zero    (B.suc q) refl = ⊥-elim (<ᴰ-irrefl q)
    ch (B.suc p) B.zero    refl = ⊥-elim (<ᴰ-irrefl p)
    ch (B.suc p) (B.suc q) e′ = coh e p q e′

  module Blk (O : ℕ → Ordᴰ) (Bd : ℕ → C) (B∞ : C) (e₀ : Eb (O 0) (Bd 0))
    (N  : ∀ n {d} → d B.< B.suc (O (suc n)) → C)
    (Nb : ∀ n {d} (p : d B.< B.suc (O (suc n))) → N n p ≺ Bd (suc n))
    (Nm : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O (suc n))) (q : d₂ B.< B.suc (O (suc n))) → d₁ B.< d₂ → N n p ≺ N n q)
    (Nc : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O (suc n))) (q : d₂ B.< B.suc (O (suc n))) → d₁ ≡ d₂ → N n p ≈ N n q)
    (fl : ∀ n {x} → x ≺ Bd n → ∀ {d} (p : d B.< B.suc (O (suc n))) → x ≺ N n p)
    (sp : ∀ n {x} → x ≺ Bd n → x ≺ B∞) where

    Σs : ℕ → Ordᴰ
    Σs = cumsum O

    disp : ∀ n {c} → (∀ {c′} → c′ B.< Σs n → C) → Inv (Σs n) (B.suc (O (suc n))) c → C
    disp n m₀ (inl q)     = m₀ q
    disp n m₀ (inr d r e) = N n r

    En : ∀ n → Eb (Σs n) (Bd n)
    En zero    = e₀
    En (suc n) = record { map = m ; below = bl ; mono = mn ; coh = ch }
      where
      e = En n
      m : ∀ {c} → c B.< Σs (suc n) → C
      m p = disp n (map e) (inv p)
      bl : ∀ {c} (p : c B.< Σs (suc n)) → m p ≺ Bd (suc n)
      bl p with inv {Σs n} {B.suc (O (suc n))} p
      ... | inl q     = ≺t (fl n (below e q) B.zero) (Nb n B.zero)
      ... | inr d r _ = Nb n r
      mn : ∀ {c d} (p : c B.< Σs (suc n)) (q : d B.< Σs (suc n)) → c B.< d → m p ≺ m q
      mn p q x with inv {Σs n} {B.suc (O (suc n))} p | inv {Σs n} {B.suc (O (suc n))} q
      ... | inl p′      | inl q′      = mono e p′ q′ x
      ... | inl p′      | inr d r ee  = fl n (below e p′) r
      ... | inr d r refl | inl q′     = ⊥-elim (add-not< (Σs n) d (B.<-trans x q′))
      ... | inr d₁ r₁ refl | inr d₂ r₂ refl = Nm n r₁ r₂ (cancel< r₁ r₂ x)
      ch : ∀ {c d} (p : c B.< Σs (suc n)) (q : d B.< Σs (suc n)) → c ≡ d → m p ≈ m q
      ch p q x with inv {Σs n} {B.suc (O (suc n))} p | inv {Σs n} {B.suc (O (suc n))} q
      ... | inl p′      | inl q′      = coh e p′ q′ x
      ... | inl p′      | inr d r ee  = ⊥-elim (add-not< (Σs n) d (subst (B._< _) (trans x ee) p′))
      ... | inr d r ee  | inl q′      = ⊥-elim (add-not< (Σs n) d (subst (B._< _) (trans (sym x) ee) q′))
      ... | inr d₁ r₁ refl | inr d₂ r₂ refl = Nc n r₁ r₂ (cancel≡ r₁ r₂ x)

    lift1 : ∀ n {c} → c B.< Σs n → c B.< Σs (suc n)
    lift1 n p = lt-add p (B.suc (O (suc n)))

    ext1 : ∀ n {c} (p : c B.< Σs n) → map (En (suc n)) (lift1 n p) ≈ map (En n) p
    ext1 n p with inv {Σs n} {B.suc (O (suc n))} (lift1 n p)
    ... | inl q      = coh (En n) q p refl
    ... | inr d r ee = ⊥-elim (add-not< (Σs n) d (subst (B._< _) ee p))

    liftS : ∀ {n k c} → n ≤′ k → c B.< Σs n → c B.< Σs k
    liftS ≤′-refl     p = p
    liftS (≤′-step k) p = lift1 _ (liftS k p)

    extS : ∀ {n k c} (l : n ≤′ k) (p : c B.< Σs n) → map (En k) (liftS l p) ≈ map (En n) p
    extS ≤′-refl     p = ≈r _
    extS (≤′-step l) p = ≈t (ext1 _ (liftS l p)) (extS l p)

    Lim : Eb (B.lim Σs (cumsum-mono O)) B∞
    Lim = record { map = m ; below = bl ; mono = mn ; coh = ch }
      where
      m : ∀ {c} → c B.< B.lim Σs (cumsum-mono O) → C
      m (B.lim n p) = map (En n) p
      bl : ∀ {c} (p : c B.< B.lim Σs (cumsum-mono O)) → m p ≺ B∞
      bl (B.lim n p) = sp n (below (En n) p)
      mn : ∀ {c d} (p : c B.< B.lim Σs (cumsum-mono O)) (q : d B.< B.lim Σs (cumsum-mono O)) → c B.< d → m p ≺ m q
      mn (B.lim n p) (B.lim k q) r =
        ≺l (extS (≤⇒≤′ (m≤m+n n k)) p) (≺r (mono (En (n +ᴺ k)) (liftS (≤⇒≤′ (m≤m+n n k)) p) (liftS (≤⇒≤′ (m≤n+m k n)) q) r) (extS (≤⇒≤′ (m≤n+m k n)) q))
      ch : ∀ {c d} (p : c B.< B.lim Σs (cumsum-mono O)) (q : d B.< B.lim Σs (cumsum-mono O)) → c ≡ d → m p ≈ m q
      ch (B.lim n p) (B.lim k q) r =
        ≈t (≈s (extS (≤⇒≤′ (m≤m+n n k)) p)) (≈t (coh (En (n +ᴺ k)) (liftS (≤⇒≤′ (m≤m+n n k)) p) (liftS (≤⇒≤′ (m≤n+m k n)) q) r) (extS (≤⇒≤′ (m≤n+m k n)) q))
```

## §3 目标是累加

```agda
𝕆 : Tgt
𝕆 = record
  { C = Ordᴰ ; _≺_ = B._<_ ; _≈_ = _≡_
  ; ≈r = λ _ → refl ; ≈s = sym ; ≈t = trans
  ; ≺t = B.<-trans ; ≺l = λ { refl q → q } ; ≺r = λ { q refl → q } }

open Blocks 𝕆

off : (ℕ → Ordᴰ) → ℕ → Ordᴰ → Ordᴰ
off O zero    x = x
off O (suc k) x = cumsum O k +ᴰ x

off-mono : ∀ O m {x y} → x B.< y → off O m x B.< off O m y
off-mono O zero    r = r
off-mono O (suc k) r = B.+-mono r

off-top : ∀ O m {x} → x B.< O m → off O m x B.< cumsum O m
off-top O zero    r = r
off-top O (suc k) r = B.+-mono (B.suc r)

Eb-off : ∀ O m {A} → Eb A (O m) → Eb A (cumsum O m)
Eb-off O m e = record
  { map   = λ p → off O m (map e p)
  ; below = λ p → off-top O m (below e p)
  ; mono  = λ p q r → off-mono O m (mono e p q r)
  ; coh   = λ p q r → cong (off O m) (coh e p q r) }

Σ-lift : ∀ O {a k x} → a ≤′ k → x B.< cumsum O a → x B.< cumsum O k
Σ-lift O ≤′-refl     r = r
Σ-lift O (≤′-step l) r = B.<-trans (Σ-lift O l r) (cumsum-mono O Trich.zero)
```

## §4 `V2`

```agda
g-mono : ∀ {g : ℕ → S.Ord₀} → St (tr₀ (lim g)) → ∀ {a b} → a ≤′ b → tr₀ (g a) ≼ tr₀ (g b)
g-mono st ≤′-refl     = ≼-refl _
g-mono st (≤′-step l) = ≼-trans (g-mono st l) (≼-trans (≼-suc (≼-refl _)) (st-l₂ st _))

O∘ : (ℕ → S.Ord₀) → ℕ → Ordᴰ
O∘ f n = ordᴰ (f n)

V2  : ∀ (x y : S.Ord₀) → St (tr₀ x) → St (tr₀ y) → tr₀ x ≼ tr₀ y → Eb (ordᴰ x) (ordᴰ y)
V2s : ∀ (x₀ y : S.Ord₀) → St (tr₀ x₀) → St (tr₀ y) → tr₀ (suc x₀) ≼ tr₀ y → Eb (B.suc (ordᴰ x₀)) (ordᴰ y)

V2s x₀ zero sx sy w = ⊥-elim (s≼0 w)
V2s x₀ (suc y₀) sx sy (s≼s w) = Eb-suc (V2 x₀ y₀ sx (st-s⁻ sy) w) (ordᴰ y₀) (λ p → p) B.zero
V2s x₀ (lim g) sx sy (≼l m w) = Eb-wk (Eb-off (O∘ g) m (V2s x₀ (g m) sx (st-l₁ sy m) w)) (λ p → B.lim m p)
V2s x₀ (limᵢ () f) sx sy w

V2 zero y sx sy w = Eb-zero
V2 (suc x₀) y sx sy w = V2s x₀ y (st-s⁻ sx) sy w
V2 (limᵢ () f) y sx sy w
V2 (lim f) zero sx sy w = ⊥-elim (s≼0 (≼-trans (st-l₂ sx 0) (lim-≼⁻ w 1)))
V2 (lim f) (suc y₀) sx sy w =
  Eb-wk (V2 (lim f) y₀ sx (st-s⁻ sy) (l≼ (λ n → s≼s⁻ (≼-trans (st-l₂ sx n) (lim-≼⁻ w (suc n)))))) (λ p → B.suc p)
V2 (lim f) (lim g) sx sy w = Blk.Lim (O∘ f) Bd B∞ e₀ N Nb Nm Nc fl sp
  where
  B∞ = ordᴰ (lim g)
  bnd : ∀ n → Σ ℕ (λ m → tr₀ (suc (f n)) ≼ tr₀ (g m))
  bnd n = ≼lim⁻ (≼-trans (st-l₂ sx n) (lim-≼⁻ w (suc n)))
  M : ℕ → ℕ
  M zero    = proj₁ (bnd 0)
  M (suc n) = suc (M n +ᴺ proj₁ (bnd (suc n)))
  sM : ∀ n → tr₀ (suc (f n)) ≼ tr₀ (g (M n))
  sM zero    = proj₂ (bnd 0)
  sM (suc n) = ≼-trans (proj₂ (bnd (suc n))) (g-mono sy (≤′-step (≤⇒≤′ (m≤n+m (proj₁ (bnd (suc n))) (M n)))))
  Bd : ℕ → Ordᴰ
  Bd n = cumsum (O∘ g) (M n)
  e₀ : Eb (O∘ f 0) (Bd 0)
  e₀ = Eb-off (O∘ g) (M 0) (V2 (f 0) (g (M 0)) (st-l₁ sx 0) (st-l₁ sy (M 0)) (≼-trans (≼-suc (≼-refl _)) (sM 0)))
  eN : ∀ n → Eb (B.suc (O∘ f (suc n))) (O∘ g (M (suc n)))
  eN n = V2s (f (suc n)) (g (M (suc n))) (st-l₁ sx (suc n)) (st-l₁ sy (M (suc n))) (sM (suc n))
  N : ∀ n {d} → d B.< B.suc (O∘ f (suc n)) → Ordᴰ
  N n p = off (O∘ g) (M (suc n)) (map (eN n) p)
  Nb : ∀ n {d} (p : d B.< B.suc (O∘ f (suc n))) → N n p B.< Bd (suc n)
  Nb n p = off-top (O∘ g) (M (suc n)) (below (eN n) p)
  Nm : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O∘ f (suc n))) (q : d₂ B.< B.suc (O∘ f (suc n))) → d₁ B.< d₂ → N n p B.< N n q
  Nm n p q r = off-mono (O∘ g) (M (suc n)) (mono (eN n) p q r)
  Nc : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O∘ f (suc n))) (q : d₂ B.< B.suc (O∘ f (suc n))) → d₁ ≡ d₂ → N n p ≡ N n q
  Nc n p q r = cong (off (O∘ g) (M (suc n))) (coh (eN n) p q r)
  fl : ∀ n {x} → x B.< Bd n → ∀ {d} (p : d B.< B.suc (O∘ f (suc n))) → x B.< N n p
  fl n r p = lt-add (Σ-lift (O∘ g) (≤⇒≤′ (m≤m+n (M n) _)) r) _
  sp : ∀ n {x} → x B.< Bd n → x B.< B∞
  sp n r = B.lim (M n) r
```
