# src 树族内部的单调关系 `Qh`

> 接 [BTBOValDn](BTBOValDn.lagda.md). 本文只谈 src 的树族. `Qh x y` 是按右边层号分层的归纳关系, 对 `+`, `↑`, `ψ<` 封闭 (`Q-add`, `Q↑ʳ`, `Q↑ˡ`, `Q-ψ`). 严格性读作 `Qh (suc x) y`, 也对折叠封闭 (`S-ψ`). 这是 `BTBOFullSt` 证严格性的工具.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFullQ where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; module Trich; injᵃ; injᵇ; injᶜ)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ)
open S using (iter; zero; suc; lim; limᵢ)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValDn using (coe-coe₀)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-suc)
open import OCF.Align.Level using (Ordᶜ)
```

`<ᴰ-irrefl`: 第 0 层下标的字面序无自反.

```agda
data Accᴰ (a : Ordᴰ) : Set where
  acc : (∀ {b} → b B.< a → Accᴰ b) → Accᴰ a

accᴰ : ∀ a {b} → b B.< a → Accᴰ b
accᴰ (B.suc a)   B.zero      = acc (accᴰ a)
accᴰ (B.suc a)   (B.suc p)   = accᴰ a p
accᴰ (B.lim f m) (B.lim n p) = accᴰ (f n) p

<ᴰ-irrefl : ∀ {a} → ¬ (a B.< a)
<ᴰ-irrefl {a} = go (acc (accᴰ a)) where
  go : ∀ {a} → Accᴰ a → ¬ (a B.< a)
  go (acc h) p = go (h p) p

clash-lt : ∀ {a b} → a B.< b → b B.< a → ⊥
clash-lt p q = <ᴰ-irrefl (B.<-trans p q)
```

## §1 关系

`Qb` 是 "链过了 $\Omega_c+1$" 的规则, $c\le j$. 只有 `Qb` 能让 $\Omega_c+1$ 落在 $\Omega_{c+1}$ 之下: 链的第 0 项 $0$, 第 1 项 $\ge\Omega_c$, 第 2 项才过 $\Omega_c+1$, 要分支非零.

```agda
Lev : Ordᴰ → Ordᴰ → Set
Lev c j = c B.< j ⊎ c ≡ j

module _ (k : Ordᴰ) (Q< : (i : Ordᴰ) (p : i B.< k) → S.Ord< i p → ∀ {ℓ} → S.Ord ℓ → Set) where
  data Q₊ : ∀ {ℓ} → S.Ord ℓ → S.Ord k → Set where
    Qz  : ∀ {ℓ} {b : S.Ord k} → Q₊ {ℓ} zero b
    Qs  : ∀ {ℓ} {a : S.Ord ℓ} {b : S.Ord k} → Q₊ a b → Q₊ (suc a) (suc b)
    Qsr : ∀ {ℓ} {a : S.Ord ℓ} {b : S.Ord k} → Q₊ a b → Q₊ a (suc b)
    Qll : ∀ {ℓ} {f : ℕ → S.Ord ℓ} {b : S.Ord k} → (∀ n → Q₊ (f n) b) → Q₊ (lim f) b
    Qlr : ∀ {ℓ} {a : S.Ord ℓ} {g : ℕ → S.Ord k} n → Q₊ a (g n) → Q₊ a (lim g)
    Qii : ∀ {ℓ j} {q₁ : j B.< ℓ} {q : j B.< k} {f : S.Ord< j q₁ → S.Ord ℓ} {g : S.Ord< j q → S.Ord k} →
          (∀ (z z′ : S.Ord j) → Q< j q (S.coe₀ {p = q} z′) z → Q₊ (f (S.coe₀ {p = q₁} z)) (g (S.coe₀ {p = q} z′))) →
          Q₊ (limᵢ q₁ f) (limᵢ q g)
    Qir : ∀ {ℓ j} {a : S.Ord ℓ} {q : j B.< k} {g : S.Ord< j q → S.Ord k} →
          (∀ (z′ : S.Ord j) → Q₊ a (g (S.coe₀ {p = q} z′))) → Q₊ a (limᵢ q g)
    Qb  : ∀ {ℓ j} {a : S.Ord ℓ} {q : j B.< k} {g : S.Ord< j q → S.Ord k} {c} → Lev c j →
          (∀ (z′ : S.Ord j) → Q< j q (S.coe₀ {p = q} z′) (S.Ω j) → Q< j q (S.coe₀ {p = q} z′) (suc (zero {ℓ = B.zero})) →
             Q₊ (suc (zero {ℓ = B.zero})) (g (S.coe₀ {p = q} z′))) →
          (∀ (z′ : S.Ord j) → Q< j q (S.coe₀ {p = q} z′) (suc (S.Ω c)) → Q₊ a (g (S.coe₀ {p = q} z′))) →
          Q₊ a (limᵢ q g)

Q< : ∀ {k} (i : Ordᴰ) (p : i B.< k) → S.Ord< i p → ∀ {ℓ} → S.Ord ℓ → Set
Q< i B.zero      y a = Q₊ i Q< a y
Q< i (B.suc p)   y a = Q< i p y a
Q< i (B.lim n p) y a = Q< i p y a

Qh : ∀ {ℓ k} → S.Ord ℓ → S.Ord k → Set
Qh {k = k} = Q₊ k Q<

Q<→Q : ∀ {i k ℓ} (p : i B.< k) {y : S.Ord i} {a : S.Ord ℓ} → Q< i p (S.coe₀ {p = p} y) a → Qh a y
Q<→Q B.zero      d = d
Q<→Q (B.suc p)   d = Q<→Q p d
Q<→Q (B.lim n p) d = Q<→Q p d

Q→Q< : ∀ {i k ℓ} (p : i B.< k) {y : S.Ord i} {a : S.Ord ℓ} → Qh a y → Q< i p (S.coe₀ {p = p} y) a
Q→Q< B.zero      d = d
Q→Q< (B.suc p)   d = Q→Q< p d
Q→Q< (B.lim n p) d = Q→Q< p d

one : ∀ {ℓ} → S.Ord ℓ
one = suc zero

Q-one-conv : ∀ {ℓ₁ ℓ₂ k} {y : S.Ord k} → Qh (one {ℓ₁}) y → Qh (one {ℓ₂}) y
Q-one-conv (Qs d)    = Qs Qz
Q-one-conv (Qsr d)   = Qsr (Q-one-conv d)
Q-one-conv (Qlr n d) = Qlr n (Q-one-conv d)
Q-one-conv (Qir h)   = Qir (λ z′ → Q-one-conv (h z′))
Q-one-conv (Qb r nz h) = Qb r nz (λ z′ w → Q-one-conv (h z′ w))

Q-s→one : ∀ {ℓ₁ ℓ₂ k} {x : S.Ord ℓ₁} {y : S.Ord k} → Qh (suc x) y → Qh (one {ℓ₂}) y
Q-s→one (Qs d)    = Qs Qz
Q-s→one (Qsr d)   = Qsr (Q-s→one d)
Q-s→one (Qlr n d) = Qlr n (Q-s→one d)
Q-s→one (Qir h)   = Qir (λ z′ → Q-s→one (h z′))
Q-s→one (Qb r nz h) = Qb r nz (λ z′ w → Q-s→one (h z′ w))

Q→≼ : ∀ {x y : S.Ord₀} → Qh x y → tr₀ x ≼ tr₀ y
Q→≼ Qz        = z≼
Q→≼ (Qs d)    = s≼s (Q→≼ d)
Q→≼ (Qsr d)   = ≼-suc (Q→≼ d)
Q→≼ (Qll h)   = l≼ (λ n → Q→≼ (h n))
Q→≼ (Qlr n d) = ≼l n (Q→≼ d)
Q→≼ (Qii {q = ()} h)
Q→≼ (Qir {q = ()} h)
Q→≼ (Qb {q = ()} r nz h)
```

## §2 沿 `↑` 不变

```agda
Q↑ʳ : ∀ {k k′ ℓ} (r : k B.< k′) {x : S.Ord ℓ} {y : S.Ord k} → Qh x y → Qh x (S.↑ r y)
Q↑ʳ r Qz        = Qz
Q↑ʳ r (Qs d)    = Qs (Q↑ʳ r d)
Q↑ʳ r (Qsr d)   = Qsr (Q↑ʳ r d)
Q↑ʳ r (Qll h)   = Qll (λ n → Q↑ʳ r (h n))
Q↑ʳ r (Qlr n d) = Qlr n (Q↑ʳ r d)
Q↑ʳ r (Qii {q₁ = q₁} {q = q} {f = f} {g = g} h) = Qii (λ z z′ w →
  subst (λ u → Qh (f (S.coe₀ {p = q₁} z)) (S.↑ r (g u))) (sym (coe-coe₀ (B.<-trans q r) q z′))
        (Q↑ʳ r (h z z′ (Q→Q< q (Q<→Q (B.<-trans q r) w)))))
Q↑ʳ r (Qir {a = a} {q = q} {g = g} h) = Qir (λ z′ →
  subst (λ u → Qh a (S.↑ r (g u))) (sym (coe-coe₀ (B.<-trans q r) q z′)) (Q↑ʳ r (h z′)))
Q↑ʳ r (Qb {a = a} {q = q} {g = g} c nz h) = Qb c
  (λ z′ w₁ w₂ → subst (λ u → Qh one (S.↑ r (g u))) (sym (coe-coe₀ (B.<-trans q r) q z′))
     (Q↑ʳ r (nz z′ (Q→Q< q (Q<→Q (B.<-trans q r) w₁)) (Q→Q< q (Q<→Q (B.<-trans q r) w₂)))))
  (λ z′ w → subst (λ u → Qh a (S.↑ r (g u))) (sym (coe-coe₀ (B.<-trans q r) q z′))
     (Q↑ʳ r (h z′ (Q→Q< q (Q<→Q (B.<-trans q r) w)))))

Q↑ˡ : ∀ {k ℓ ℓ′} (r : ℓ B.< ℓ′) {x : S.Ord ℓ} {y : S.Ord k} → Qh x y → Qh (S.↑ r x) y
Q↑ˡ r Qz        = Qz
Q↑ˡ r (Qs d)    = Qs (Q↑ˡ r d)
Q↑ˡ r (Qsr d)   = Qsr (Q↑ˡ r d)
Q↑ˡ r (Qll h)   = Qll (λ n → Q↑ˡ r (h n))
Q↑ˡ r (Qlr n d) = Qlr n (Q↑ˡ r d)
Q↑ˡ r (Qii {q₁ = q₁} {f = f} {g = g} h) = Qii (λ z z′ w →
  subst (λ u → Qh (S.↑ r (f u)) _) (sym (coe-coe₀ (B.<-trans q₁ r) q₁ z)) (Q↑ˡ r (h z z′ w)))
Q↑ˡ r (Qir h)     = Qir (λ z′ → Q↑ˡ r (h z′))
Q↑ˡ r (Qb c nz h) = Qb c nz (λ z′ w → Q↑ˡ r (h z′ w))
```

## §3 加法

```agda
Q-add-r : ∀ {k ℓ} {a : S.Ord ℓ} {a′ : S.Ord k} (b : S.Ord k) → Qh a a′ → Qh a (a′ S.+ b)
Q-add-r zero       d = d
Q-add-r (suc b)    d = Qsr (Q-add-r b d)
Q-add-r (lim g)    d = Qlr 0 (Q-add-r (g 0) d)
Q-add-r (limᵢ q g) d = Qir (λ z′ → Q-add-r (g (S.coe₀ {p = q} z′)) d)

Q-add : ∀ {k ℓ} {a b : S.Ord ℓ} {a′ b′ : S.Ord k} → Qh a a′ → Qh b b′ → Qh (a S.+ b) (a′ S.+ b′)
Q-add {b′ = b′} da Qz = Q-add-r b′ da
Q-add da (Qs d)    = Qs (Q-add da d)
Q-add da (Qsr d)   = Qsr (Q-add da d)
Q-add da (Qll h)   = Qll (λ n → Q-add da (h n))
Q-add da (Qlr n d) = Qlr n (Q-add da d)
Q-add da (Qii h)   = Qii (λ z z′ w → Q-add da (h z z′ w))
Q-add da (Qir h)   = Qir (λ z′ → Q-add da (h z′))
Q-add da (Qb c nz h) = Qb c (λ z′ w₁ w₂ → Q-add-l (nz z′ w₁ w₂)) (λ z′ w → Q-add da (h z′ w))
  where
  Q-add-l : ∀ {k ℓ} {x : S.Ord ℓ} {a′ b′ : S.Ord k} → Qh x b′ → Qh x (a′ S.+ b′)
  Q-add-l Qz        = Qz
  Q-add-l (Qs d)    = Qs (Q-add-l d)
  Q-add-l (Qsr d)   = Qsr (Q-add-l d)
  Q-add-l (Qll h)   = Qll (λ n → Q-add-l (h n))
  Q-add-l (Qlr n d) = Qlr n (Q-add-l d)
  Q-add-l (Qii h)   = Qii (λ z z′ w → Q-add-l (h z z′ w))
  Q-add-l (Qir h)   = Qir (λ z′ → Q-add-l (h z′))
  Q-add-l (Qb c n h) = Qb c (λ z′ w₁ w₂ → Q-add-l (n z′ w₁ w₂)) (λ z′ w → Q-add-l (h z′ w))

iter-Q : ∀ {k ℓ} {A : S.Ord ℓ} {A′ : S.Ord k} → Qh A A′ → ∀ n → Qh (iter (A S.+_) zero n) (iter (A′ S.+_) zero n)
iter-Q d zero    = Qz
iter-Q d (suc n) = Q-add d (iter-Q d n)
```

## §4 $\Omega$

```agda
ω-refl : (g : ℕ → S.Ord₀) → (∀ n → Qh (g n) (g n)) → Qh (lim g) (lim g)
ω-refl g h = Qll (λ n → Qlr n (h n))

qnat : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → ∀ n → Qh (g n) (g n)
qnat g g0 gs zero    = subst (λ u → Qh u u) (sym g0) Qz
qnat g g0 gs (suc n) = subst (λ u → Qh u u) (sym (gs n)) (Qs (qnat g g0 gs n))

seqω : ℕ → S.Ord₀
seqω = sq S.ω
  where sq : S.Ord₀ → ℕ → S.Ord₀
        sq (lim f) = f
        sq _       = λ _ → zero

Q-ωω : Qh S.ω S.ω
Q-ωω = ω-refl seqω (qnat seqω refl (λ _ → refl))

Q-Ω : ∀ a → Qh (S.Ω a) (S.Ω a)
Q-Ω B.zero      = Q-ωω
Q-Ω (B.suc c)   = Qii (λ z z′ w → Q↑ʳ B.zero (Q↑ˡ B.zero w))
Q-Ω (B.lim f m) = Qll (λ n → Qlr n (Q↑ʳ (B.f<l n) (Q↑ˡ (B.f<l n) (Q-Ω (f n)))))

Q-one-Ω : ∀ {ℓ} a → Qh (one {ℓ}) (S.Ω a)
Q-one-Ω B.zero      = Qlr 1 (Qs Qz)
Q-one-Ω (B.suc c)   = Qb (inj₂ refl) (λ z′ w₁ w₂ → Q↑ʳ B.zero w₂) (λ z′ w → Q↑ʳ B.zero (Q-s→one w))
Q-one-Ω (B.lim f m) = Qlr 0 (Q↑ʳ (B.f<l 0) (Q-one-Ω (f 0)))

Ω-st : ∀ {c d} → c B.< d → Qh (suc (S.Ω c)) (S.Ω d)
Ω-st {c} B.zero      = Qb (inj₂ refl) (λ z′ w₁ w₂ → Q↑ʳ B.zero w₂) (λ z′ w → Q↑ʳ B.zero w)
Ω-st {c} (B.suc q)   = Qb (inj₁ q)    (λ z′ w₁ w₂ → Q↑ʳ B.zero w₂) (λ z′ w → Q↑ʳ B.zero w)
Ω-st {c} (B.lim n q) = Qlr n (Q↑ʳ (B.f<l n) (Ω-st q))
```

## §5 折叠

`gen`: 右边是 $\Omega_j$ 之上, 折叠不降到 $\Omega_j$ 以下. `one-ψ`: 输出非零. `Q-ψ`: 折叠保持 `Qh`. `S-ψ`: 折叠保持严格.

```agda
gen : ∀ {j ℓ′ ℓ} {a : S.Ord ℓ} → Qh a (S.Ω j) → (p : j B.< ℓ′) (w : S.Ord ℓ′) → Qh a (S.ψ< p w)
gen d p zero       = d
gen d p (suc w)    = Qlr 1 (gen d p w)
gen d p (lim g)    = Qlr 0 (gen d p (g 0))
gen d p (limᵢ q g) with B.<-dec q p
... | injᵃ j<i  = Qir (λ z′ → gen d p (g (S.coe {p = j<i} {q = q} (S.coe₀ {p = j<i} z′))))
... | injᵇ _    = Qlr 0 (gen d p (g (S.coe₀ {p = q} zero)))
... | injᶜ refl = Qlr 1 (gen d p (g (S.coe₀ {p = q} zero)))

one-ψ : ∀ {j ℓ′ ℓ} (p : j B.< ℓ′) (w : S.Ord ℓ′) → Qh (one {ℓ}) (S.ψ< p w)
one-ψ {j} = gen (Q-one-Ω j)

B1 : ∀ {j ℓ′} (p : j B.< ℓ′) (w : S.Ord ℓ′) → Qh (S.Ω j) (S.ψ< p w)
B1 {j} = gen (Q-Ω j)

Q-ψ′ : ∀ {i₁ i k ℓ₁} {x : S.Ord ℓ₁} {y : S.Ord k} → i₁ ≡ i → (p₁ : i₁ B.< ℓ₁) (p : i B.< k) → Qh x y → Qh (S.ψ< p₁ x) (S.ψ< p y)
S-ψ : ∀ {i k ℓ₁} {u : S.Ord ℓ₁} {v : S.Ord k} (p₁ : i B.< ℓ₁) (p : i B.< k) → Qh (suc u) v → Qh (suc (S.ψ< p₁ u)) (S.ψ< p v)

Bt : ∀ {c j ℓ′} → Lev c j → (p : j B.< ℓ′) (w : S.Ord ℓ′) → Qh (one {B.zero}) w → Qh (suc (S.Ω c)) (S.ψ< p w)
Bt (inj₁ q)    p w d = gen (Ω-st q) p w
Bt (inj₂ refl) p w d = S-ψ B.zero p (Q-one-conv d)

chain2 : ∀ {j k c} {q : j B.< k} {g : S.Ord< j q → S.Ord k} (r : j B.< k) → Lev c j →
         (∀ (z′ : S.Ord j) → Q< j q (S.coe₀ {p = q} z′) (S.Ω j) → Q< j q (S.coe₀ {p = q} z′) (suc (zero {ℓ = B.zero})) →
            Qh (suc (zero {ℓ = B.zero})) (g (S.coe₀ {p = q} z′))) →
         Qh (suc (S.Ω c)) (S.ψ< r (g (S.coe₀ {p = q} (S.ψ< r (g (S.coe₀ {p = q} zero))))))
chain2 {q = q} {g = g} r c nz = Bt c r _ (nz _ (Q→Q< q (B1 r _)) (Q→Q< q (one-ψ r _)))

chainQ : ∀ {j k ℓ₁} {q₁ : j B.< ℓ₁} {q : j B.< k} {f : S.Ord< j q₁ → S.Ord ℓ₁} {g : S.Ord< j q → S.Ord k}
         (r₁ : j B.< ℓ₁) (r : j B.< k) →
         (∀ (z z′ : S.Ord j) → Q< j q (S.coe₀ {p = q} z′) z → Qh (f (S.coe₀ {p = q₁} z)) (g (S.coe₀ {p = q} z′))) →
         ∀ n → Qh (iter (λ x → S.ψ< r₁ (f (S.coe₀ {p = q₁} x))) zero n) (iter (λ x → S.ψ< r (g (S.coe₀ {p = q} x))) zero n)
chainQ r₁ r h zero = Qz
chainQ {q₁ = q₁} {q = q} {f = f} {g = g} r₁ r h (suc n) =
  Q-ψ′ refl r₁ r (h _ _ (Q→Q< q (chainQ {q₁ = q₁} {q = q} {f = f} {g = g} r₁ r h n)))

Q-ψ′ refl p₁ p Qz = B1 p _
Q-ψ′ E p₁ p (Qs d)    = Qll (λ n → Qlr n (iter-Q (Q-ψ′ E p₁ p d) n))
Q-ψ′ E p₁ p (Qsr d)   = Qlr 1 (Q-ψ′ E p₁ p d)
Q-ψ′ E p₁ p (Qll h)   = Qll (λ n → Q-ψ′ E p₁ p (h n))
Q-ψ′ E p₁ p (Qlr n d) = Qlr n (Q-ψ′ E p₁ p d)
Q-ψ′ E p₁ p (Qir {q = q} {g = g} h) with B.<-dec q p
... | injᵃ j<i  = Qir (λ z′ → subst (λ v → Qh _ (S.ψ< p (g v))) (sym (coe-coe₀ j<i q z′)) (Q-ψ′ E p₁ p (h z′)))
... | injᵇ _    = Qlr 0 (Q-ψ′ E p₁ p (h zero))
... | injᶜ refl = Qlr 1 (Q-ψ′ E p₁ p (h zero))
Q-ψ′ E p₁ p (Qb {q = q} {g = g} c nz h) with B.<-dec q p
... | injᵃ j<i  = Qb c
      (λ z′ w₁ w₂ → one-ψ p _)
      (λ z′ w → subst (λ v → Qh _ (S.ψ< p (g v))) (sym (coe-coe₀ j<i q z′)) (Q-ψ′ E p₁ p (h z′ (Q→Q< q (Q<→Q j<i w)))))
... | injᵇ _    = Qlr 2 (Q-ψ′ E p₁ p (h _ (Q→Q< q (chain2 {q = q} {g = g} q c nz))))
... | injᶜ refl = Qlr 3 (Q-ψ′ E p₁ p (h _ (Q→Q< q (chain2 {q = q} {g = g} p c nz))))
Q-ψ′ E p₁ p (Qii {q₁ = q₁} {q = q} {f = f} {g = g} h) with B.<-dec q₁ p₁ | B.<-dec q p
... | injᵃ a | injᵃ b = Qii (λ z z′ w →
       subst₂ (λ u v → Qh (S.ψ< p₁ (f u)) (S.ψ< p (g v))) (sym (coe-coe₀ a q₁ z)) (sym (coe-coe₀ b q z′))
              (Q-ψ′ E p₁ p (h z z′ (Q→Q< q (Q<→Q b w)))))
... | injᵃ a | injᵇ b    = ⊥-elim (clash-lt (subst (_ B.<_) E a) b)
... | injᵃ a | injᶜ refl = ⊥-elim (<ᴰ-irrefl (subst (_ B.<_) E a))
... | injᵇ a | injᵃ b    = ⊥-elim (clash-lt (subst (B._< _) E a) b)
... | injᶜ refl | injᵃ b = ⊥-elim (<ᴰ-irrefl (subst (_ B.<_) (sym E) b))
... | injᵇ _ | injᵇ _    = Qll (λ n → Qlr n (Q-ψ′ E p₁ p (h _ _ (Q→Q< q (chainQ {q₁ = q₁} {q = q} {f = f} {g = g} q₁ q h n)))))
... | injᵇ _ | injᶜ refl = Qll (λ n → Qlr (suc n) (Q-ψ′ E p₁ p (h _ _ (Q→Q< q (chainQ {q₁ = q₁} {q = q} {f = f} {g = g} q₁ p h n)))))
... | injᶜ refl | injᵇ _ = Qll (λ where
        zero    → Qz
        (suc n) → Qlr n (Q-ψ′ E p₁ p (h _ _ (Q→Q< q (chainQ {q₁ = q₁} {q = q} {f = f} {g = g} p₁ q h n)))))
... | injᶜ refl | injᶜ refl = Qll (λ n → Qlr n (chainQ {q₁ = q₁} {q = q} {f = f} {g = g} p₁ p h n))

S-ψ {v = suc b} p₁ p (Qs d)  = Qlr 2 (Q-add (Q-ψ′ refl p₁ p d) (one-ψ p b))
S-ψ p₁ p (Qsr d)   = Qlr 1 (S-ψ p₁ p d)
S-ψ p₁ p (Qlr n d) = Qlr n (S-ψ p₁ p d)
S-ψ p₁ p (Qir {q = q} {g = g} h) with B.<-dec q p
... | injᵃ j<i  = Qir (λ z′ → subst (λ v → Qh _ (S.ψ< p (g v))) (sym (coe-coe₀ j<i q z′)) (S-ψ p₁ p (h z′)))
... | injᵇ _    = Qlr 0 (S-ψ p₁ p (h zero))
... | injᶜ refl = Qlr 1 (S-ψ p₁ p (h zero))
S-ψ p₁ p (Qb {q = q} {g = g} c nz h) with B.<-dec q p
... | injᵃ j<i  = Qb c
      (λ z′ w₁ w₂ → one-ψ p _)
      (λ z′ w → subst (λ v → Qh _ (S.ψ< p (g v))) (sym (coe-coe₀ j<i q z′)) (S-ψ p₁ p (h z′ (Q→Q< q (Q<→Q j<i w)))))
... | injᵇ _    = Qlr 2 (S-ψ p₁ p (h _ (Q→Q< q (chain2 {q = q} {g = g} q c nz))))
... | injᶜ refl = Qlr 3 (S-ψ p₁ p (h _ (Q→Q< q (chain2 {q = q} {g = g} p c nz))))

Q-ψ : ∀ {i k ℓ₁} {x : S.Ord ℓ₁} {y : S.Ord k} (p₁ : i B.< ℓ₁) (p : i B.< k) → Qh x y → Qh (S.ψ< p₁ x) (S.ψ< p y)
Q-ψ = Q-ψ′ refl
```
