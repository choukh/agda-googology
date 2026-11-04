# src 对角线的严格性

> 接 [BTBOFullQ](BTBOFullQ.lagda.md). 定理 `St-x`: 对一切 $k$, `St (tr₀ (ψⁿ k))`. 也就是 src 的 $x_k$ 里每个 `lim` 的相邻项值严格递增. 这条之前只有纸面判断.
>
> `Gs` 是 `Uniform` 的 `Good` 在 src 族上的严格版: `lim` 步进严格, `limᵢ` 的分支单调且严格单调. 对 $\Omega$, `+`, `↑`, `ψ<` 封闭. 层号 `Ordᴰ` 字面严格, 所以 `Ω (lim f _)` 的步进直接来自 `Ω-st`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOFullSt where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; module Trich; injᵃ; injᵇ; injᶜ)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ)
open S using (iter; ordᴰ; ψⁿ; zero; suc; lim; limᵢ)
open import OCF.Align.BTBOValBase using (tr₀; fd)
open import OCF.Align.BTBOValDn using (coe-coe₀)
open import OCF.Align.BTBOValAbsorb using (St; stz; sts; stl; absorb; P)
open import OCF.Align.Value using (_≼_)
open import OCF.Align.BTBOFullQ hiding (module S; module B)
```

## §1 谓词

```agda
module _ (k : Ordᴰ) (G< : (i : Ordᴰ) (p : i B.< k) → S.Ord< i p → Set) where
  data G₊ : S.Ord k → Set where
    gz : G₊ zero
    gs : ∀ {a} → G₊ a → G₊ (suc a)
    gl : ∀ {h : ℕ → S.Ord k} → (∀ n → G₊ (h n)) → (∀ n → Qh (suc (h n)) (h (suc n))) → G₊ (lim h)
    gi : ∀ {j} {q : j B.< k} {f : S.Ord< j q → S.Ord k} →
         (∀ (z : S.Ord j) → G< j q (S.coe₀ {p = q} z) → G₊ (f (S.coe₀ {p = q} z))) →
         (∀ (z z′ : S.Ord j) → Q< j q (S.coe₀ {p = q} z′) z → Qh (f (S.coe₀ {p = q} z)) (f (S.coe₀ {p = q} z′))) →
         (∀ (z z′ : S.Ord j) → Q< j q (S.coe₀ {p = q} z′) (suc z) → Qh (suc (f (S.coe₀ {p = q} z))) (f (S.coe₀ {p = q} z′))) →
         G₊ (limᵢ q f)

G< : ∀ {k} (i : Ordᴰ) (p : i B.< k) → S.Ord< i p → Set
G< i B.zero      y = G₊ i G< y
G< i (B.suc p)   y = G< i p y
G< i (B.lim n p) y = G< i p y

Gs : ∀ {k} → S.Ord k → Set
Gs {k} = G₊ k G<

G<→G : ∀ {i k} (p : i B.< k) {y : S.Ord i} → G< i p (S.coe₀ {p = p} y) → Gs y
G<→G B.zero      d = d
G<→G (B.suc p)   d = G<→G p d
G<→G (B.lim n p) d = G<→G p d

G→G< : ∀ {i k} (p : i B.< k) {y : S.Ord i} → Gs y → G< i p (S.coe₀ {p = p} y)
G→G< B.zero      d = d
G→G< (B.suc p)   d = G→G< p d
G→G< (B.lim n p) d = G→G< p d
```

## §2 封闭

```agda
Q-refl : ∀ {k} {x : S.Ord k} → Gs x → Qh x x
Q-refl gz        = Qz
Q-refl (gs g)    = Qs (Q-refl g)
Q-refl (gl h s)  = Qll (λ n → Qlr n (Q-refl (h n)))
Q-refl (gi h m s) = Qii m

G-↑ : ∀ {k k′} (r : k B.< k′) {x : S.Ord k} → Gs x → Gs (S.↑ r x)
G-↑ r gz       = gz
G-↑ r (gs g)   = gs (G-↑ r g)
G-↑ r (gl h s) = gl (λ n → G-↑ r (h n)) (λ n → Q↑ʳ r (Q↑ˡ r (s n)))
G-↑ r (gi {q = q} {f = f} h m st) = gi
  (λ z g → subst (λ u → Gs (S.↑ r (f u))) (sym (coe-coe₀ (B.<-trans q r) q z))
                 (G-↑ r (h z (G→G< q (G<→G (B.<-trans q r) g)))))
  (λ z z′ w → subst₂ (λ u v → Qh (S.↑ r (f u)) (S.↑ r (f v))) (sym (coe-coe₀ (B.<-trans q r) q z)) (sym (coe-coe₀ (B.<-trans q r) q z′))
                 (Q↑ʳ r (Q↑ˡ r (m z z′ (Q→Q< q (Q<→Q (B.<-trans q r) w))))))
  (λ z z′ w → subst₂ (λ u v → Qh (suc (S.↑ r (f u))) (S.↑ r (f v))) (sym (coe-coe₀ (B.<-trans q r) q z)) (sym (coe-coe₀ (B.<-trans q r) q z′))
                 (Q↑ʳ r (Q↑ˡ r (st z z′ (Q→Q< q (Q<→Q (B.<-trans q r) w))))))

G-ω : (g : ℕ → S.Ord₀) → g 0 ≡ zero → (∀ n → g (suc n) ≡ suc (g n)) → Gs (lim g)
G-ω g g0 gs′ = gl good step
  where
  good : ∀ n → Gs (g n)
  good zero    = subst Gs (sym g0) gz
  good (suc n) = subst Gs (sym (gs′ n)) (gs (good n))
  step : ∀ n → Qh (suc (g n)) (g (suc n))
  step n = subst (λ u → Qh (suc (g n)) u) (sym (gs′ n)) (Qs (Q-refl (good n)))

G-Ω : ∀ a → Gs (S.Ω a)
G-Ω B.zero      = G-ω seqω refl (λ _ → refl)
G-Ω (B.suc c)   = gi (λ z g → G-↑ B.zero g) (λ z z′ w → Q↑ʳ B.zero (Q↑ˡ B.zero w)) (λ z z′ w → Q↑ʳ B.zero (Q↑ˡ B.zero w))
G-Ω (B.lim f m) = gl (λ n → G-↑ (B.f<l n) (G-Ω (f n)))
                     (λ n → Q↑ʳ (B.f<l (suc n)) (Q↑ˡ (B.f<l n) (Ω-st (m Trich.zero))))

G-add : ∀ {k} {a b : S.Ord k} → Gs a → Gs b → Gs (a S.+ b)
G-add ga gz       = ga
G-add ga (gs g)   = gs (G-add ga g)
G-add ga (gl h s) = gl (λ n → G-add ga (h n)) (λ n → Q-add (Q-refl ga) (s n))
G-add ga (gi h m st) = gi (λ z g → G-add ga (h z g))
                          (λ z z′ w → Q-add (Q-refl ga) (m z z′ w))
                          (λ z z′ w → Q-add (Q-refl ga) (st z z′ w))

G-iter : ∀ {k} {A : S.Ord k} → Gs A → ∀ n → Gs (iter (A S.+_) zero n)
G-iter gA zero    = gz
G-iter gA (suc n) = G-add gA (G-iter gA n)

rule4 : ∀ {k} {A : S.Ord k} → Gs A → Qh (suc (zero {ℓ = k})) A → ∀ n → Qh (suc (iter (A S.+_) zero n)) (iter (A S.+_) zero (suc n))
rule4 gA o zero    = o
rule4 gA o (suc n) = Q-add (Q-refl gA) (rule4 gA o n)

G-ψ : ∀ {i k} (p : i B.< k) {x : S.Ord k} → Gs x → Gs (S.ψ< p x)

chain-good : ∀ {j k} {q : j B.< k} {f : S.Ord< j q → S.Ord k} (r : j B.< k) →
             (∀ (z : S.Ord j) → G< j q (S.coe₀ {p = q} z) → Gs (f (S.coe₀ {p = q} z))) →
             ∀ n → Gs (iter (λ x → S.ψ< r (f (S.coe₀ {p = q} x))) zero n)
chain-good r h zero = gz
chain-good {q = q} {f = f} r h (suc n) = G-ψ r (h _ (G→G< q (chain-good {q = q} {f = f} r h n)))

chain-step : ∀ {j k} {q : j B.< k} {f : S.Ord< j q → S.Ord k} (r : j B.< k) →
             (∀ (z z′ : S.Ord j) → Q< j q (S.coe₀ {p = q} z′) (suc z) → Qh (suc (f (S.coe₀ {p = q} z))) (f (S.coe₀ {p = q} z′))) →
             ∀ n → Qh (suc (iter (λ x → S.ψ< r (f (S.coe₀ {p = q} x))) zero n)) (iter (λ x → S.ψ< r (f (S.coe₀ {p = q} x))) zero (suc n))
chain-step r st zero = one-ψ r _
chain-step {q = q} {f = f} r st (suc n) = S-ψ r r (st _ _ (Q→Q< q (chain-step {q = q} {f = f} r st n)))

G-ψ {i} p gz = G-Ω i
G-ψ p (gs {a} g)  = gl (G-iter (G-ψ p g)) (rule4 (G-ψ p g) (one-ψ p a))
G-ψ p (gl h s)    = gl (λ n → G-ψ p (h n)) (λ n → S-ψ p p (s n))
G-ψ p (gi {q = q} {f = f} h m st) with B.<-dec q p
... | injᵃ j<i = gi
      (λ z g → subst (λ u → Gs (S.ψ< p (f u))) (sym (coe-coe₀ j<i q z)) (G-ψ p (h z (G→G< q (G<→G j<i g)))))
      (λ z z′ w → subst₂ (λ u v → Qh (S.ψ< p (f u)) (S.ψ< p (f v))) (sym (coe-coe₀ j<i q z)) (sym (coe-coe₀ j<i q z′))
                  (Q-ψ p p (m z z′ (Q→Q< q (Q<→Q j<i w)))))
      (λ z z′ w → subst₂ (λ u v → Qh (suc (S.ψ< p (f u))) (S.ψ< p (f v))) (sym (coe-coe₀ j<i q z)) (sym (coe-coe₀ j<i q z′))
                  (S-ψ p p (st z z′ (Q→Q< q (Q<→Q j<i w)))))
... | injᵇ _ = gl (λ n → G-ψ p (h _ (G→G< q (chain-good {q = q} {f = f} q h n))))
                  (λ n → S-ψ p p (st _ _ (Q→Q< q (chain-step {q = q} {f = f} q st n))))
... | injᶜ refl = gl (chain-good {q = q} {f = f} p h) (chain-step {q = q} {f = f} p st)
```

## §3 对角线

```agda
G→St : ∀ {x : S.Ord₀} → Gs x → St (tr₀ x)
G→St gz       = stz
G→St (gs g)   = sts (G→St g)
G→St (gl h s) = stl (λ n → G→St (h n)) (λ n → Q→≼ (s n))
G→St (gi {q = ()} h m st)

G-ψ₀ : ∀ a → Gs (S.ψ₀ (S.Ω a))
G-ψ₀ B.zero      = G-Ω B.zero
G-ψ₀ (B.suc a)   = G-ψ (B.z<nz _) (G-Ω (B.suc a))
G-ψ₀ (B.lim f m) = G-ψ (B.z<nz _) (G-Ω (B.lim f m))

G-x : ∀ k → Gs (ψⁿ k)
G-x zero    = gz
G-x (suc k) = G-ψ₀ (ordᴰ (ψⁿ k))

St-x : ∀ k → St (tr₀ (ψⁿ k))
St-x k = G→St (G-x k)

absorb-x : ∀ k → fd (ordᴰ (ψⁿ k)) ≼ P (tr₀ (suc (ψⁿ k)))
absorb-x k = absorb (ψⁿ k) (St-x k)
```
