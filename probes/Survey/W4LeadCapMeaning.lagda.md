# 将前缀上的反复右加还原为正层指数

第四层。把运算解释为右加一个一级参数。一级参数的 ω 次乘法在前缀上成为迭代，同一计算用两次便得到第二个正层指数的精确展开。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadCapMeaning where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
import OCF.Align.Level as L
open import WVOne using (T₀)
open import WVTwo using (T₁)
open import WSLevel using (Ω₁ᴸ)
open import YiLAB7Replay using (Ω₂ᴸ)
import B12LimitSrc as M
import B12Omega3Ref as R
import B13Target as P
import B15RefAlgebra as A
import B17RefExp as E
import Survey.W4LeadCapPrograms as J

append : ∀ {k k′} {c : L.Ordᶜ k} {d : L.Ordᶜ k′} {a b : M.Lev₂} {u : T₁}
  (σ : L.Simᴵ k (L.suc (L.suc L.zero))) (τ : L.Simᴵ k′ (L.suc L.zero)) →
  a L.≅ L.add b L.suc u → c L.≅ d → L.add a σ c L.≅ L.add b L.suc (L.add u τ d)
append σ τ e L.z≅ = e
append σ τ e (L.s≅ d) = L.s≅ (append σ τ e d)
append σ τ e (L.l≅ d) = L.l≅ (λ n → append σ τ e (d n))
append σ τ e (L.upˡ {r = L.zero} d) = append (λ p → σ (L.suc p)) τ e d
append σ τ e (L.upˡ {r = L.self n} d) = append (λ p → σ (L.lim n p)) τ e d
append σ τ e (L.upʳ {r = L.zero} d) = append σ (λ p → τ (L.suc p)) e d
append σ τ e (L.upʳ {r = L.self n} d) = append σ (λ p → τ (L.lim n p)) e d
append {a = a} {b} {u} σ τ e (L.lᵢ≅ {p = p} {q} {f} {g} h parts) = L.lᵢ≅ h (λ x y d → go x y d)
  where
  rp = L.<→◃ (σ p)
  rq = L.<→◃ (τ q)
  ro = L.<→◃ (L.suc (τ q))
  go : ∀ x y (d : L.R _ rp (L.into rp x) y) →
    L.add a σ (f (L.coe rp (L.<→◃ p) (L.into rp x))) L.≅
    L.add b L.suc (L.add u τ (g (L.coe rq (L.<→◃ q) (L.coe ro rq (L.into ro y)))))
  go x y d rewrite L.out-into rp x | L.out-into ro y | L.out-into rq y =
    append σ τ e (parts x y (L.R-conv rp (L.<→◃ p) d))

Adds : J.Op → T₁ → Set
Adds f u = ∀ {p q : M.Lev₂} → p L.≅ q → f p L.≅ L.add q L.suc u

after : ∀ {V : Set} (f : V → V) p n → J.iter f p (suc n) ≡ J.iter f (f p) n
after f p zero = refl
after f p (suc n) = cong f (after f p n)

module Count {f u} (h : Adds f u) (r : u L.≅ u) where
  seq = J.iter (u L.+_) L.zero
  eq : ∀ n → Adds (λ p → J.iter f p n) (seq n)
  eq zero d = d
  eq (suc n) {p} {q} d rewrite after f p n =
    L.≅-trans (eq n (h d)) (append L.suc (λ t → t) (L.add-≅ {σ = L.suc} {σ′ = L.suc} (P.refl-left (L.≅-sym d)) r)
      (L.iter-R L._≅_ {G = u L.+_} {G′ = u L.+_} (L.add-≅ {σ = λ t → t} {σ′ = λ t → t} r) L.z≅ n))
  pow : Adds (λ p → L.lim (J.iter f p)) (A.power u)
  pow d = L.l≅ (λ n → eq n d)

sum : ∀ {x y : T₀} → x L.≅ y → ∀ {f u} → Adds f u → u L.≅ u → Adds (J.sum f x) (A.E₀ u y)
sum L.z≅ h r = h
sum (L.s≅ {b = y} d) {f} {u} h r = Count.pow (sum d {f} h r) (E.small r (L.≅-refl⁰ y))
sum (L.l≅ ds) {f} h r p = L.l≅ λ n → sum (ds n) {f} h r p

wide : ∀ {f u} → Adds f u → u L.≅ u → Adds (J.wide f) (A.E u Ω₁ᴸ)
wide {f} h r p = L.lᵢ≅ L.z≅ λ x y d → sum d {f} h r p

module Power {k : J.Op → J.Op} {b : T₁} (b-ok : b L.≅ b)
  (step : ∀ {f u} → Adds f u → u L.≅ u → Adds (k f) (A.E u b)) where
  seq = J.iter (b L.+_) L.zero
  regular : ∀ n → seq n L.≅ seq n
  regular = L.iter-R L._≅_ {G = b L.+_} {G′ = b L.+_} (L.add-≅ {σ = λ t → t} {σ′ = λ t → t} b-ok) L.z≅
  eq : ∀ n {f u} → Adds f u → u L.≅ u → Adds (J.iter k f n) (A.E u (seq n))
  eq zero h r = h
  eq (suc n) {f} {u} h r {p} {q} d rewrite after k f n =
    L.≅-trans (eq n {k f} (step {f} h r) (E.wide r b-ok) d)
      (L.add-≅ {σ = L.suc} {σ′ = L.suc} (P.refl-left (L.≅-sym d))
        (E.Shift.compose u b (A.E u b) (E.wide r b-ok) (regular n)))

higher : ∀ {x y : T₀} → x L.≅ y → ∀ {f u} → Adds f u → u L.≅ u →
  Adds (J.higher x f) (A.E u (A.E₀ Ω₁ᴸ y))
higher L.z≅ {f} h r = wide {f} h r
higher (L.s≅ {a = x} {b = y} d) {f} {u} h r e = L.l≅ (λ n → Chain.eq n {f} h r e)
  where module Chain = Power {J.higher x} {A.E₀ Ω₁ᴸ y}
          (E.small (L.Ω-refl _) (L.≅-refl⁰ y)) (λ {z} {w} a b → higher d {z} a b)
higher (L.l≅ ds) {f} h r e = L.l≅ λ n → higher (ds n) {f} h r e

roof : J.roof J.base Ω₂ᴸ L.≅ L.add Ω₂ᴸ L.suc (A.E Ω₁ᴸ (A.E Ω₁ᴸ Ω₁ᴸ))
roof = L.lᵢ≅ L.z≅ (λ x y d → higher d {J.base} {Ω₁ᴸ} (λ p → L.add-≅ {σ = L.suc} {σ′ = L.suc} p (L.Ω-refl _)) (L.Ω-refl _) (L.Ω-refl _))
```
