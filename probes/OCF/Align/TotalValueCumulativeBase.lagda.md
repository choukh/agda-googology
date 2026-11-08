# 错位回灌值证明的累计层基础

只为验收重基旧 BTBOFull 的分块吸收证明。Ordᴰ 来自原已发表程序；
本文件的读回逐字进入本轮 Free 层，不进入新闭项生产依赖。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueCumulativeBase where
open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Ord-Ord; module BoundedTrich; module Trich)
module S = Ord-Ord
module B = BoundedTrich
open import OCF.Align.OrdLabZLevel
open import OCF.Align.TotalValueBuildStrictBase public using (St; stz; sts; stl; s≼0)
open import OCF.Align.ValueJudgeBase

tr₀ : S.Ord₀ → Ordᶜ zero
tr₀ S.zero = zero
tr₀ (S.suc a) = suc (tr₀ a)
tr₀ (S.lim f) = lim (λ n → tr₀ (f n))
tr₀ (S.limᵢ () f)

τ : B.Ordᴰ → Ordᴵ
τ-< : ∀ {a b} → a B.< b → τ a <ᴵ τ b
<→⊑ᴵ : ∀ {a b} → a <ᴵ b → a ⊑ᴵ b
<→⊑ᴵ q = Sim→⊑ᴵ (λ c → <ᴵ-trans c q)
τ B.zero = zero
τ (B.suc a) = suc (τ a)
τ (B.lim f m) = lim (τ ∘ f) (λ n → <→⊑ᴵ (τ-< (m Trich.zero)))
τ-< B.zero = zero
τ-< (B.suc p) = suc (τ-< p)
τ-< (B.lim n p) = lim n (τ-< p)

via< : ∀ {a b} → a <ᴵ b → a ≺ᴵ b
via< q = via (≅ᴵ-refl _) q

st-s⁻ : ∀ {a} → St (suc a) → St a
st-s⁻ (sts p) = p
st-l₁ : ∀ {f} → St (lim f) → ∀ n → St (f n)
st-l₁ (stl p step) = p
st-l₂ : ∀ {f} → St (lim f) → ∀ n → suc (f n) ≼ f (suc n)
st-l₂ (stl p step) = step

lim-≼⁻ : ∀ {f : ℕ → Ordᶜ zero} {b : Ordᶜ zero} → lim f ≼ b → ∀ n → f n ≼ b
lim-≼⁻ (l≼ p) n = p n
lim-≼⁻ (≼l k p) n = ≼l k (lim-≼⁻ p n)
lim-≼⁻ (≼i {p = ()} x ex p) n
lim-≼⁻ (≼u {r = ()} p) n

add-≺ : ∀ (a : Ordᶜ zero) {c b : Ordᶜ zero} → c ≺ b → (a + c) ≺ (a + b)
add-≺ a (≺z e) = ≺z (add-≅ (≅-refl⁰ a) e)
add-≺ a (≺s p) = ≺s (add-≺ a p)
add-≺ a (≺l n p) = ≺l n (add-≺ a p)
add-≺ a (≺i {p = ()} x ex p)
add-≺ a (≺u {r = ()} p)

z≺ψ⁰ : ∀ {k} (x : Ordᶜ k) → (zero {ℓ = zero}) ≺ ψ⁰ x
z≺ψ⁰ zero = ≺z z≅
z≺ψ⁰ (suc a) = ≺l 1 (z≺ψ⁰ a)
z≺ψ⁰ (lim f) = ≺l 0 (z≺ψ⁰ (f 0))
z≺ψ⁰ (limᵢ q f) = ≺l 0 (z≺ψ⁰ (f (into (<→◃ q) (Ω _))))
z≺ψ⁰ (up zero x) = z≺ψ⁰ x
z≺ψ⁰ (up (self n) x) = z≺ψ⁰ x
```
