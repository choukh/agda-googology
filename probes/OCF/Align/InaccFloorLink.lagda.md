# 字面上界: 层号函数就是树的折叠

> 不含记号. `P̂` 不是另一个对象: `toLv (ψⁿ 1 x) ≈ P̂ (toLv x)` (`link`). 第 5 站的一致族在 $\theta=2$ 处的树 `F (natL 2)` 的层号就是 `Ψ₁Ω₂` (`link-F₂`), 对任何 `S`. 所以 [InaccFloorIter](InaccFloorIter.lagda.md) 的证书说的是树.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccFloorLink where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.InaccTreeBase hiding (_⊑_; _≺_; via)
open import OCF.Align.InaccFloorBase using (_≈_; z≈; s≈; l≈; o≈; ≈-refl; ≈-trans; ≈-sym; times; _⊞_)
open import OCF.Align.InaccFloorIter using (_⊕_; ≈⊕; rp; rp≈; L₁; P̂; P̂≈; Pit; Ψ₁Ω₂)
open import OCF.Align.InaccFloorTree

add0 : ∀ {ℓ} (a : Ordᴸ ℓ) (τ : Sim zero ℓ) (x : Ordᴸ zero) → toLv (add a τ x) ≈ (toLv a ⊕ toLv x)
add0 a τ zero    = ≈-refl _
add0 a τ (suc x) = s≈ (add0 a τ x)
add0 a τ (lim f) = l≈ (λ n → add0 a τ (f n))

add1 : (a b : Ordᴸ (natL 1)) → toLv (a + b) ≈ (toLv a ⊕ toLv b)
add1 a zero    = ≈-refl _
add1 a (suc b) = s≈ (add1 a b)
add1 a (lim f) = l≈ (λ n → add1 a (f n))
add1 a (limᵢ (inj₁ _) f) = o≈ (λ y → add1 a (f y))
add1 a (up _ x) = add0 a _ x

L₁≈ : toLv (Ω (natL 1)) ≈ L₁
L₁≈ = o≈ go where
  go : ∀ (x : Ordᴸ zero) → toLv x ≈ (zero ⊞ x)
  go zero    = z≈
  go (suc x) = s≈ (go x)
  go (lim f) = l≈ (λ n → go (f n))

module _ (S : Sib) where
  open PF S

  iter≈ : (M : Ordᴸ (natL 1)) → ∀ n → toLv (iter (M +_) zero n) ≈ rp (toLv M) n
  iter≈ M zero    = z≈
  iter≈ M (suc n) = ≈-trans (add1 M (iter (M +_) zero n)) (≈⊕ (≈-refl _) (iter≈ M n))

  link₀ : (x : Ordᴸ zero) → toLv (ψⁿ 1 x) ≈ P̂ (toLv x)
  link₀ zero    = L₁≈
  link₀ (suc x) = l≈ (λ n → ≈-trans (iter≈ (ψⁿ 1 x) n) (rp≈ (link₀ x) n))
  link₀ (lim f) = l≈ (λ n → link₀ (f n))

  link : (x : Ordᴸ (natL 1)) → toLv (ψⁿ 1 x) ≈ P̂ (toLv x)
  link zero    = L₁≈
  link (suc x) = l≈ (λ n → ≈-trans (iter≈ (ψⁿ 1 x) n) (rp≈ (link x) n))
  link (lim f) = l≈ (λ n → link (f n))
  link (limᵢ (inj₁ _) f) = o≈ (λ y → link (f y))
  link (up _ x) = link₀ x

  ch : ℕ → Ordᴸ (natL 1)
  ch = iter (λ x → ψᵖ (chM (natL 2) (inj₁ tt)) (up tt (intoL (natL 2) (inj₁ tt) x))) (Ω (natL 1))

  chk : ∀ n → toLv (ψⁿ 1 (ch n)) ≈ Pit n
  chk zero    = ≈-trans (link (Ω (natL 1))) (P̂≈ L₁≈)
  chk (suc n) = ≈-trans (link (ch (suc n))) (P̂≈ (chk n))

  link-F₂ : toLv (F (natL 2)) ≈ Ψ₁Ω₂
  link-F₂ = l≈ chk
```
