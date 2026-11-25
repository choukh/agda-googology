# 任意正有限层的一次自身返回

第四层验收。自身槽的底取任意正整数，输入取 1。旧折叠和 W4 的 `ex` 返回交给外层真实折叠后取同一序数值。两边的基本列相差一项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseBridgeSelf where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Unit.Base using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≅→≼; ⊑→≼; ≼-trans; ≼l; l≼)
import OCF.Align.Level as L
import OCF.Lean.YiLegBlock as O
import OCF.Lean.YiLegOps as A
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLegFold as G
import OCF.Lean.YiLSRead as V
import W4Block as W
import W4Ops as U
import W4Path as Q
import W4Fold as F
import WVOne as R
open import Survey.W4FiniteRaiseBridge using (ol; wl; wp; Same; rl; same-it; read-same)

on : ∀ {d} → ℕ → O.Tr d
on zero = O.zero
on (suc n) = O.suc (on n)

wn : ∀ {d} → ℕ → W.Tr d
wn zero = W.zero
wn (suc n) = W.suc (wn n)

shift : ℕ → ℕ → ℕ → ℕ
shift m zero i = i
shift m (suc k) i = m + shift m k i

add-on : ∀ {d} m k → on {d} m A.+ on k ≡ on (k + m)
add-on m zero = refl
add-on m (suc k) = cong O.suc (add-on m k)

copies : ∀ {d} m k → A.iter (on {d} m A.+_) (on m) k ≡ on (shift m k m)
copies m zero = refl
copies {d} m (suc k) = trans (cong (on {d} m A.+_) (copies m k))
  (trans (add-on m (shift m k m)) (cong on (+-comm (shift m k m) m)))

module At (n m : ℕ) (ε : P.Ev (ol (suc n))) (ρ : P.Rt (ol (suc n))) (B : G.Base (ol (suc n)))
          (o : Q.Ok (wl (suc n))) (D : F.Base (wl (suc n))) (β : U.Tr⁺ W.zero)
          (start : Same (G.b⊥ B) (proj₁ β)) where
  j = ol (suc n)
  ℓ = wl (suc n)
  p = wp (suc n)
  b = suc m

  observe = G.ψ⊥ j ε ρ B
  native = F.ψ ℓ o D W.zero p β

  old₊ : (k : ℕ) → j O.⊢ O.zero ◃ on (suc k)
  old₊ k = A.z◃s (on k)
  new₊ : (k : ℕ) → ℓ W.⊢ W.zero ◃ wn (suc k)
  new₊ k = U.z◃ (wn k) W.◃s

  old-return = G.ψs j ε ρ B j P.self (on b) (old₊ m) (on 1)
  new-return = proj₁ (F.ψ ℓ o D ℓ W.self (wn b , new₊ m) (wn 1))
  worker = F.opB ℓ o (wn b) (new₊ m)
  state = λ i u → F.ψ ℓ o D i u (D i u) (wn b)
  base = native (wn b)

  extend : ∀ t i (S : F.Base ℓ) (v : U.Tr⁺ W.zero) → Same (observe (on i)) (proj₁ v) →
           Same (observe (on (t + i))) (proj₁ (F.ψ ℓ o S W.zero p v (wn t)))
  extend zero i S v h = h
  extend (suc t) i S v h = rl (same-it (extend t i S v h))

  initial : ∀ t → Same (observe (on t)) (proj₁ (native (wn t)))
  initial zero = start
  initial (suc t) = rl (same-it (initial t))

  iterate : ∀ k i (S : F.Base ℓ) (v : U.Tr⁺ W.zero) → Same (observe (on i)) (proj₁ v) →
            Same (observe (on (shift b k i))) (proj₁ (F.itV worker k S W.zero p v))
  iterate zero i S v h = h
  iterate (suc k) i S v h = extend b (shift b k i) (F.itS worker k S)
    (F.itV worker k S W.zero p v) (iterate k i S v h)

  old-branch = λ k → observe (A.iter (on b A.+_) (on b) k)
  new-branch = λ k → proj₁ (F.itV worker (suc k) state W.zero p base)

  aligned : ∀ k → Same (old-branch (suc k)) (new-branch k)
  aligned k rewrite copies {j} b (suc k) = iterate (suc k) b state base (initial b)

  strict-at : ∀ k → V.read (old-branch k) L.≺ R.read (new-branch k)
  strict-at k = L.≺-respʳ (V.◃→≺ (G.mono⊥ j ε ρ B (A.nextA (on b) (old₊ m) k)))
    (read-same (aligned k))

  value : V.read (observe old-return) ≈ᵛ R.read (proj₁ (native new-return))
  value = l≼ lower , l≼ (λ k → ≼l (suc k) (≅→≼ (L.≅-sym (read-same (aligned k)))))
    where
    lower : ∀ k → V.read (old-branch k) ≼ R.read (proj₁ (native new-return))
    lower zero = ≼l 0 (≼-trans (⊑→≼ (V.read (old-branch 0)) {V.read (old-branch 1)} (V.◃⊑ (G.mono⊥ j ε ρ B (A.nextA (on b) (old₊ m) zero))))
                               (≅→≼ (read-same (aligned 0))))
    lower (suc k) = ≼l k (≅→≼ (read-same (aligned k)))
```
