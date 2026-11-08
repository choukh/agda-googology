# 稳定采样关系的加法闭包

加法左端携带两侧VRel自证。context情形用带关系的结合律重排，
不使用函数外延，也不把任意Same送过fold。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformUpperStableAdd where
open import Data.Nat using (zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul)
open import OCF.Align.BoundedCompletionTerminalValueIf
open import OCF.Align.BoundedCompletionTerminalValueClosure using (add-rel; floor; floor-self)
open import OCF.Align.UniformUpperStableIf

nested : ∀ {a a′ b b′} → VRel a a′ → VRel b b′ → ∀ d → VRel (a ⊞ b) (a′ ⊞ (b′ ⊞ d))
nested p q hz = add-rel p q
nested p q (hs d) = vr (nested p q d)
nested p q (hl f) = vli 0 (nested p q (f 0))
nested p q (hΩ (inj₁ ()) g)
nested p q (hΩ (inj₂ _) g) = vor (λ c → nested p q (g c))

associate : ∀ {a a′ b b′ c c′} → VRel a a′ → VRel b b′ → VRel c c′ →
  VRel ((a ⊞ b) ⊞ c) (a′ ⊞ (b′ ⊞ c′))
associate p q {-(c)-} vz = nested p q _
associate p q (vs r) = vs (associate p q r)
associate p q (vr r) = vr (associate p q r)
associate p q (vl r) = vl (λ n → associate p q (r n))
associate p q (vli n r) = vli n (associate p q r)
associate p q (vo r) = vo (λ e → associate p q (r e))
associate p q (vor r) = vor (λ c → associate p q (r c))

pad : ∀ {a b} → Core a b → ∀ c → Core a (b ⊞ c)
pad p hz = p
pad p (hs c) = right (pad p c)
pad p (hl f) = pick 0 (pad p (f 0))
pad p (hΩ (inj₁ ()) g)
pad p (hΩ (inj₂ _) g) = uniform (λ c → pad p (g c))

add-v : ∀ {a b c d} → Core a b → VRel c d → Core (a ⊞ c) (b ⊞ d)
add-v p vz = pad p _
add-v p (vs q) = succ (add-v p q)
add-v p (vr q) = right (add-v p q)
add-v p (vl q) = all (λ n → add-v p (q n))
add-v p (vli n q) = pick n (add-v p q)
add-v p (vo q) = omega (λ r → add-v p (q r))
add-v p (vor q) = uniform (λ c → add-v p (q c))

add : ∀ {a b c d} → VRel a a → VRel b b → Core a b → Core c d → Core (a ⊞ c) (b ⊞ d)
add aa bb p (lift q) = add-v p q
add aa bb p unit = context p bb
add aa bb p (succ q) = succ (add aa bb p q)
add aa bb p (right q) = right (add aa bb p q)
add aa bb p (all q) = all (λ n → add aa bb p (q n))
add aa bb p (pick n q) = pick n (add aa bb p q)
add aa bb p (omega q) = omega (λ r → add aa bb p (q r))
add aa bb p (uniform q) = uniform (λ c → add aa bb p (q c))
add aa bb p (context q dd) = through (add-rel (add-rel bb dd) floor-self)
  (context (add aa bb p q) (add-rel bb dd))
  (lift (associate bb dd floor-self))
add aa bb p (through dd q r) = through (add-rel bb dd)
  (add aa bb p q) (add bb bb (lift bb) r)

multiple : ∀ {a b} → VRel a a → VRel b b → Core a b → ∀ n → Core (mul a n) (mul b n)
multiple aa bb p zero = p
multiple aa bb p (suc n) = add (self-mul aa n) (self-mul bb n) (multiple aa bb p n) p
  where
  self-mul : ∀ {x} → VRel x x → ∀ n → VRel (mul x n) (mul x n)
  self-mul xx zero = xx
  self-mul xx (suc n) = add-rel (self-mul xx n) xx

repeated : ∀ {a b} → VRel a a → VRel b b → Core a b → Core (hl (mul a)) (hl (mul b))
repeated aa bb p = all (λ n → pick n (multiple aa bb p n))
```
