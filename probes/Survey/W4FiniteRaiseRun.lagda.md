# 实际有限层相邻两项的完整 Ω 输入

第四层。相邻有限层之间的任一合法路径，都把前层的完整输入送到后层同一个孩子。将此性质用于实际前缀的最后一项，可同时读出各层的自槽与低槽。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseRun where

open import Data.Nat.Base as N using (ℕ; zero; suc; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
import B13FiniteLift as Lift
import B13FiniteTower as Fin
import B12Terminal as T
import B12ActualSlots as Slots
import B12Strict as Strict
import OCF.Align.Level as L
open import WVOne using (T₀; read)
open import OCF.Align.Value using (_≼_)
import B31PPrefix as Prefix
import WKTower as Tower

fin : ℕ → W.L
fin zero = W.zero
fin (suc n) = Lift.sc (fin n)

depth : W.L → ℕ
depth W.zero = zero
depth (W.nd s h) = suc (depth (h (O.c₀ s)))

size : ∀ n → depth (fin n) ≡ n
size zero = refl
size (suc n) = cong suc (size n)

bounded : ∀ {k} n → k W.≤ fin n → depth k N.≤ n
bounded zero W.self = z≤n
bounded (suc n) W.self = subst (λ t → t N.≤ suc n) (sym (size (suc n))) NP.≤-refl
bounded (suc n) (W.inc tt v) = NP.m≤n⇒m≤1+n (bounded n v)
bounded (suc n) (W.inu vs) = NP.m≤n⇒m≤1+n (bounded n (vs tt))

no-down : ∀ n → fin (suc n) W.≤ fin n → ⊥
no-down n p = NP.1+n≰n (subst (λ t → t N.≤ n) (size (suc n)) (bounded n p))

diagonal : ∀ {a b} (w : a W.≤ b) n → a ≡ fin n → b ≡ fin n → (o : P.Ok b) →
  P.emb b o w (O.Ωt a) ≡ O.Ωt b
diagonal W.self n ea eb o = refl
diagonal (W.inc _ _) zero ea () o
diagonal (W.inu _) zero ea () o
diagonal (W.ink _) zero ea () o
diagonal (W.inc tt v) (suc n) refl refl o = ⊥-elim (no-down n v)
diagonal (W.inu vs) (suc n) refl refl o = ⊥-elim (no-down n (vs tt))

data LastInput (j : W.L) : (k : W.L) → W.Tr k → Set where
  child : LastInput j (Lift.sc j) (proj₁ (O.upz {s = W.sS} {h = λ _ → j} tt (O.Ωt j)))

adjacent : ∀ n {j k} → j ≡ fin n → k ≡ fin (suc n) → (o : P.Ok k) (w : j W.≤ k) →
  LastInput j k (proj₁ (P.emb k o w (O.Ωt j)))
adjacent n {j} {k} ej ek o w = go w ej ek
  where
  go : ∀ {a b} (v : a W.≤ b) → a ≡ fin n → (q : b ≡ fin (suc n)) →
    {u : P.Ok b} → LastInput a b (proj₁ (P.emb b u v (O.Ωt a)))
  go W.self refl q = ⊥-elim (NP.1+n≰n (subst (λ t → t N.≤ n) (trans (cong depth q) (size (suc n)))
    (bounded n W.self)))
  go (W.inc tt p) refl refl {u} rewrite diagonal p n refl refl (proj₂ u tt) = child
  go (W.inu vs) refl refl {u} rewrite diagonal (vs tt) n refl refl (proj₂ u tt) = child

tower-level : ∀ n → Tower.gL n ≡ fin (suc n)
tower-level zero = refl
tower-level (suc n) = trans (Fin.succ-level n) (cong Lift.sc (tower-level n))

into : ∀ {j k x} → LastInput j k x → ∀ {i} → i W.≤ j → i W.≤ k
into child w = W.inc tt w

child-ok : ∀ {j k x} → LastInput j k x → P.Ok k → P.Ok j
child-ok child o = proj₂ o tt

restrict : ∀ {j k x} → LastInput j k x → F.Base k → F.Base j
restrict h B i w = B i (into h w)

unfold : ∀ {j k x} (h : LastInput j k x) o B i (w : i W.≤ j) z →
  F.ψ k o B i (into h w) z x ≡ F.ψ j (child-ok h o) (restrict h B) i w z (proj₁ (O.Ωt j))
unfold child o B i w z = refl

data Power {j : W.L} (b : O.Tr⁺ j) : W.Tr j → Set where
  power : (e : W.Ex (W.Sig j)) → Power b (W.ex (proj₁ b) (proj₁ b) (proj₂ b) (proj₁ (O.Ωt j)) e)

self-input : ∀ n {j} → j ≡ fin (suc n) → (o : P.Ok j) (B : F.Base j) (b : O.Tr⁺ j) →
  Power b (proj₁ (F.ψ j o B j W.self b (proj₁ (O.Ωt j))))
self-input n refl o B b = power tt

above : ∀ {j} {b : O.Tr⁺ j} {x} → proj₁ (O.Ωt j) Slots.⊴ proj₁ b → Power b x → j W.⊢ proj₁ (O.Ωt j) ◃ x
above (inj₁ refl) (power _) = W.◃e
above (inj₂ d) (power _) = W.◃t d W.◃e

module At (r : T.Run Tower.Lω) where
  module A = Prefix.At Tower.gL r
  lt : ∀ n → n N.< suc n
  lt n = NP.≤-refl
  last-input : ∀ n → LastInput (Tower.gL n) (Tower.gL (suc n)) (A.cast n (suc n) (lt n))
  last-input n = adjacent (suc n) (tower-level n) (tower-level (suc n))
    (A.ok (suc n)) (A.picked n (suc n) (lt n))

  higher = λ n → T.limRun Tower.gL r (suc n)
  path = λ n {i} → into (last-input n) {i}
  partial = λ n → Prefix.apply (A.rest (suc n)) (A.fix (suc n) n)
  old = λ n → restrict (last-input n) (partial n)
  ok = λ n → child-ok (last-input n) (A.ok (suc n))

  slot : ∀ n i (w : i W.≤ Tower.gL n) →
    T.Run.bs (higher n) i (path n w) ≡ F.ψ (Tower.gL n) (ok n) (old n) i w (old n i w) (proj₁ (O.Ωt (Tower.gL n)))
  slot n i w = trans
    (cong (λ f → f i (path n w) (A.rest (suc n) i (path n w))) (A.step n (suc n) (lt n)))
    (unfold (last-input n) (A.ok (suc n)) (partial n) i w (old n i w))

  self-slot : ∀ n → Power (old n (Tower.gL n) W.self)
    (proj₁ (T.Run.bs (higher n) (Tower.gL n) (path n W.self)))
  self-slot n = subst (Power (old n (Tower.gL n) W.self)) (sym (cong proj₁ (slot n (Tower.gL n) W.self)))
    (self-input n (tower-level n) (ok n) (old n) (old n (Tower.gL n) W.self))

  before : ∀ n → T.Run (Tower.gL (suc n))
  before n = T.enterRun W.sL Tower.gL r (suc n) (T.prefix Tower.gL n)

  replay : ∀ n → T.Run (Tower.gL n)
  replay n = T.makeRun (ok n) (old n) (old n W.zero (P.z≤ (Tower.gL n)))
    (λ w → T.Run.oneB (before n) (path n w))
    (λ w → T.Run.omegaB (before n) (path n w))
    (T.Run.oneB (before n) (path n (P.z≤ (Tower.gL n))))

  covered : Slots.Covered r → ∀ n → Slots.Covered (replay n)
  covered h n i w = Slots.enter W.sL Tower.gL r (suc n) (T.prefix Tower.gL n) h i (path n w)

  observe : ∀ n → W.Tr (Tower.gL n) → T₀
  observe n x = read (proj₁ (F.ψ (Tower.gL n) (ok n) (old n) W.zero (P.z≤ (Tower.gL n))
    (T.Run.β (replay n)) x))

  strict-self : Slots.Covered r → ∀ n → L.suc (read (T.value (replay n))) ≼
    observe n (proj₁ (T.Run.bs (higher n) (Tower.gL n) (path n W.self)))
  strict-self cv n = Strict.strict (F.mono (Tower.gL n) (ok n) (old n) W.zero (P.z≤ (Tower.gL n))
    (T.Run.β (replay n)) (above (covered cv n (Tower.gL n) W.self) (self-slot n)))

  receive : ∀ n → read (proj₁ (T.Run.bs (higher n) W.zero (path n (P.z≤ (Tower.gL n))))) ≡ read (T.value (replay n))
  receive n = cong (λ x → read (proj₁ x)) (slot n W.zero (P.z≤ (Tower.gL n)))

  transfer : ∀ n (a : T₀) → ((u : T.Run (Tower.gL n)) → Slots.Covered u → a ≼ read (T.value u)) →
    Slots.Covered r → a ≼ read (proj₁ (T.Run.bs (higher n) W.zero (path n (P.z≤ (Tower.gL n)))))
  transfer n a law cv = subst (a ≼_) (sym (receive n)) (law (replay n) (covered cv n))

```
