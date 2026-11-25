# YiXVFiniteIndex
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。
> 有限左端点的等式唯一性按标准库 Constant⇒UIP 的证明局部化。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteIndex where
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
import Data.Fin as F
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans; sym; trans-symˡ)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no; recompute; recompute-constant)
import OCF.Align.Level as L
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVRef2 as F

T : ℕ → Set
T n = L.Ordᶜ (L.natᴵ n)
q₁ : L.natᴵ 1 L.<ᴵ L.natᴵ 2
q₁ = L.zero
q₀ : L.natᴵ 0 L.<ᴵ L.natᴵ 2
q₀ = L.suc L.zero
top-input : L.U (L.natᴵ 1) (L.<→◃ q₁)
top-input = L.Ω (L.natᴵ 1)
low-input : L.U (L.natᴵ 0) (L.<→◃ q₀)
low-input = L.suc L.zero
actual : C.Gd F.Ω₂
actual = C.Gd-Ω₂

step : ∀ {m n} → m ≤ n → m ≤ suc n
step z≤n = z≤n
step (s≤s p) = s≤s (step p)
r≤ : ∀ n → n ≤ n
r≤ zero = z≤n
r≤ (suc n) = s≤s (r≤ n)

record Slot (n : ℕ) (i : L.Ordᴵ) : Set where
  constructor slot
  field
    level : ℕ
    equal : i ≡ L.natᴵ level
    bound : level ≤ n
open Slot

rank : ∀ n → F.Fin (suc n) → ℕ
rank n F.zero = n
rank zero (F.suc ())
rank (suc n) (F.suc i) = rank n i
rank-bound : ∀ n i → rank n i ≤ n
rank-bound n F.zero = r≤ n
rank-bound zero (F.suc ())
rank-bound (suc n) (F.suc i) = step (rank-bound n i)
record FinSlot (n : ℕ) (i : L.Ordᴵ) : Set where
  constructor fslot
  field
    index : F.Fin (suc n)
    same : i ≡ L.natᴵ (rank n index)
open FinSlot
cutF : ∀ n {i} → i L.<ᴵ L.natᴵ (suc n) → FinSlot n i
cutF n L.zero = fslot F.zero refl
cutF zero (L.suc ())
cutF (suc n) (L.suc q) with cutF n q
... | fslot i refl = fslot (F.suc i) refl
cut : ∀ n {i} → i L.<ᴵ L.natᴵ (suc n) → Slot n i
cut n q with cutF n q
... | fslot i e = slot (rank n i) e (rank-bound n i)

Uref : ∀ n {i} (q : i L.<ᴵ L.natᴵ (suc n)) → L.U i (L.<→◃ q) → T (rank n (index (cutF n q)))
Uref n q u = subst L.Ordᶜ (same (cutF n q)) (L.out (L.<→◃ q) u)

data Finite : L.Ordᴵ → Set where
  fz : Finite L.zero
  fs : ∀ {a} → Finite a → Finite (L.suc a)
finite : ∀ n → Finite (L.natᴵ n)
finite zero = fz
finite (suc n) = fs (finite n)

dec-at : ∀ {a} → Finite a → (b : L.Ordᴵ) → Dec (a ≡ b)
dec-at fz L.zero = yes refl
dec-at fz (L.suc b) = no (λ ())
dec-at fz (L.lim f s) = no (λ ())
dec-at (fs ga) L.zero = no (λ ())
dec-at (fs ga) (L.suc b) with dec-at ga b
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })
dec-at (fs ga) (L.lim f s) = no (λ ())

module AtFinite {a : L.Ordᴵ} (ga : Finite a) where
  norm : ∀ {b} → a ≡ b → a ≡ b
  norm {b} p = recompute (dec-at ga b) p
  constant : ∀ {b} (p q : a ≡ b) → norm p ≡ norm q
  constant {b} = recompute-constant (dec-at ga b)
  canonical : ∀ {b} (p : a ≡ b) → trans (sym (norm refl)) (norm p) ≡ p
  canonical refl = trans-symˡ (norm refl)
  unique : ∀ {b} (p q : a ≡ b) → p ≡ q
  unique p q = trans (sym (canonical p))
    (trans (cong (trans (sym (norm refl))) (constant p q)) (canonical q))

below : ∀ {a b} → Finite b → a L.<ᴵ b → Finite a
below fz ()
below (fs gb) L.zero = gb
below (fs gb) (L.suc p) = below gb p

Edge : L.Ordᴵ → Set
Edge b = Σ L.Ordᴵ (λ a → a L.<ᴵ b)
edge-inj : ∀ {a a′ b} → Finite b → (p : a L.<ᴵ b) (q : a′ L.<ᴵ b) → a ≡ a′ →
  (a , p) ≡ (a′ , q)
edge-inj fz () q e
edge-inj (fs gb) L.zero L.zero e = refl
edge-inj (fs {a = b} gb) L.zero (L.suc q) e =
  ⊥-elim (L.≺ᴵ-irrefl (L.via (L.≅ᴵ-refl b) (subst (λ a → a L.<ᴵ b) (sym e) q)))
edge-inj (fs {a = b} gb) (L.suc p) L.zero e =
  ⊥-elim (L.≺ᴵ-irrefl (L.via (L.≅ᴵ-refl b) (subst (λ a → a L.<ᴵ b) e p)))
edge-inj (fs gb) (L.suc p) (L.suc q) e = cong (λ { (a , r) → a , L.suc r }) (edge-inj gb p q e)

snd-path : ∀ {b} {x y : Edge b} (e : x ≡ y) → subst (λ a → a L.<ᴵ b) (cong proj₁ e) (proj₂ x) ≡ proj₂ y
snd-path refl = refl

q-uniqueᶠ : ∀ {a b} → Finite b → (p q : a L.<ᴵ b) → p ≡ q
q-uniqueᶠ {a} {b} gb p q = trans
  (sym (cong (λ e → subst (λ a → a L.<ᴵ b) e p) (AtFinite.unique (below gb p) (cong proj₁ bundle) refl)))
  (snd-path bundle)
  where
  bundle : (a , p) ≡ (a , q)
  bundle = edge-inj gb p q refl
q-unique : ∀ n {i} (p q : i L.<ᴵ L.natᴵ n) → p ≡ q
q-unique n = q-uniqueᶠ (finite n)

eq-uniqueᶠ : ∀ {a b} → Finite a → Finite b → (e d : a L.≅ᴵ b) → e ≡ d
eq-uniqueᶠ fz fz L.z≅ L.z≅ = refl
eq-uniqueᶠ (fs ga) (fs gb) (L.s≅ e) (L.s≅ d) = cong L.s≅ (eq-uniqueᶠ ga gb e d)
eq-unique : ∀ n (e : L.natᴵ n L.≅ᴵ L.natᴵ n) → e ≡ L.≅ᴵ-refl (L.natᴵ n)
eq-unique n e = eq-uniqueᶠ (finite n) (finite n) e (L.≅ᴵ-refl (L.natᴵ n))

≤-unique : ∀ {m n} (p q : m ≤ n) → p ≡ q
≤-unique z≤n z≤n = refl
≤-unique (s≤s p) (s≤s q) = cong s≤s (≤-unique p q)

out-coe : ∀ n {i} (q : i L.<ᴵ L.natᴵ n) (u : L.U i (L.<→◃ q)) →
  L.out (L.<→◃ q) (L.coe (L.<→◃ q) (L.<→◃ q) u) ≡ L.out (L.<→◃ q) u
out-coe n q u = L.out-into (L.<→◃ q) (L.out (L.<→◃ q) u)

sample₁ : Uref 1 q₁ top-input ≡ L.Ω (L.natᴵ 1)
sample₁ = refl
sample₀ : Uref 1 q₀ low-input ≡ L.suc L.zero
sample₀ = refl
```
