# 有限层折叠在零层反馈域上的同时模拟

第四层验收。有限后继层的两套折叠可在同一子文法上作结构归纳，底返回和零槽返回同时计算。Ω 行以返回值作下一次实参，分支关系因而量化到整条迭代。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseBridge where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
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

ol : ℕ → O.L
ol zero = O.zero
ol (suc n) = O.suc (ol n)

wl : ℕ → W.L
wl zero = W.zero
wl (suc n) = W.nd W.sS (λ _ → wl n)

op : ∀ n → O.zero P.≤ ol n
op zero = P.self
op (suc n) = P.ins (op n)

wp : ∀ n → W.zero W.≤ wl n
wp zero = W.self
wp (suc n) = W.inc tt (wp n)

data Same : O.Tr O.zero → W.Tr W.zero → Set where
  rz : Same O.zero W.zero
  rs : ∀ {a b} → Same a b → Same (O.suc a) (W.suc b)
  rl : ∀ {f g d e} → (∀ k → Same (f k) (g k)) → Same (O.lim f d) (W.lim g e)

read-same : ∀ {a b} → Same a b → V.read a L.≅ R.read b
read-same rz = L.z≅
read-same (rs h) = L.s≅ (read-same h)
read-same (rl h) = L.l≅ (λ k → read-same (h k))

same-add : ∀ {a b c d} → Same a b → Same c d → Same (a A.+ c) (b U.+ d)
same-add h rz = h
same-add h (rs k) = rs (same-add h k)
same-add h (rl k) = rl (λ i → same-add h (k i))

same-it : ∀ {a b} → Same a b → ∀ k → Same (A.iter (a A.+_) a k) (W.iter (b U.+_) b k)
same-it h zero = h
same-it h (suc k) = same-add h (same-it h k)

same-cum : ∀ {a b} → (∀ i → Same (a i) (b i)) → ∀ k → Same (A.cum a k) (U.cum b k)
same-cum h zero = h zero
same-cum h (suc k) = same-add (same-cum h k) (h (suc k))

data Row : (n : ℕ) → O.Tr (ol n) → W.Tr (wl n) → Set where
  z : ∀ {n} → Row n O.zero W.zero
  s : ∀ {n a b} → Row n a b → Row n (O.suc a) (W.suc b)
  l : ∀ {n f g d e} → (∀ k → Row n (f k) (g k)) → Row n (O.lim f d) (W.lim g e)
  u : ∀ {n a b x y d e} → Row (suc n) a b → Row n x y →
      Row (suc n) (O.up a tt x d) (W.up b tt y e)
  Ω₁ : ∀ {f g} → (∀ {x y} → Same x y → Row 1 (f x) (g y)) →
       Row 1 (O.Ω (inj₁ tt) f) (W.Ω (inj₂ (tt , inj₁ tt)) g)

zero-row : ∀ {a b} → Same a b → Row 0 a b
zero-row rz = z
zero-row (rs k) = s (zero-row k)
zero-row (rl k) = l (λ i → zero-row (k i))

Ω₁-row : Row 1 (A.Ωt (ol 1)) (proj₁ (U.Ωt (wl 1)))
Ω₁-row = Ω₁ (λ h → u z (s (zero-row h)))

OldSeed = Σ (O.Tr O.zero) (O._⊢_◃_ O.zero O.zero)

data Entry : Set where
  bottom : Entry
  slot : OldSeed → Entry

seed : ∀ {n} → G.Base (ol n) → Entry → OldSeed
seed B bottom = G.b⊥ B , G.n⊥ B
seed B (slot a) = a

eval : ∀ n → P.Ev (ol n) → P.Rt (ol n) → G.Base (ol n) → Entry → O.Tr (ol n) → OldSeed
eval n ε ρ B bottom x = G.ψ⊥ (ol n) ε ρ B x , G.nz⊥ (ol n) ε ρ B x
eval n ε ρ B (slot (b , e)) x = G.ψs (ol n) ε ρ B O.zero (op n) b e x , G.nzs (ol n) ε ρ B O.zero (op n) b e x

entry-at : ∀ n → G.Base (ol n) → OldSeed
entry-at n B = G.bs B O.zero (op n) , G.ns B O.zero (op n)

Run : ∀ {n} → O.Tr (ol n) → W.Tr (wl n) → Set
Run {n} x y = (ε : P.Ev (ol n)) (ρ : P.Rt (ol n)) (B : G.Base (ol n))
  (o : Q.Ok (wl n)) (D : F.Base (wl n)) → Same (proj₁ (entry-at n B)) (proj₁ (D W.zero (wp n))) →
  (r : Entry) (β : U.Tr⁺ W.zero) → Same (proj₁ (seed {n} B r)) (proj₁ β) →
  Same (proj₁ (eval n ε ρ B r x)) (proj₁ (F.ψ (wl n) o D W.zero (wp n) β y))
```

```agda
zero-run : ∀ {n} → Run {n} O.zero W.zero
zero-run ε ρ B o D q bottom β h = h
zero-run ε ρ B o D q (slot (b , e)) β h = h

succ-run : ∀ {n a b} → Run {n} a b → Run {n} (O.suc a) (W.suc b)
succ-run {n = zero} k ε ρ B o D q bottom β h = rl (same-it (k ε ρ B o D q bottom β h))
succ-run {n = zero} k ε ρ B o D q r@(slot (_ , _)) β h = rl (same-it (k ε ρ B o D q r β h))
succ-run {suc n} k ε ρ B o D q bottom β h = rl (same-it (k ε ρ B o D q bottom β h))
succ-run {suc n} k ε ρ B o D q r@(slot (_ , _)) β h = rl (same-it (k ε ρ B o D q r β h))

lim-run : ∀ {n f g d e} → (∀ i → Run {n} (f i) (g i)) → Run {n} (O.lim f d) (W.lim g e)
lim-run {n = zero} k ε ρ B o D q bottom β h = rl (λ i → k i ε ρ B o D q bottom β h)
lim-run {n = zero} k ε ρ B o D q r@(slot (_ , _)) β h = rl (λ i → k i ε ρ B o D q r β h)
lim-run {suc n} k ε ρ B o D q bottom β h = rl (λ i → k i ε ρ B o D q bottom β h)
lim-run {suc n} k ε ρ B o D q r@(slot (_ , _)) β h = rl (λ i → k i ε ρ B o D q r β h)

up-run : ∀ {n a b x y d e} → Run {suc n} a b → Run {n} x y →
         Run {suc n} (O.up a tt x d) (W.up b tt y e)
up-run {n} {a} {b} {x} {y} {d} {e} k j ε ρ B o D q r β h = at-child r h
  where
  child-B = G.dS (ol n) ε ρ B a
  child-D : F.Base (wl n)
  child-D i v = F.ψ (wl (suc n)) o D i (W.inc tt v) (D i (W.inc tt v)) b
  child-β = F.ψ (wl (suc n)) o D W.zero (wp (suc n)) β b
  child-q = k ε ρ B o D q (slot (entry-at (suc n) B)) (D W.zero (wp (suc n))) q

  at-child : (r′ : Entry) → Same (proj₁ (seed {suc n} B r′)) (proj₁ β) →
             Same (proj₁ (eval (suc n) ε ρ B r′ (O.up a tt x d)))
                  (proj₁ (F.ψ (wl n) (proj₂ o tt) child-D W.zero (wp n) child-β y))
  at-child bottom t = j ε ρ child-B (proj₂ o tt) child-D child-q bottom child-β (k ε ρ B o D q bottom β t)
  at-child r′@(slot (_ , _)) t = j ε ρ child-B (proj₂ o tt) child-D child-q
    (slot (eval (suc n) ε ρ B r′ a)) child-β (k ε ρ B o D q r′ β t)
```

```agda
omega-run : ∀ {f g} → (∀ {x y} → Same x y → Run {1} (f x) (g y)) →
            Run {1} (O.Ω (inj₁ tt) f) (W.Ω (inj₂ (tt , inj₁ tt)) g)
omega-run {f} {g} k ε ρ B o D q r β h = outer r h
  where
  α = entry-at 1 B
  γ = D W.zero (wp 1)
  old-step : O.Tr O.zero → O.Tr O.zero
  old-step x = proj₁ (eval 1 ε ρ B (slot α) (f x))
  w-step : W.Tr W.zero → W.Tr W.zero
  w-step y = proj₁ (F.ψ (wl 1) o D W.zero (wp 1) γ (g y))

  chain : ∀ i → Same (A.iter old-step O.zero i) (W.iter w-step W.zero i)
  chain zero = rz
  chain (suc i) = k (chain i) ε ρ B o D q (slot α) γ q

  terms : ∀ r′ → Same (proj₁ (seed {1} B r′)) (proj₁ β) → ∀ i →
          Same (proj₁ (eval 1 ε ρ B r′ (f (A.iter old-step O.zero i))))
               (proj₁ (F.ψ (wl 1) o D W.zero (wp 1) β (g (W.iter w-step W.zero i))))
  terms r′ t i = k (chain i) ε ρ B o D q r′ β t

  outer : ∀ r′ → Same (proj₁ (seed {1} B r′)) (proj₁ β) →
          Same (proj₁ (eval 1 ε ρ B r′ (O.Ω (inj₁ tt) f)))
               (proj₁ (F.ψ (wl 1) o D W.zero (wp 1) β (W.Ω (inj₂ (tt , inj₁ tt)) g)))
  outer bottom t = rl (same-cum (terms bottom t))
  outer r′@(slot (_ , _)) t = rl (same-cum (terms r′ t))

simulate : ∀ {n a b} → Row n a b → Run {n} a b
simulate {n} z = zero-run {n}
simulate {n} (s {a = a} {b} k) = succ-run {n} {a} {b} (simulate k)
simulate {n} (l {f = f} {g} k) = lim-run {n} {f} {g} (λ i → simulate (k i))
simulate (u {n} {a} {b} {x} {y} k j) = up-run {n} {a} {b} {x} {y} (simulate k) (simulate j)
simulate (Ω₁ {f} {g} k) = omega-run {f} {g} (λ t → simulate (k t))
```

```agda
standard : ∀ {n a b} → Row n a b → (ε : P.Ev (ol n)) (ρ : P.Rt (ol n)) (o : Q.Ok (wl n)) →
           V.read (G.ψ⊥ (ol n) ε ρ (G.B₀ (ol n)) a) L.≅
           R.read (proj₁ (F.ψ (wl n) o (F.B₀ (wl n)) W.zero (wp n) (U.Ωt W.zero) b))
standard {n} h ε ρ o = read-same (simulate h ε ρ (G.B₀ (ol n)) o (F.B₀ (wl n)) (rs rz)
  bottom (U.Ωt W.zero) (rs rz))
```
