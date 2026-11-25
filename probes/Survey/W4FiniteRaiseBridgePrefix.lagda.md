# 有限层前缀的环境更新与 Ω₁ 反馈种子的自身返回

第四层验收。任意旧前缀与成对的 `Row` 尾相加，可把此前缀对外部底和零槽的两次折叠转入新环境。正种子属于该域时，自层指数 1 给出双向同值。域中允许零、后继、可数极限、有限层间的任意 `up` 及第一层的 Ω₁ 反馈。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseBridgePrefix where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
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

import Survey.W4FiniteRaiseBridge as Orig
open Orig using (ol; wl; wp; Same; rz; rl; same-it; same-cum; Entry; bottom; slot; entry-at; eval; Row; z; s; l; u; Ω₁)

PrefixRun : ∀ {n} → O.Tr (ol n) → O.Tr (ol n) → W.Tr (wl n) → Set
PrefixRun {n} p x y = (ε : P.Ev (ol n)) (ρ : P.Rt (ol n)) (B : G.Base (ol n))
  (o : Q.Ok (wl n)) (D : F.Base (wl n)) → Same (proj₁ (eval n ε ρ B (slot (entry-at n B)) p)) (proj₁ (D W.zero (wp n))) →
  (r : Entry) (β : U.Tr⁺ W.zero) → Same (proj₁ (eval n ε ρ B r p)) (proj₁ β) →
  Same (proj₁ (eval n ε ρ B r (p A.+ x))) (proj₁ (F.ψ (wl n) o D W.zero (wp n) β y))

zero-run : ∀ {n p} → PrefixRun {n} p O.zero W.zero
zero-run ε ρ B o D q bottom β h = h
zero-run ε ρ B o D q (slot (b , e)) β h = h

succ-run : ∀ {n p a b} → PrefixRun {n} p a b → PrefixRun {n} p (O.suc a) (W.suc b)
succ-run {n = zero} k ε ρ B o D q bottom β h = rl (same-it (k ε ρ B o D q bottom β h))
succ-run {n = zero} k ε ρ B o D q r@(slot (_ , _)) β h = rl (same-it (k ε ρ B o D q r β h))
succ-run {suc n} k ε ρ B o D q bottom β h = rl (same-it (k ε ρ B o D q bottom β h))
succ-run {suc n} k ε ρ B o D q r@(slot (_ , _)) β h = rl (same-it (k ε ρ B o D q r β h))

lim-run : ∀ {n p f g d e} → (∀ i → PrefixRun {n} p (f i) (g i)) → PrefixRun {n} p (O.lim f d) (W.lim g e)
lim-run {n = zero} k ε ρ B o D q bottom β h = rl (λ i → k i ε ρ B o D q bottom β h)
lim-run {n = zero} k ε ρ B o D q r@(slot (_ , _)) β h = rl (λ i → k i ε ρ B o D q r β h)
lim-run {suc n} k ε ρ B o D q bottom β h = rl (λ i → k i ε ρ B o D q bottom β h)
lim-run {suc n} k ε ρ B o D q r@(slot (_ , _)) β h = rl (λ i → k i ε ρ B o D q r β h)

up-run : ∀ {n p a b x y d e} → PrefixRun {suc n} p a b → Orig.Run {n} x y →
         PrefixRun {suc n} p (O.up a tt x d) (W.up b tt y e)
up-run {n} {p} {a} {b} {x} {y} {d} {e} k j ε ρ B o D q r β h = at-child r h
  where
  child-B = G.dS (ol n) ε ρ B (p A.+ a)
  child-D : F.Base (wl n)
  child-D i v = F.ψ (wl (suc n)) o D i (W.inc tt v) (D i (W.inc tt v)) b
  child-β = F.ψ (wl (suc n)) o D W.zero (wp (suc n)) β b
  child-q = k ε ρ B o D q (slot (entry-at (suc n) B)) (D W.zero (wp (suc n))) q

  at-child : (r′ : Entry) → Same (proj₁ (eval (suc n) ε ρ B r′ p)) (proj₁ β) →
             Same (proj₁ (eval (suc n) ε ρ B r′ (O.up (p A.+ a) tt x d)))
                  (proj₁ (F.ψ (wl n) (proj₂ o tt) child-D W.zero (wp n) child-β y))
  at-child bottom t = j ε ρ child-B (proj₂ o tt) child-D child-q bottom child-β (k ε ρ B o D q bottom β t)
  at-child r′@(slot (_ , _)) t = j ε ρ child-B (proj₂ o tt) child-D child-q
    (slot (eval (suc n) ε ρ B r′ (p A.+ a))) child-β (k ε ρ B o D q r′ β t)

omega-run : ∀ {p f g} → (∀ {x y} → Same x y → PrefixRun {1} p (f x) (g y)) →
            PrefixRun {1} p (O.Ω (inj₁ tt) f) (W.Ω (inj₂ (tt , inj₁ tt)) g)
omega-run {p} {f} {g} k ε ρ B o D q r β h = outer r h
  where
  α = entry-at 1 B
  γ = D W.zero (wp 1)
  old-step : O.Tr O.zero → O.Tr O.zero
  old-step x = proj₁ (eval 1 ε ρ B (slot α) (p A.+ f x))
  w-step : W.Tr W.zero → W.Tr W.zero
  w-step y = proj₁ (F.ψ (wl 1) o D W.zero (wp 1) γ (g y))

  chain : ∀ i → Same (A.iter old-step O.zero i) (W.iter w-step W.zero i)
  chain zero = rz
  chain (suc i) = k (chain i) ε ρ B o D q (slot α) γ q

  terms : ∀ r′ → Same (proj₁ (eval 1 ε ρ B r′ p)) (proj₁ β) → ∀ i →
          Same (proj₁ (eval 1 ε ρ B r′ (p A.+ f (A.iter old-step O.zero i))))
               (proj₁ (F.ψ (wl 1) o D W.zero (wp 1) β (g (W.iter w-step W.zero i))))
  terms r′ t i = k (chain i) ε ρ B o D q r′ β t

  outer : ∀ r′ → Same (proj₁ (eval 1 ε ρ B r′ p)) (proj₁ β) →
          Same (proj₁ (eval 1 ε ρ B r′ (O.Ω (inj₁ tt) (λ x → p A.+ f x))))
               (proj₁ (F.ψ (wl 1) o D W.zero (wp 1) β (W.Ω (inj₂ (tt , inj₁ tt)) g)))
  outer bottom t = rl (same-cum (terms bottom t))
  outer r′@(slot (_ , _)) t = rl (same-cum (terms r′ t))

simulate : ∀ {n a b} → Row n a b → (p : O.Tr (ol n)) → PrefixRun {n} p a b
simulate {n} z p = zero-run {n} {p}
simulate {n} (s {a = a} {b} k) p = succ-run {n} {p} {a} {b} (simulate k p)
simulate {n} (l {f = f} {g} k) p = lim-run {n} {p} {f} {g} (λ i → simulate (k i) p)
simulate (u {n} {a} {b} {x} {y} k j) p = up-run {n} {p} {a} {b} {x} {y} (simulate k p) (Orig.simulate j)
simulate (Ω₁ {f} {g} k) p = omega-run {p} {f} {g} (λ t → simulate (k t) p)

```

右边与另一个旧输入同形时，可经它传递分支对应。槽状态和外部参数各自从第一次执行之后启动余下迭代。

```agda
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; sym)
open import OCF.Align.Value using (_≈ᵛ_; _≼_; ≼l; l≼; ≅→≼; ≼-trans; ⊑→≼)
open Orig using (rs; read-same)

same-compose : ∀ {a b x y} → Same a x → Same b x → Same b y → Same a y
same-compose rz rz rz = rz
same-compose (rs k) (rs m) (rs v) = rs (same-compose k m v)
same-compose (rl k) (rl m) (rl v) = rl (λ i → same-compose (k i) (m i) (v i))

row-add : ∀ {n a b x y} → Row n a b → Row n x y → Row n (a A.+ x) (b U.+ y)
row-add k z = k
row-add k (s m) = s (row-add k m)
row-add k (l m) = l (λ i → row-add k (m i))
row-add k (u m j) = u (row-add k m) j
row-add k (Ω₁ m) = Ω₁ (λ t → row-add k (m t))

shift-state : ∀ {ℓ X} (f : F.Op {ℓ} X) k S → F.itS f k (F.stepS f S) ≡ F.itS f (suc k) S
shift-state f zero S = refl
shift-state f (suc k) S = cong (F.stepS f) (shift-state f k S)

shift-value : ∀ {ℓ X} (f : F.Op {ℓ} X) k S i w v →
  F.itV f k (F.stepS f S) i w (F.run f S i w v) ≡ F.itV f (suc k) S i w v
shift-value f zero S i w v = refl
shift-value f (suc k) S i w v = cong₂ (λ C u → F.run f C i w u) (shift-state f k S) (shift-value f k S i w v)

```

旧树把同一种子逐次左加。每次把最左的种子移入底及零槽，剩余旧和与更新环境下的 W4 迭代逐项同形。

```agda
module Self (n : ℕ) (a : O.Tr (ol (suc n))) (b : W.Tr (wl (suc n)))
            (oa : ol (suc n) O.⊢ O.zero ◃ a) (wb : wl (suc n) W.⊢ W.zero ◃ b) (row : Row (suc n) a b)
            (ε : P.Ev (ol (suc n))) (ρ : P.Rt (ol (suc n))) (o : Q.Ok (wl (suc n))) where
  j = ol (suc n)
  ℓ = wl (suc n)
  w = wp (suc n)
  worker = F.opB ℓ o b wb
  old-copies = A.iter (a A.+_) a
  new-copies = W.iter (b U.+_) b
  many : ∀ k → Row (suc n) (old-copies k) (new-copies k)
  many zero = row
  many (suc k) = row-add row (many k)

  push : G.Base j → G.Base j
  push B = G.base (G.ψ⊥ j ε ρ B a) (G.nz⊥ j ε ρ B a)
    (λ i p → G.ψs j ε ρ B i p (G.bs B i p) (G.ns B i p) a)
    (λ i p → G.nzs j ε ρ B i p (G.bs B i p) (G.ns B i p) a)

  matched : G.Base j → F.Base ℓ → Set

  matched = λ B D → Same (proj₁ (entry-at (suc n) B)) (proj₁ (D W.zero w))
  fold = G.ψ⊥ j ε ρ
  iterated : ∀ k (B : G.Base j) (D : F.Base ℓ) (v : U.Tr⁺ W.zero) → matched B D → Same (G.b⊥ B) (proj₁ v) →
             Same (fold B (old-copies k)) (proj₁ (F.itV worker (suc k) D W.zero w v))
  iterated zero B D v q h = Orig.simulate row ε ρ B o D q bottom v h
  iterated (suc k) B D v q h = subst (λ z → Same (fold B (old-copies (suc k))) (proj₁ z))
    (shift-value worker (suc k) D W.zero w v) (same-compose prefixed rebased replayed)
    where
    B′ = push B
    D′ = F.stepS worker D
    v′ = F.run worker D W.zero w v
    q′ = Orig.simulate row ε ρ B o D q (slot (entry-at (suc n) B)) (D W.zero w) q
    h′ = Orig.simulate row ε ρ B o D q bottom v h
    prefixed = simulate (many k) a ε ρ B o D′ q′ bottom v′ h′
    rebased = Orig.simulate (many k) ε ρ B′ o D′ q′ bottom v′ h′
    replayed = iterated k B′ D′ v′ q′ h′

  module Observe (B : G.Base j) (D : F.Base ℓ) (v : U.Tr⁺ W.zero)
                 (q : matched B D) (h : Same (G.b⊥ B) (proj₁ v)) where
    old-return = G.ψs j ε ρ B j P.self a oa (O.suc O.zero)
    new-return = proj₁ (F.ψ ℓ o D ℓ W.self (b , wb) (W.suc W.zero))
    observe = F.ψ ℓ o D W.zero w v
    old-branch = λ k → fold B (old-copies k)
    new-branch = λ k → proj₁ (F.itV worker (suc k) (F.stepS worker D) W.zero w (F.run worker D W.zero w v))
    aligned : ∀ k → Same (old-branch (suc k)) (new-branch k)
    aligned k = subst (λ z → Same (old-branch (suc k)) (proj₁ z))
      (sym (shift-value worker (suc k) D W.zero w v)) (iterated (suc k) B D v q h)

    strict-at : ∀ k → V.read (old-branch k) L.≺ R.read (new-branch k)
    strict-at k = L.≺-respʳ (V.◃→≺ (G.mono⊥ j ε ρ B (A.nextA a oa k))) (read-same (aligned k))

    value : V.read (fold B old-return) ≈ᵛ R.read (proj₁ (observe new-return))
    value = l≼ lower , l≼ (λ k → ≼l (suc k) (≅→≼ (L.≅-sym (read-same (aligned k)))))
      where
      lower : ∀ k → V.read (old-branch k) ≼ R.read (proj₁ (observe new-return))
      lower zero = ≼l 0 (≼-trans (⊑→≼ (V.read (old-branch 0)) {V.read (old-branch 1)} (V.◃⊑ (G.mono⊥ j ε ρ B (A.nextA a oa zero))))
                                 (≅→≼ (read-same (aligned 0))))
      lower (suc k) = ≼l k (≅→≼ (read-same (aligned k)))

```

取第一层本身的 Ω₁ 树作正种子，真实返回的指数取 1，两个标准底的前提均由构造子给出。相邻有限层实际传递的返回以 Ωⱼ 为指数。

```agda
module OmegaOne = Self 0 (A.Ωt (ol 1)) (proj₁ (U.Ωt (wl 1))) (A.Ωt-nz (ol 1)) (proj₂ (U.Ωt (wl 1)))
  Orig.Ω₁-row tt tt (tt , λ _ → tt)

module StandardOmegaOne = OmegaOne.Observe (G.B₀ (ol 1)) (F.B₀ (wl 1)) (U.Ωt W.zero) (rs rz) (rs rz)
```
