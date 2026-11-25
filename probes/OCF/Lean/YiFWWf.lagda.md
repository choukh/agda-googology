# B7 候选第一位置的良基
> 编译定理：各孩子的原关系良基时，新增第一位置良基且非自反。
> 证明沿 Ω 的第一分支下降；同构只用到第一点保持，未要求下标三歧。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFWWf where
open import OCF.Lean.YiFWBlock
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (subst; sym)

data Acc {A : Set} (R : A → A → Set) (x : A) : Set where
  acc : (∀ {y} → R y x → Acc R y) → Acc R x

down : ∀ {A R} {x y : A} → Acc R y → R x y → Acc R x
down (acc h) d = h d

module _ {S : Sg} where
  mutual
    accS : (x : T S) → Acc (Lt S) x → Acc (Lt S) (suc x)
    accS x ax = acc (belowS x ax)

    belowS : (x : T S) → Acc (Lt S) x → ∀ {y} → Lt S y (suc x) → Acc (Lt S) y
    belowS x ax ◃s = ax
    belowS x ax (◃t d e) = down (belowS x ax e) d

  mutual
    accL : (f : ℕ → T S) (a : ∀ n → Lt S (f n) (f (suc n)))
         → (∀ n → Acc (Lt S) (f n)) → Acc (Lt S) (lim f a)
    accL f a af = acc (belowL f a af)

    belowL : (f : ℕ → T S) (a : ∀ n → Lt S (f n) (f (suc n)))
         → (∀ n → Acc (Lt S) (f n)) → ∀ {y} → Lt S y (lim f a) → Acc (Lt S) y
    belowL f a af (◃l n) = af n
    belowL f a af (◃t d e) = down (belowL f a af e) d

  mutual
    accW : (p : P S) (g : B S p → T S) → Acc (Lt S) (g (b₀ S p)) → Acc (Lt S) (Ω p g)
    accW p g ag = acc (belowW p g ag)

    belowW : (p : P S) (g : B S p → T S) → Acc (Lt S) (g (b₀ S p))
           → ∀ {y} → Lt S y (Ω p g) → Acc (Lt S) y
    belowW p g ag ◃w = ag
    belowW p g ag (◃t d e) = down (belowW p g ag e) d
    belowW p g (acc ag) (◃σ {p = q} {g = f} e h) =
      accW q f (ag (subst (λ z → Lt S (f z) (g (b₀ S p))) (cv₀ S e) (h (b₀ S p))))

  mutual
    accU : (x : T S) → Acc (Lt S) x → (c : C S) (y : D S c) (e : R S c (z₀ S c) y)
         → Acc (R S c) y → Acc (Lt S) (up x c y e)
    accU x ax c y e ay = acc (belowU x ax c y e ay)

    belowU : (x : T S) → Acc (Lt S) x → (c : C S) (y : D S c) (e : R S c (z₀ S c) y)
         → Acc (R S c) y → ∀ {t} → Lt S t (up x c y e) → Acc (Lt S) t
    belowU x ax c y e ay (◃u .x .c .y .e) = ax
    belowU x ax c y e (acc ay) (◃c .x .c {y′ = y′} {e′ = e′} d) = accU x ax c y′ e′ (ay d)
    belowU x ax c y e ay (◃t d f) = down (belowU x ax c y e ay f) d

  wf : (∀ c y → Acc (R S c) y) → (x : T S) → Acc (Lt S) x
  wf w zero = acc λ d → ⊥-elim (no-zero d)
  wf w (suc x) = accS x (wf w x)
  wf w (lim f a) = accL f a (λ n → wf w (f n))
  wf w (Ω p g) = accW p g (wf w (g (b₀ S p)))
  wf w (up x c y e) = accU x (wf w x) c y e (w c y)

  irrefl : (∀ c y → Acc (R S c) y) → ∀ {x} → Lt S x x → ⊥
  irrefl w {x} = go (wf w x)
    where
    go : ∀ {x} → Acc (Lt S) x → Lt S x x → ⊥
    go (acc ax) d = go (ax d) d
```
