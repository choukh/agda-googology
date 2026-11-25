# W4 能容纳的起点和时钟可以一起变动

第四层，无条件。任一标准塔给起点作上界时，它上方首个 ε 数以内（含端点）的全部时钟可以共用再高五层的一座塔。将输出重新作起点并更新时钟，得到严格超过旧时钟整族的 W4 下界。[原迭代](W4PTOClock.lagda.md) · [比较标尺](W4RouteTests.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ClockClosure where

open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s; _⊔_)
import Data.Nat.Properties as Nat
open import Data.Product using (_,_)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-suc; ≼-trans; ≼lim⁻; ≼l; l≼; s≼s; z≼; ≅→≼)
open import WVOne using (T₀)
open import W4Block using (iter)
import B20StandardInside as St
import B21StandardShape as Shape
import B22MovingIndex as E
import B22TowerCut as K
import B24RExit as Entry
import B24ROrbit as Seed
import B25ARank as X
import B25ADiagonal as P
import B25AOrbit as Orbit
import Survey.W4PTOClock as C
import Survey.W4PTOFirstQuery as Ref
import Survey.W4RouteTests as Test

rank-mono : ∀ n {x y : T₀} → x ≼ y → X.rank n x ≼ X.rank n y
rank-mono zero {x} {y} = K.advance {x} {y}
rank-mono (suc n) {x} {y} h = l≼ λ j → ≼l j (points j)
  where
  points : ∀ j → iter (X.rank n) x j ≼ iter (X.rank n) y j
  points zero = h
  points (suc j) = rank-mono n (points j)

height-mono : ∀ n {x y : T₀} → x ≼ y → X.height n x ≼ X.height n y
height-mono zero h = h
height-mono (suc n) {x} {y} h =
  rank-mono (suc n) {X.height n x} {X.height n y} (height-mono n h)

step-mono : ∀ {x y} → x ≼ y → X.diagonal x ≼ X.diagonal y
step-mono h = l≼ λ n → ≼l n (height-mono n h)

start-below : ∀ x t → x ≼ C.run x t
start-below x L.zero = ≼-refl x
start-below x (L.suc t) = ≼-trans {b = L.suc (C.run x t)}
  (≼-suc (start-below x t)) (Orbit.strict-step (C.run x t))
start-below x (L.lim f) = ≼l 0 (start-below x (f 0))

both : ∀ {x y t u : T₀} → x ≼ y → t ≼ u → C.run x t ≼ C.run y u
both {y = y} {u = u} h z≼ = ≼-trans {b = y} h (start-below y u)
both h (s≼s d) = step-mono (both h d)
both h (≼l j d) = ≼l j (both h d)
both h (l≼ d) = l≼ λ j → both h (d j)
both h (OCF.Align.Value.≼i {p = ()} _ _ _)
both h (OCF.Align.Value.i≼ {p = ()} _)
both h (OCF.Align.Value.≼u {r = ()} _)
both h (OCF.Align.Value.u≼ {r = ()} _)

module Budget (n : ℕ) where
  s = St.std n
  p = P.embed s
  b = L.ψ⁰ p
  module B = C.Clocks p (P.reg s)
  value : b ≼ St.std (suc (suc (suc n)))
  value = ≼-trans {b = E.above s} (P.norm s) (K.up n)

  endpoint : ∀ x → x ≼ s → C.run x (E.above b) ≼ St.std (Orbit.five n)
  endpoint x h = l≼ λ j → B.fixed (suc n) value x
    (≼-trans {b = s} h (P.infl s)) (E.steps b j) (B.H.point j)

  run : ∀ x t → x ≼ s → t ≼ E.above s → C.run x t ≼ St.std (Orbit.five n)
  run x t h clock = ≼-trans {b = C.run x (E.above b)}
    (both {x} {x} {t} {E.above b} (≼-refl x)
      (≼-trans {b = E.above s} clock (K.advance {s} {b} (P.infl s))))
    (endpoint x h)

module Rising (f : ℕ → T₀) (rise : ∀ n → L.suc (f n) ≼ f (suc n)) where
  mono : ∀ {n m} → n ≤ m → f n ≼ f m
  mono h = walk (Nat.≤⇒≤′ h)
    where
    open import Data.Nat.Base using (_≤′_; ≤′-refl; ≤′-step)
    walk : ∀ {i j} → i ≤′ j → f i ≼ f j
    walk {i} ≤′-refl = ≼-refl (f i)
    walk {i} (≤′-step {n = j} d) = ≼-trans {b = L.suc (f j)} (≼-suc (walk d)) (rise j)

  under : ∀ {x : T₀} n → x ≼ f n → L.suc x ≼ L.lim f
  under n h = ≼l (suc n) (≼-trans {b = L.suc (f n)} (s≼s h) (rise n))

module Standard = Rising St.std Shape.rise

in-cut : ∀ x t → L.suc x ≼ K.cut → L.suc t ≼ K.cut → L.suc (C.run x t) ≼ K.cut
in-cut x t hx ht with ≼lim⁻ {a = x} {f = St.std} hx | ≼lim⁻ {a = t} {f = St.std} ht
... | i , xi | j , tj = ≼l (suc (Orbit.five k))
    (≼-trans {b = L.suc (St.std (Orbit.five k))} (s≼s (Budget.run k x t low clock)) (Shape.rise (Orbit.five k)))
  where
  k = i ⊔ j
  low = ≼-trans {b = L.suc x} (≼-suc (≼-refl x))
    (≼-trans {b = St.std i} xi (Standard.mono (Nat.m≤m⊔n i j)))
  clock = ≼-trans {b = L.suc (St.std k)}
    (≼-suc (≼-trans {b = L.suc t} (≼-suc (≼-refl t))
      (≼-trans {b = St.std j} tj (Standard.mono (Nat.m≤n⊔m i j)))))
    (E.strict (St.std k))

jump : T₀ → T₀
jump x = C.run x (E.above x)

rises : ∀ x → L.suc x ≼ jump x
rises x = ≼-trans {b = E.above x} (E.strict x) (Test.clock-below x (E.above x))

stages-from : T₀ → ℕ → T₀
stages-from x zero = x
stages-from x (suc n) = jump (stages-from x n)

hull : T₀ → T₀
hull x = L.lim (stages-from x)

stage = stages-from Seed.D

first-clock : E.above (L.ψ⁰ X.p) ≼ E.above Seed.D
first-clock = K.advance {L.ψ⁰ X.p} {Seed.D} (≅→≼ (L.≅-sym Entry.input))

old-end : C.run Seed.D (E.above (L.ψ⁰ X.p)) ≼ stage 1
old-end = both {Seed.D} {Seed.D} {E.above (L.ψ⁰ X.p)} {E.above Seed.D} (≼-refl Seed.D) first-clock

first-paid : stage 1 ≼ St.std 4
first-paid = ≼-trans {b = C.run Seed.D (E.above (L.ψ⁰ X.p))}
  (both {Seed.D} {Seed.D} {E.above Seed.D} {E.above (L.ψ⁰ X.p)} (≼-refl Seed.D)
    (K.advance {Seed.D} {L.ψ⁰ X.p} (≅→≼ Entry.input))) Ref.paid-end

tower : ℕ → ℕ
tower zero = 4
tower (suc n) = Orbit.five (tower n)

paid : ∀ n → stage (suc n) ≼ St.std (tower n)
paid zero = first-paid
paid (suc n) = Budget.run (tower n) x (E.above x) (paid n)
  (K.advance {x} {St.std (tower n)} (paid n))
  where x = stage (suc n)

past-family : ∀ t → C.Actual.H.In t → L.suc (C.run Seed.D t) ≼ stage 2
past-family t h = ≼-trans {b = L.suc (stage 1)}
  (s≼s (both {Seed.D} {Seed.D} {t} {E.above Seed.D} (≼-refl Seed.D)
    (≼-trans {b = L.suc t} (≼-suc (≼-refl t))
      (≼-trans {b = E.above (L.ψ⁰ X.p)} (C.Actual.H.finite {t} h) first-clock))))
  (rises (stage 1))

front : T₀
front = hull Seed.D

captured : front ≼ K.cut
captured = l≼ λ where
  zero → ≼l 2 (Orbit.point 0)
  (suc n) → ≼l (tower n) (paid n)

terminal : front ≼ Test.Y
terminal = ≼-trans {b = K.cut} captured K.terminal
```

从同一起点有限次任意交错地取下一 ε 数、用两个已有结果作起点和时钟，都留在这个上确界的严格初段中。下面同时核对上一轮时钟端点本身的严格界。

```agda
past-end : L.suc (C.run Seed.D (E.above (L.ψ⁰ X.p))) ≼ stage 2
past-end = ≼-trans {b = L.suc (stage 1)} (s≼s old-end) (rises (stage 1))

module Stages = Rising stage (λ n → rises (stage n))
open Stages using (under)

eps-closed : ∀ x → L.suc x ≼ front → L.suc (E.above x) ≼ front
eps-closed x h with ≼lim⁻ {a = x} {f = stage} h
... | n , d = under (suc n) (≼-trans {b = E.above (stage n)}
  (K.advance {x} {stage n} (≼-trans {b = L.suc x} (≼-suc (≼-refl x)) d))
  (Test.clock-below (stage n) (E.above (stage n))))

run-closed : ∀ x t → L.suc x ≼ front → L.suc t ≼ front → L.suc (C.run x t) ≼ front
run-closed x t hx ht with ≼lim⁻ {a = x} {f = stage} hx | ≼lim⁻ {a = t} {f = stage} ht
... | i , xi | j , tj = under (suc k) (both {x} {stage k} {t} {E.above (stage k)} lo clock)
  where
  k = i ⊔ j
  lo = ≼-trans {b = L.suc x} (≼-suc (≼-refl x))
    (≼-trans {b = stage i} xi (Stages.mono (Nat.m≤m⊔n i j)))
  clock = ≼-trans {b = L.suc (stage k)}
    (≼-suc (≼-trans {b = L.suc t} (≼-suc (≼-refl t))
      (≼-trans {b = stage j} tj (Stages.mono (Nat.m≤n⊔m i j))))) (E.strict (stage k))

least-closed : ∀ (b : T₀) → L.suc Seed.D ≼ b →
  (∀ x → L.suc x ≼ b → L.suc (E.above x) ≼ b) →
  (∀ x t → L.suc x ≼ b → L.suc t ≼ b → L.suc (C.run x t) ≼ b) → front ≼ b
least-closed b seed eps run = l≼ λ n → ≼-trans {b = L.suc (stage n)} (≼-suc (≼-refl _)) (inside n)
  where
  inside : ∀ n → L.suc (stage n) ≼ b
  inside zero = seed
  inside (suc n) = run (stage n) (E.above (stage n)) (inside n) (eps (stage n) (inside n))

enum : T₀ → T₀
enum L.zero = E.above L.zero
enum (L.suc t) = E.above (enum t)
enum (L.lim f) = L.lim (λ n → enum (f n))

index-below : ∀ t → t ≼ enum t
index-below L.zero = z≼
index-below (L.suc t) = ≼-trans {b = L.suc (enum t)} (s≼s (index-below t)) (E.strict (enum t))
index-below (L.lim f) = l≼ λ n → ≼l n (index-below (f n))

enum-in-run : ∀ x → E.above L.zero ≼ x → ∀ t → enum t ≼ C.run x t
enum-in-run x h L.zero = h
enum-in-run x h (L.suc t) = ≼-trans {b = E.above (C.run x t)}
  (K.advance {enum t} {C.run x t} (enum-in-run x h t)) (≼l 1 (≼l 1 (≼-refl _)))
enum-in-run x h (L.lim f) = l≼ λ n → ≼l n (enum-in-run x h (f n))

epsilon-seed : ∀ x → E.above L.zero ≼ jump x
epsilon-seed x = ≼-trans {b = E.above x} (K.advance {L.zero} {x} z≼)
  (Test.clock-below x (E.above x))

weaken : ∀ {x y : T₀} → L.suc x ≼ y → x ≼ y
weaken {x} h = ≼-trans {b = L.suc x} (≼-suc (≼-refl x)) h

hull-in-cut : ∀ x → L.suc x ≼ K.cut → hull x ≼ K.cut
hull-in-cut x seed = l≼ λ n → weaken (inside n)
  where
  f = stages-from x
  inside : ∀ n → L.suc (f n) ≼ K.cut
  inside zero = seed
  inside (suc n) = in-cut (f n) (E.above (f n)) (inside n) (K.inside {f n} (inside n))

hulls-cofinal : K.cut ≈ᵛ L.lim (λ n → hull (St.std n))
hulls-cofinal = (l≼ λ n → ≼l n (≼l 0 (≼-refl (St.std n)))) ,
  (l≼ λ n → hull-in-cut (St.std n) (≼l (suc n) (Shape.rise n)))

fixed-at : ∀ x → enum (hull x) ≼ hull x
fixed-at x = l≼ λ n → ≼l (suc (suc n)) (≼-trans {b = C.run (jump x) (f n)}
  (enum-in-run (jump x) (epsilon-seed x) (f n))
  (both {jump x} {f (suc n)} {f n} {E.above (f (suc n))} (H.mono (s≤s z≤n))
    (weaken (≼-trans {b = f (suc n)} (rises (f n)) (weaken (E.strict (f (suc n))))))))
  where
  f = stages-from x
  module H = Rising f (λ n → rises (f n))

cut-fixed : enum K.cut ≼ K.cut
cut-fixed = l≼ λ n → ≼-trans {b = C.run (stage 1) (St.std n)}
  (enum-in-run (stage 1) (epsilon-seed Seed.D) (St.std n))
  (weaken (in-cut (stage 1) (St.std n)
    (≼l 5 (≼-trans {b = L.suc (St.std 4)} (s≼s first-paid) (Shape.rise 4)))
    (≼l (suc n) (Shape.rise n))))
```

### 新下界的经典序数值

记 $D=\psi_0(\psi_2(\Omega_2+\Omega_1))$，$I(x,t)$ 为从 $x$ 起按时钟 $t$ 迭代对角运算，$s_0=D$，$s_{m+1}=I(s_m,\varepsilon^+(s_m))$，$V=\sup_m s_m$。按零、后继、上确界读零层树，代码中的 `enum` 给出正规函数 $\alpha\mapsto\varepsilon_\alpha$。其零值来自上方首个 ε 数的最小性，后继取下一个 ε 数，极限取上确界。对有最大值的分支族，单调性保证取得最大值。上述两向树值比较分别给出 $\varepsilon_V=V$ 与 $\varepsilon_K=K$，其中 $K$ 为独立标准塔的上确界。[上方首个 ε 数的最小性](Reports-2026-11-18/attachments/B22MovingIndex.agda.txt) · [ε 枚举与 Veblen 函数的约定](https://math.berkeley.edu/~antonio/papers/veblen.pdf)

**经典纸面标定。** $V$ 恰为满足 $\varepsilon_\lambda=\lambda$ 且 $\lambda>D$ 的最小序数。为证最小性，取任意这样的 $\lambda$。从一个 ε 数 $\varepsilon_b$ 出发，第 $k$ 个秩算子给出 $\varepsilon_{b+\omega^k}$。当 $k=0$ 时它取下一个 ε 数，每升一级则迭代前一算子所有有限次并取上确界。沿第 $1$ 到 $n$ 级依次作用，再对 $n$ 取上确界，得到对角值 $\varepsilon_{b+\omega^\omega}$。因而对时钟归纳，由右加和左乘关于右参数的连续性得到
$$
 I(\varepsilon_b,t)=\varepsilon_{b+\omega^\omega\cdot t}.
$$
对任意 $x,t<\lambda$，由 $\lambda=\sup_{b<\lambda}\varepsilon_b$ 可取 $b<\lambda$ 使 $x\le\varepsilon_b$。又 $\lambda$ 自身是 ε 数，故 $b+\omega^\omega\cdot t<\lambda$。由起点单调性得 $I(x,t)<\lambda$，而 $\varepsilon^+(x)\le\varepsilon_{b+1}<\lambda$。从 $D<\lambda$ 归纳得到每个 $s_m<\lambda$，故 $V\le\lambda$。`rises`、`fixed-at` 与 `index-below` 给出 $D<V$ 和 $\varepsilon_V=V$。以上推导对任一起点 $z$ 同样成立，因此 `hull z` 恰为 $z$ 上方首个 ε 枚举不动点，以下记作 $\zeta^+(z)$。由 `hull-in-cut`、`hulls-cofinal` 又得 $x<K\Rightarrow\zeta^+(x)\le K$ 和 $K=\sup_n\zeta^+(\mathrm{std}(n))$。[各级秩与对角运算](Reports-2026-11-19/attachments/B25ARank.agda.txt)
