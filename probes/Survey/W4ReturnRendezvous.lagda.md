# 同一次真实反馈的旧起点与新返回

第四层。若一个单位返回严格超过一座完整的旧塔，地址的先后次序由值比较决定。用这条性质，可以同时在真实起点保留旧塔、在同一调用的单位返回中严格超过指定的参照值。记 Mₖ 为恢复轨道的第 k 个参照值，R 为其上确界。对每个 k，只要选一次这样的调用，另给它一个具名上界 Mₐ，就足以证明整树同值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnRendezvous where

open import Data.Nat.Base as Nat using (ℕ; suc; _⊔_; _<_; _≤_)
import Data.Nat.Properties as N
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import WVOne using (T₀; read)
open import OCF.Lean.YiRVLevel using (LEM)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-suc; ≼-trans; ≼lim⁻; s≼s)
open import OCF.Align.TightValBase using (s≼-irrefl)
import B12EboRows as Rows
import B17CellNext as Next
import B17CellPrefix as Cell
import B17ValueDich as Order
import B18CellState as State
import B18Reset as Reset
import B18ResetCell as Unit
import B18Product as Mul
import B19Coefficient as Product
import B20StandardGoal as Standard
import B20StandardInside as St
import B28Branches as Branch
import B28PReference as Small
import B26Names as Names
import B26PActual as W
import B26PSums as Sums
import B27UEnvelope as Env
import B27Joint as Joint
import B28Acceptance as Acc
import B28Orbit as Orbit
import B28OrbitValue as Ref
import B28Sparse as Sparse

M : ℕ → T₀
M = Orbit.value
R : T₀
R = Names.E
base : ℕ → ℕ → T₀
base = λ n j → read (proj₁ (Next.At.b n j))
unit : ℕ → ℕ → T₀
unit = Unit.At.fresh
tower : ℕ → T₀
tower = Rows.child

walk : ∀ {i n} → i ≤ n → tower i ≼ tower n
walk {i} {n} le = Next.walk {i} {n} (N.≤⇒≤′ le)

rise : ∀ i → L.suc (tower i) ≼ tower (suc i)
rise i = ≼-trans {b = Cell.cell i 0} (Next.strict i 0) (Cell.At.S.lift-value i 0)

within : ∀ n j → unit n j ≼ tower (suc n)
within n j = ≼-trans {b = Reset.fresh (suc n)} (Unit.At.into n j) (Reset.lower (suc n))

later : ∀ i n j → L.suc (tower (suc i)) ≼ unit n j → i < n
later i n j hit with N.≤-total (suc i) n
... | inj₁ d = d
... | inj₂ d with N.m≤n⇒m<n∨m≡n d
...   | inj₂ eq = subst (suc i ≤_) (sym eq) N.≤-refl
...   | inj₁ lt = ⊥-elim (s≼-irrefl (tower (suc i))
  (≼-trans {b = unit n j} hit (≼-trans {b = tower (suc n)} (within n j) (walk lt))))

record Return (i k n j : ℕ) : Set where
  field
    forward : i < n
    inherited : L.suc (tower i) ≼ base n j
    repeated : L.suc (tower i) ≼ unit n j
    target : L.suc (M k) ≼ unit n j

  actual : Cell.cell n j ≈ᵛ (base n j Mul.· unit n j)
  actual = subst (λ x → Cell.cell n j ≈ᵛ (x Mul.· unit n j)) (sym (State.prior n j))
    (Product.Cell.exact-cell n j)

join : ∀ i k n j → L.suc (tower (suc i)) ≼ unit n j → L.suc (M k) ≼ unit n j → Return i k n j
join i k n j fresh high = record
  { forward = d
  ; inherited = ≼-trans {b = tower n}
      (≼-trans {b = tower (suc i)} (rise i) (walk d)) (Next.At.before n j)
  ; repeated = ≼-trans {b = L.suc (tower (suc i))} (s≼s (Cell.promote i)) fresh
  ; target = high }
  where d = later i n j fresh

-- 第零座旧塔与第零个参照由同一次调用两边同时兑现，后续塔及其询问可任取。
seed : ∀ n j → Return 0 0 (suc n) j
seed n j = record
  { forward = Nat.s≤s Nat.z≤n
  ; inherited = ≼-trans {b = tower (suc n)} (≼-trans {b = tower 1} (rise 0)
      (walk {1} {suc n} (Nat.s≤s Nat.z≤n))) (Next.At.before (suc n) j)
  ; repeated = Standard.At.child n j 0 Nat.z≤n
  ; target = ≼-trans {b = L.suc (St.std 1)}
      (s≼s (≼-trans {b = Sparse.point 0 1} (Sparse.low 0 1) (Small.two (Branch.At.Head.at 0 1))))
      (Standard.At.child n j 1 (Nat.s≤s Nat.z≤n)) }

After : ℕ → ℕ → Set
After i k = Σ ℕ (λ n → Σ ℕ (Return i k n))

-- 一个比旧塔稍高的参照下标可同时约束两个读值；选择地址时没有使用排中律。
locate : Acc.Units → ∀ i k → L.suc (tower (suc i)) ≼ R → After i k
locate paid i k small = n , j , join i k n j exceeds-old exceeds-target
  where
  pick = ≼lim⁻ {a = tower (suc i)} {f = M}
    (≼-trans {a = L.suc (tower (suc i))} {b = R} {c = L.lim M} small (proj₁ Ref.complete))
  t = proj₁ pick
  h = t ⊔ k
  receipt = paid h
  n = proj₁ receipt
  j = proj₁ (proj₂ receipt)
  monotone : ∀ a → a ≤ h → M a ≼ M h
  monotone a d = Sparse.Actual.move {n = a} {k = h} (N.≤⇒≤′ d)
  exceeds-old : L.suc (tower (suc i)) ≼ unit n j
  exceeds-old = ≼-trans {a = L.suc (tower (suc i))} {b = M t} {c = unit n j} (proj₂ pick)
    (≼-trans {a = M t} {b = M h} {c = unit n j} (monotone t (N.m≤m⊔n t k))
     (≼-trans {a = M h} {b = L.suc (M h)} {c = unit n j} (≼-suc (≼-refl (M h))) (proj₂ (proj₂ receipt))))
  exceeds-target : L.suc (M k) ≼ unit n j
  exceeds-target = ≼-trans {a = L.suc (M k)} {b = L.suc (M h)} {c = unit n j}
    (s≼s (monotone k (N.m≤n⊔m t k))) (proj₂ (proj₂ receipt))

Local = ∀ i k → After i k
Early = Σ ℕ (λ i → R ≼ tower i)

lower : Early ⊎ Local → R ≼ W.Y
lower (inj₁ (i , h)) = Rows.into {x = R} (i , h)
lower (inj₂ f) = Acc.enough λ k → receipt k (f 0 k)
  where
  receipt : ∀ k → After 0 k → Joint.Hit (M k)
  receipt k (n , j , r) = n , j , Return.target {i = 0} {k = k} {n = n} {j = j} r

overshoot : Early → L.suc R ≼ W.Y
overshoot (i , h) = ≼-trans {b = L.suc (tower i)} (s≼s h) (Sums.child-in i)

-- 同一批单位返回给出两边比较。上界只查选中的调用。
record Bracket (k : ℕ) : Set where
  constructor bracket
  field
    n j a : ℕ
    step : Return k k n j
    ceiling : unit n j ≼ M a

Diagonal = ∀ k → Bracket k

from-diagonal : Diagonal → R ≈ᵛ W.Y
from-diagonal chain = Acc.enough (λ k → hits k (chain k)) , Next.assemble {q = R} (λ k → caps k (chain k))
  where
  hits : ∀ k → Bracket k → Joint.Hit (M k)
  hits k (bracket n j a r hi) = n , j , Return.target {i = k} {k = k} {n = n} {j = j} r
  caps : ∀ k → Bracket k → tower k ≼ R
  caps k (bracket n j a r hi) = ≼-trans {a = tower k} {b = L.suc (tower k)} {c = R}
    (≼-suc (≼-refl (tower k)))
    (≼-trans {a = L.suc (tower k)} {b = unit n j} {c = R}
      (Return.repeated {i = k} {k = k} {n = n} {j = j} r)
      (≼-trans {a = unit n j} {b = M a} {c = R} hi
        (≼-trans {a = M a} {b = L.suc (M a)} {c = R} (≼-suc (≼-refl (M a))) (Names.strict (Orbit.target a)))))

module Classical (lem : LEM) where
  inside : (Early → Data.Empty.⊥) → ∀ i → L.suc (tower i) ≼ R
  inside no i = choose (Order.Classical.compare lem R (tower i))
    where
    choose : (R ≼ tower i) ⊎ (L.suc (tower i) ≼ R) → L.suc (tower i) ≼ R
    choose (inj₁ h) = ⊥-elim (no (i , h))
    choose (inj₂ h) = h
  alternatives : R ≼ W.Y → Early ⊎ Local
  alternatives goal = choose (lem Early)
    where
    choose : Early ⊎ (Early → Data.Empty.⊥) → Early ⊎ Local
    choose (inj₁ w) = inj₁ w
    choose (inj₂ no) = inj₂ λ i k → locate (Acc.Classical.all-units lem goal) i k (inside no (suc i))

  equality-forces : R ≈ᵛ W.Y → Local
  equality-forces (lo , hi) i k = locate (Acc.Classical.all-units lem lo) i k
    (≼-trans {b = W.Y} (Sums.child-in (suc i)) hi)
  to-diagonal : R ≈ᵛ W.Y → Diagonal
  to-diagonal eq k = finish (equality-forces eq k k)
    where
    finish : After k k → Bracket k
    finish (n , j , r) = bracket n j (proj₁ bound) r
      (≼-trans {a = unit n j} {b = L.suc (unit n j)} {c = M (proj₁ bound)}
        (≼-suc (≼-refl (unit n j))) (proj₂ bound))
      where
      bound = ≼lim⁻ {a = unit n j} {f = M}
        (≼-trans {a = L.suc (unit n j)} {b = W.Y} {c = L.lim M}
          (≼-trans {a = L.suc (unit n j)} {b = L.suc (tower (suc n))} {c = W.Y}
            (s≼s (within n j)) (Sums.child-in (suc n)))
          (≼-trans {a = W.Y} {b = R} {c = L.lim M} (proj₂ eq) (proj₁ Ref.complete)))
```

设 tₖ 为 Λ 的第 k 个完整塔返回，u 为被选调用从 1 起算的返回。同值的充分条件是每个 k 能找到一处真实调用，使其起点严格超过 tₖ，且 tₖ < u、Mₖ < u ≤ Mₐ。前两个严格下界各有用途。由 Mₖ < u 得 R ≤ Y，由 tₖ < u ≤ Mₐ < R 得 Y ≤ R。排中律下，同值也能反取这一组见证。起始实例 `seed` 已经同时兑现 t₀ 和 M₀ 的严格下界。对所有 k 构造这种有上下界的调用仍开放。
