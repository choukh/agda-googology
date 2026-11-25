# YiXVReadRouteWay
> 验收文件。档位：编译定理。原 rt/way 返回的精确路径有 Route，比较仍只在自然数孩子编号上。
> 跟踪 YiLegPath 的原计算；不改树、折叠、UR、比较器。未交完整极限／节点世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteWay where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₂)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRoute as Route
import OCF.Lean.YiXVReadOmegaInput as Ω
import OCF.Lean.YiXVReadRouteStep as Step

module Family (f : ℕ → S.Tr S.zero) (d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)) where
  g = λ n → J.ℓ (f n)
  adj = proj₂ (T.ρh (S.lim f d))
  Cert : ∀ m n → P.Way g m n → Set
  Cert m n (P.fwd v) = R.Route (f n) (f m) v
  Cert m n (P.bwd v) = R.Route (f m) (f n) v
  model₀ : Cert 0 0 (P.way g adj 0 0)
  model₀ = R.here
  model₊ : Cert 0 1 (P.way g adj 0 1)
  model₊ = Step.adj f d 0
  model₋ : Cert 1 0 (P.way g adj 1 0)
  model₋ = Step.adj f d 0

  rt : ∀ {m n} (l : m P.<ₙ n) → R.Route (f n) (f m) (P.rt g adj l)
  rt P.here = Step.adj f d _
  rt (P.nxt {n} l) = Route.compose (Step.adj f d n) (rt l)
  way′ : ∀ {m n} (c : P.Cmp m n) → Cert m n (P.way′ g adj c)
  way′ P.eq = R.here
  way′ (P.lt l) = rt l
  way′ (P.gt l) = rt l
  way : ∀ m n → Cert m n (P.way g adj m n)
  way m n = way′ (P.cmp m n)

module Actual = Family Ω.nat (λ n → S.◃s)
actual-ω : ∀ m n → Actual.Cert m n (P.way Actual.g Actual.adj m n)
actual-ω = Actual.way
```
