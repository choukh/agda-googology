# YiXVReadRouteStep
> 验收文件。档位：编译定理。每个实际第一位置步进的原路径有 Route，包含原 ρh 的精确相邻字段。
> 跟踪 YiLegPath 的原计算；不改树、折叠、UR、比较器。未交完整极限／节点世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteStep where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadOmegaInput as Ω
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadRoute as Route
import OCF.Lean.YiXVReadFinitePathInput as Fin
import OCF.Lean.YiXVReadFinitePath as F

finite : ∀ {x y : S.Tr S.zero} (d : S.zero S.⊢ x ◃ y) → Fin.Finite (P.◃→⊑ S.zero d)
finite S.◃s = Fin.ins Fin.self
finite (S.◃l n) = Fin.inl n Fin.self
finite (S.◃w {p = ()})
finite (S.◃u x () y e)
finite (S.◃c x () d)
finite (S.◃t p q) = F.compose (finite p) (finite q)
path : ∀ {x y : S.Tr S.zero} → S.zero S.⊢ x ◃ y → J.ℓ x P.≤ J.ℓ y
path d = P.⊑→≤ (P.⊕⊑ S.zero (P.◃→⊑ S.zero d))
step : ∀ {x y : S.Tr S.zero} (d : S.zero S.⊢ x ◃ y) → R.Route y x (path d)
step S.◃s = R.ins R.here
step (S.◃l n) = R.inl n R.here
step (S.◃w {p = ()})
step (S.◃u x () y e)
step (S.◃c x () d)
step (S.◃t {x} {y} {z} p q) = subst (R.Route z x) (sym eq) (Route.compose (step q) (step p))
  where
  eq = trans (cong P.⊑→≤ (F.map-compose S.zero (P.◃→⊑ S.zero p) (finite q)))
    (F.to-compose (P.⊕⊑ S.zero (P.◃→⊑ S.zero p)) (F.map S.zero (finite q)))

adj : ∀ (f : ℕ → S.Tr S.zero) (d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)) n →
  R.Route (f (suc n)) (f n) (proj₂ (T.ρh (S.lim f d)) n)
adj f d n = step (d n)
model-ω : ∀ n → R.Route (Ω.nat (suc n)) (Ω.nat n) (proj₂ (T.ρh Ω.ω) n)
model-ω = adj Ω.nat (λ n → S.◃s)
```
