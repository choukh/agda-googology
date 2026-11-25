# YiXVReadRouteFeed
> 验收文件。档位：编译定理。原 posW 的送回值等于实际槽位的送回值，实际槽位路径有 Route。
> 跟踪 YiLegPath 的原计算；不改树、折叠、UR、比较器。未交完整极限／节点世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteFeed where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as P
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadRouteInput as R
import OCF.Lean.YiXVReadOmegaInput as Ω

pos : ∀ cur (p : S.Pos (J.ℓ cur)) → J.ℓ (J.slot cur p) P.≤ J.ℓ cur
pos S.zero ()
pos (S.suc r) (inj₁ t) = P.ins P.self
pos (S.suc r) (inj₂ p) = P.ins (pos r p)
pos (S.lim f d) (n , inj₁ t) = P.inl n P.self
pos (S.lim f d) (n , inj₂ p) = P.inl n (pos (f n) p)
pos (S.Ω () g) p
pos (S.up r () y ny) p
route : ∀ cur p → R.Route cur (J.slot cur p) (pos cur p)
route S.zero ()
route (S.suc r) (inj₁ t) = R.ins R.here
route (S.suc r) (inj₂ p) = R.ins (route r p)
route (S.lim f d) (n , inj₁ t) = R.inl n R.here
route (S.lim f d) (n , inj₂ p) = R.inl n (route (f n) p)
route (S.Ω () g) p
route (S.up r () y ny) p
feed : ∀ cur p (Φ : ∀ j → j P.≤ J.ℓ cur → S.Tr j) →
  S.fromBr (J.ℓ cur) p (Φ (S.at (J.ℓ cur) p) (P.posW (J.ℓ cur) p)) ≡
  J.inB cur p (Φ (J.ℓ (J.slot cur p)) (pos cur p))
feed S.zero () Φ
feed (S.suc r) (inj₁ t) Φ = refl
feed (S.suc r) (inj₂ p) Φ = feed r p (λ j v → Φ j (P.ins v))
feed (S.lim f d) (n , inj₁ t) Φ = refl
feed (S.lim f d) (n , inj₂ p) Φ = feed (f n) p (λ j v → Φ j (P.inl n v))
feed (S.Ω () g) p Φ
feed (S.up r () y ny) p Φ

model-ω : ∀ n p → S.fromBr (J.ℓ Ω.ω) (n , p) (O.Ωt (S.at (J.ℓ Ω.ω) (n , p))) ≡
  J.inB Ω.ω (n , p) (O.Ωt (J.ℓ (J.slot Ω.ω (n , p))))
model-ω n p = feed Ω.ω (n , p) (λ j v → O.Ωt j)
```
