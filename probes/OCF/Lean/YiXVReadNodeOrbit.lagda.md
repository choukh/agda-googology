# YiXVReadNodeOrbit
> 验收文件。档位：编译定理。原节点回灌轨道与实际槽位坐标逐点对应，不用函数外延。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadNodeOrbit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadRouteFeed as Feed
import OCF.Lean.YiXVReadAffineNodeModels as Model
import OCF.Lean.YiXVReadGrowthInput as Growth
model-first : J.inB (S.suc S.zero) (inj₁ tt) S.zero ≡ S.br0 (J.ℓ (S.suc S.zero)) (inj₁ tt)
model-first = refl
first : ∀ cur p → J.inB cur p S.zero ≡ S.br0 (J.ℓ cur) p
first S.zero ()
first (S.suc r) (inj₁ t) = refl
first (S.suc r) (inj₂ p) = first r p
first (S.lim f d) (n , inj₁ t) = refl
first (S.lim f d) (n , inj₂ p) = first (f n) p
first (S.Ω () g) p
first (S.up r () y ny) p

module Orbit (cur : S.Tr S.zero) (p : S.Pos (J.ℓ cur)) (SrcB : Fold.Base (J.ℓ cur))
  (g : S.Br (J.ℓ cur) p → S.Tr (J.ℓ cur)) where
  i = J.slot cur p
  v = Feed.pos cur p
  fold : S.Br (J.ℓ cur) p → S.Tr (J.ℓ i)
  fold z = Fold.ψs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (J.ℓ i) v
    (Fold.bs SrcB (J.ℓ i) v) (Fold.ns SrcB (J.ℓ i) v) (g z)
  step : S.Tr (J.ℓ i) → S.Tr (J.ℓ i)
  step a = fold (J.inB cur p a)
  actual-step : S.Br (J.ℓ cur) p → S.Br (J.ℓ cur) p
  actual-step z = S.fromBr (J.ℓ cur) p
    (Fold.ψs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (S.at (J.ℓ cur) p) (Path.posW (J.ℓ cur) p)
      (Fold.bs SrcB (S.at (J.ℓ cur) p) (Path.posW (J.ℓ cur) p))
      (Fold.ns SrcB (S.at (J.ℓ cur) p) (Path.posW (J.ℓ cur) p)) (g z))
  br : ℕ → S.Br (J.ℓ cur) p
  br = O.iter actual-step (S.br0 (J.ℓ cur) p)
  c : ℕ → S.Tr (J.ℓ i)
  c n = J.outB cur p (br n)
  feed : ∀ z → actual-step z ≡ J.inB cur p (fold z)
  feed z = Feed.feed cur p (λ j v → Fold.ψs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB j v
    (Fold.bs SrcB j v) (Fold.ns SrcB j v) (g z))
  orbit : Growth.Orbit i step
  Growth.Orbit.points orbit = c
  Growth.Orbit.start orbit = trans (cong (J.outB cur p) (sym (first cur p))) (J.out-in cur p S.zero)
  Growth.Orbit.next orbit n = trans (cong (J.outB cur p) (feed (br n)))
    (trans (J.out-in cur p (fold (br n))) (cong fold (sym (J.in-out cur p (br n)))))
  row : ∀ {j : S.L} (Φ : S.Tr (J.ℓ cur) → S.Tr j) n →
    Φ (g (J.inB cur p (c n))) ≡ Φ (g (br n))
  row Φ n = cong (λ z → Φ (g z)) (J.in-out cur p (br n))
module Actual = Orbit Model.r (inj₁ tt) (Fold.B₀ (J.ℓ Model.r)) Model.g
actual : Growth.Orbit S.zero Actual.step
actual = Actual.orbit
```
