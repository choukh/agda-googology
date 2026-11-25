# YiXVReadRouteRules
> 验收文件。档位：编译定理。Route 世界的零、后继、弱化、极限与零参照增量输出；参照运算复用旧保持律。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteRules where
open import Data.Product using (proj₁)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
open import OCF.Lean.YiCeilRead using (next≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans; l≼)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadNext as Next
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOutInput as O
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadWorldStart as Start
import OCF.Lean.YiXVReadRules as Legacy
import OCF.Lean.YiXVReadPhi as Phi
import OCF.Lean.YiXVReadRouteWorldInput as W

module Rules {root cur} (within : cur P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ cur))
  (Z : L.Ordᶜ (T.lvl root)) (w : W.World root cur within SrcB Z) where
  Result = W.Out root cur within SrcB Z
  module Ref = Legacy.Rules root cur within (Fold.B₀ (J.ℓ cur)) (Old.seed root) (Start.initial-any root cur within)
  neutral : Result S.zero L.zero
  W.Out.good neutral = W.World.good w
  W.Out.bot neutral = W.World.bot w
  W.Out.slots neutral y p v rv = W.World.slots w y p v rv
  zero : Result S.zero (L.Ω (T.lvl cur))
  W.Out.good zero = Add.good (W.World.good w) (proj₁ (Ω.model (T.lvl cur)))
  W.Out.bot zero = ≼-trans (W.World.bot w) (Ref.value-mono
    (Add.right {σ = O.σ within} (W.World.good w) (proj₁ (Ω.model (T.lvl cur)))))
  W.Out.slots zero y p v rv = B.weak y (W.World.slots w y p v rv) (Phi.Frame.mono p
    (Add.right {σ = O.σ within} (W.World.good w) (proj₁ (Ω.model (T.lvl cur)))))
  suc : ∀ {a X} → A.Gd X → Result a X → Result (S.suc a) (L.suc X)
  W.Out.good (suc gx h) = Add.good (W.World.good w) (A.Layer.gs gx)
  W.Out.bot (suc {a} gx h) = next≼ _ (Fold.nz⊥ (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB a) (W.Out.bot h)
  W.Out.slots (suc {a} gx h) y p v rv = Next.next y
    (Fold.nzs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (J.ℓ y) v (Fold.bs SrcB (J.ℓ y) v) (Fold.ns SrcB (J.ℓ y) v) a)
    (Old.φ-good p (W.Out.good h)) (W.Out.slots h y p v rv)
  weak : ∀ {a X Y} → Result a X → A.Le X Y → Result a Y
  W.Out.good (weak h t) = Add.good (W.World.good w) (A.Layer.right (T.lvl cur) A.Gd< A.Le< t)
  W.Out.bot (weak h t) = ≼-trans (W.Out.bot h) (Ref.value-mono (Add.mono {σ = O.σ within} (W.World.good w) t))
  W.Out.slots (weak h t) y p v rv = B.weak y (W.Out.slots h y p v rv)
    (Phi.Frame.mono p (Add.mono {σ = O.σ within} (W.World.good w) t))
  lim : ∀ {f d X} → (∀ n → Result (f n) X) → Result (S.lim f d) X
  W.Out.good (lim h) = W.Out.good (h 0)
  W.Out.bot (lim h) = l≼ (λ n → W.Out.bot (h n))
  W.Out.slots (lim h) y p v rv = B.limU y (λ n → W.Out.slots (h n) y p v rv)

module M = Rules {root = S.suc S.zero} {cur = S.suc S.zero} P.here (Fold.B₀ (J.ℓ (S.suc S.zero)))
  (Old.seed (S.suc S.zero)) W.model₁
actual : M.Result S.zero (L.Ω (L.suc L.zero))
actual = M.zero
```
