# YiXVReadRouteWorldInput
> 验收文件。档位：编译定理。只对带 Route 的原路径量化的世界与输出接口；旧全路径接口给出其实例，含 pt 2。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRouteWorldInput where
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOutInput as O
import OCF.Lean.YiXVReadWorldInput as Old
import OCF.Lean.YiXVReadWorldStart as Start
import OCF.Lean.YiXVReadOmegaInput as Ω
import OCF.Lean.YiXVReadRouteInput as R

record World (root cur : S.Tr S.zero) (within : cur P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ cur))
  (Z : L.Ordᶜ (T.lvl root)) : Set where
  field
    good : A.Gd Z
    bot : Read.read (Fold.b⊥ SrcB) ≼ L.ψ⁰ Z
    slots : ∀ y (p : y P.≤ᵀ root) (v : J.ℓ y Path.≤ J.ℓ cur) → R.Route cur y v →
      U.UR y (Fold.bs SrcB (J.ℓ y) v) (Old.φ p Z)
record Out (root cur : S.Tr S.zero) (within : cur P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ cur))
  (Z : L.Ordᶜ (T.lvl root)) (a : S.Tr (J.ℓ cur)) (X : L.Ordᶜ (T.lvl cur)) : Set where
  field
    good : A.Gd (O.cap within Z X)
    bot : Read.read (Fold.ψ⊥ (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB a) ≼ L.ψ⁰ (O.cap within Z X)
    slots : ∀ y (p : y P.≤ᵀ root) (v : J.ℓ y Path.≤ J.ℓ cur) → R.Route cur y v →
      U.UR y (Fold.ψs (J.ℓ cur) (T.εh cur) (T.ρh cur) SrcB (J.ℓ y) v
        (Fold.bs SrcB (J.ℓ y) v) (Fold.ns SrcB (J.ℓ y) v) a) (Old.φ p (O.cap within Z X))
from-world : ∀ {root cur within SrcB Z} → Old.World root cur within SrcB Z → World root cur within SrcB Z
World.good (from-world w) = Old.World.good w
World.bot (from-world w) = Old.World.bot w
World.slots (from-world w) y p v rv = Old.World.slots w y p v
from-out : ∀ {root cur within SrcB Z a X} → O.Out root cur within SrcB Z a X → Out root cur within SrcB Z a X
Out.good (from-out h) = O.Out.good h
Out.bot (from-out h) = O.Out.bot h
Out.slots (from-out h) y p v rv = O.Out.slots h y p v

model₀ : World S.zero S.zero P.here (Fold.B₀ (J.ℓ S.zero)) (Old.seed S.zero)
model₀ = from-world Old.model₀
model₁ : World (S.suc S.zero) (S.suc S.zero) P.here (Fold.B₀ (J.ℓ (S.suc S.zero))) (Old.seed (S.suc S.zero))
model₁ = from-world Old.model₁
model-ω : World Ω.ω Ω.ω P.here (Fold.B₀ (J.ℓ Ω.ω)) (Old.seed Ω.ω)
model-ω = from-world (Start.initial Ω.ω)
actual₂ : World (T.pt 2) (T.pt 2) P.here (Fold.B₀ (J.ℓ (T.pt 2))) (Old.seed (T.pt 2))
actual₂ = from-world (Start.initial (T.pt 2))
```
