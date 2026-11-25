# YiXVReadNodeGrowth
> 验收文件。档位：编译定理。从参照 SC 律推出增长、任意目标输出与底部输出接口。
> 从 YiXVSourceGrowth/SourceNode* 与 ReadAffine* 推广，参照运算重用 Countable 接口；树、原折叠与 UR 未改。未交完整极限行、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadNodeGrowth where
open import Data.Product using (proj₁; proj₂)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAddFrame as Plus
import OCF.Lean.YiXVCountableFloor as Floor
import OCF.Lean.YiXVCountableChainInput as CI
import OCF.Lean.YiXVCountableFoldInput as Q
import OCF.Lean.YiXVCountableFold as Fold
import OCF.Lean.YiXVCountableGroundValue as Ground
import OCF.Lean.YiXVCountableZeroRead as Zero
open import OCF.Lean.YiXVLvlSteps using (Strong; read-strong)
import OCF.Lean.YiXVReadGrowthInput as Growth
import OCF.Lean.YiXVReadGrowth as Chain
import OCF.Lean.YiXVReadNodeGrowthInput as Model
import OCF.Lean.YiXVReadAffineNodeModels as M

module Frame {κ i} (sκ : Strong κ) (q : i L.<ᴵ κ)
  (f : L.U i (L.<→◃ q) → L.Ordᶜ κ)
  (law : A.Layer.SC κ A.Gd< A.Le< q f)
  (gb : ∀ X → A.Layer.GU κ A.Gd< A.Le< q X → A.Layer.Floor κ A.Gd< A.Le< q X →
    A.Gd (f (L.into (L.<→◃ q) X))) where
  module D = A.Layer κ A.Gd< A.Le<
  module I = A.Layer i A.Gd< A.Le<
  module Ops = Q.Ops (Fold.ops κ sκ)
  high : L.Ordᶜ i → L.Ordᶜ κ
  high X = f (L.into (L.<→◃ q) X)
  good : ∀ X → A.Gd X → A.Le (L.Ω i) X → A.Gd (high X)
  good X gx o = gb X (A.good-in (L.<→◃ q) gx) (A.le-in (L.<→◃ q) o)
  mono : ∀ X Y → A.Gd X → A.Gd Y → A.Le (L.Ω i) X → A.Le X Y → A.Le (high X) (high Y)
  mono X Y gx gy o t = D.SC.mo law X Y (A.good-in (L.<→◃ q) gx)
    (A.good-in (L.<→◃ q) gy) (A.le-in (L.<→◃ q) o) (A.le-in (L.<→◃ q) t)
  db : ∀ X → A.Gd X → A.Le (L.Ω i) X → A.Le (L.suc (high X)) (high (L.suc X))
  db X gx o = D.SC.db law X (A.good-in (L.<→◃ q) gx) (A.le-in (L.<→◃ q) o)
  P : L.Ordᶜ i → L.Ordᶜ i
  P X = L.ψ q (λ r → r) (high X)
  growth : Growth.Growth P
  CI.Input.good (Growth.Growth.input growth) X gx o = Ops.good sκ q (λ r → r) (good X gx o)
  CI.Input.floor (Growth.Growth.input growth) X gx o = Floor.floor q (λ r → r) (high X)
    (CI.Input.good (Growth.Growth.input growth) X gx o)
  Growth.Growth.mono growth X Y gx gy o t = Ops.mono sκ sκ q q (λ r → r) (λ r → r) (mono X Y gx gy o t)
  Growth.Growth.db growth X gx o = Ops.mono sκ sκ q q (λ r → r) (λ r → r) (db X gx o)
  Growth.Growth.initial growth = I.trans
    (Plus.mixed {σ = λ r → r} {τ = λ r → r}
      (I.rfl (proj₁ (Ω.model i))) (proj₂ (Ω.model i)))
    (I.trans (Chain.two≤ω (proj₁ (Ω.model i)))
      (Ops.mono sκ sκ q q (λ r → r) (λ r → r) (D.SC.po law)))
  module Target {ν a} (sa : Strong a) (pc : ν L.<ᴵ a) (ρ : L.Simᴵ κ a) where
    η : L.Ordᶜ i → L.Ordᶜ ν
    η X = L.ψ pc ρ (high X)
    output : Growth.Output η
    Growth.Output.good output X gx o = Ops.good sa pc ρ (good X gx o)
    Growth.Output.mono output X Y gx gy o t = Ops.mono sa sa pc pc ρ ρ (mono X Y gx gy o t)
    Growth.Output.db output X gx o = Ops.mono sa sa pc pc ρ ρ (db X gx o)
  module Bot {a} (sa : Strong a) (pc : L.zero L.<ᴵ a) (ρ : L.Simᴵ κ a) where
    η : L.Ordᶜ i → L.Ordᶜ L.zero
    η X = L.ψ⁰ (high X)
    output : Growth.Output η
    Growth.Output.good output X gx o = Ground.good (η X)
    Growth.Output.mono output X Y gx gy o t = Ground.native (Zero.mono sκ sa pc ρ (mono X Y gx gy o t))
    Growth.Output.db output X gx o = Ground.native (Zero.mono sκ sa pc ρ (db X gx o))

module Actual = Frame (read-strong M.r) L.zero M.f Model.law Model.body
actual : Growth.Growth Actual.P
actual = Actual.growth
```
