# YiXVReadRules
> 验收文件。档位：编译定理。完整 Out 的零、后继、弱化与自然极限保持，保留全局根坐标。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadRules where
open import Data.Product using (proj₁)
open import OCF.Lean.YiCeilRead using (next≼)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableFoldInput as Q
import OCF.Lean.YiXVCountableFold as F
import OCF.Lean.YiXVCountableZeroRead as Z
import OCF.Lean.YiXVReadEnv as Env
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadWorldStart as Start
open import OCF.Lean.YiXVLvlSteps using (read-strong)
import OCF.Lean.YiXVReadNext as Next
import OCF.Lean.YiXVReadOutInput as O
module Rules (root x : S.Tr S.zero) (within : x P.≤ᵀ root) (SrcB : Fold.Base (J.ℓ x))
  (Z₀ : L.Ordᶜ (T.lvl root)) (w : W.World root x within SrcB Z₀) where
  Result = O.Out root x within SrcB Z₀
  φ-mono : ∀ {y} (p : y P.≤ᵀ root) {X Y} → A.Le X Y → A.Le (W.φ p X) (W.φ p Y)
  φ-mono {y} p = Q.Ops.mono (F.ops (T.lvl root) (read-strong root))
    {ν = T.lvl y} {a = L.suc (T.lvl root)} {b = L.suc (T.lvl root)}
    (read-strong root) (read-strong root) (W.pc p) (W.pc p) (λ q → L.suc q) (λ q → L.suc q)
  value-mono : ∀ {X Y} → A.Le {T.lvl root} X Y → L.ψ⁰ X ≼ L.ψ⁰ Y
  value-mono t = Z.mono {κ = T.lvl root} {a = L.suc (T.lvl root)}
    (read-strong root) (read-strong root) (Env.zero-bound root) (λ q → L.suc q) t

  zero-out : Result S.zero (L.Ω (T.lvl x))
  O.Out.good zero-out = Add.good (W.World.good w) (proj₁ (Ω.model (T.lvl x)))
  O.Out.bot zero-out = ≼-trans (W.World.bot w)
    (value-mono (Add.right {σ = O.σ within} (W.World.good w) (proj₁ (Ω.model (T.lvl x)))))
  O.Out.slots zero-out y p v = B.weak y (W.World.slots w y p v)
    (φ-mono p (Add.right {σ = O.σ within} (W.World.good w) (proj₁ (Ω.model (T.lvl x)))))

  suc-out : ∀ {a X} → A.Gd X → Result a X → Result (S.suc a) (L.suc X)
  O.Out.good (suc-out gx h) = Add.good (W.World.good w) (A.Layer.gs gx)
  O.Out.bot (suc-out {a} gx h) = next≼ _ (Fold.nz⊥ (J.ℓ x) (T.εh x) (T.ρh x) SrcB a) (O.Out.bot h)
  O.Out.slots (suc-out {a} gx h) y p v = Next.next y
    (Fold.nzs (J.ℓ x) (T.εh x) (T.ρh x) SrcB (J.ℓ y) v
      (Fold.bs SrcB (J.ℓ y) v) (Fold.ns SrcB (J.ℓ y) v) a)
    (W.φ-good p (O.Out.good h)) (O.Out.slots h y p v)

  weak-out : ∀ {a X Y} → Result a X → A.Le X Y → Result a Y
  O.Out.good (weak-out h t) = Add.good (W.World.good w) (A.Layer.right (T.lvl x) A.Gd< A.Le< t)
  O.Out.bot (weak-out h t) = ≼-trans (O.Out.bot h) (value-mono (Add.mono {σ = O.σ within} (W.World.good w) t))
  O.Out.slots (weak-out h t) y p v = B.weak y (O.Out.slots h y p v)
    (φ-mono p (Add.mono {σ = O.σ within} (W.World.good w) t))

  lim-out : ∀ {f a X} → (∀ n → Result (f n) X) → Result (S.lim f a) X
  O.Out.good (lim-out h) = O.Out.good (h 0)
  O.Out.bot (lim-out h) = l≼ (λ n → O.Out.bot (h n))
  O.Out.slots (lim-out h) y p v = B.limU y (λ n → O.Out.slots (h n) y p v)

module Model = Rules (S.suc S.zero) (S.suc S.zero) P.here
  (Fold.B₀ (J.ℓ (S.suc S.zero))) (W.seed (S.suc S.zero))
  (Start.initial (S.suc S.zero))
actual : Model.Result S.zero (L.Ω (L.suc L.zero))
actual = Model.zero-out

actual-suc : Model.Result (S.suc S.zero) (L.suc (L.Ω (L.suc L.zero)))
actual-suc = Model.suc-out A.oneΩ actual
```
