# YiXVReadWorldStart
> 验收文件。档位：编译定理。每个实际根的 B₀ 初始世界所有字段均实填，含原 pt 2 闭实例；尚无递归保持或外层行上界。
> 保留原 h₁、lvl、B₀ 与折叠；初始化参照取 read(root) 的零前缀嵌入。未交原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadWorldStart where
open import Data.Unit using (tt)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSRead as Read
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ⊑→≼; 1≼ψ⁰)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableGroundValue as G
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadOmega as O
import OCF.Lean.YiXVReadCapBound as C
import OCF.Lean.YiXVFlatInput as F
import OCF.Lean.YiXVNeutral as N
open import OCF.Lean.YiXVLvlSteps using (read-strong)
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
weak-value : ∀ {x y} → x P.≤ᵀ y → Read.read x ≼ Read.read y
weak-value {x} P.here = ≼-refl (Read.read x)
weak-value {x} (P.below p) = ⊑→≼ (Read.read x) (Read.◃⊑ (P.raw p))
same : ∀ {root y} (p : y P.≤ᵀ root) →
  W.φ p (W.seed root) L.≅ F.flat (T.lvl y) (F.empty (T.lvl y)) (Read.read root)
same {root} {y} p = L.ψ-≅ {p = W.pc p} {σ = λ q → L.suc q}
  {p′ = L.zero {a = T.lvl y}} {σ′ = F.insert (F.empty (T.lvl y))}
  (L.≅ᴵ-refl (T.lvl y)) (N.neutral L.z≅ (L.≅-refl⁰ (Read.read root)))
cap-bound : ∀ {root y} (p : y P.≤ᵀ root) → A.Le (O.cap y) (W.φ p (W.seed root))
cap-bound {root} {y} p = D.trans (C.bound y) (D.trans
  (F.mono {κ = L.zero} {ν = T.lvl y} tt (read-strong y)
    (F.empty (T.lvl y)) (F.empty (T.lvl y)) (G.native (weak-value p)))
  (D.pack (F.good {κ = L.zero} {ν = T.lvl y} tt (read-strong y)
      (F.empty (T.lvl y)) (G.good (Read.read root)))
    (W.φ-good p (W.seed-good root)) (D.ce (L.≅-sym (same p)))))
  where module D = A.Layer (T.lvl y) A.Gd< A.Le<
initial-any : ∀ root x (within : x P.≤ᵀ root) →
  W.World root x within (Fold.B₀ (J.ℓ x)) (W.seed root)
W.World.good (initial-any root x within) = W.seed-good root
W.World.bot (initial-any root x within) = 1≼ψ⁰ (W.seed root)
W.World.slots (initial-any root x within) y p v = B.weak y (O.cover y) (cap-bound p)
initial : ∀ root → W.World root root P.here (Fold.B₀ (J.ℓ root)) (W.seed root)
initial root = initial-any root root P.here

actual₂ : W.World (T.pt 2) (T.pt 2) P.here (Fold.B₀ (J.ℓ (T.pt 2))) (W.seed (T.pt 2))
actual₂ = initial (T.pt 2)
```
