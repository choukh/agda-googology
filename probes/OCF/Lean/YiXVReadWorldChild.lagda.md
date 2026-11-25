# YiXVReadWorldChild
> 验收文件。档位：编译定理。完整 Out 给出后继孩子与自然极限孩子的新世界，槽位按原 ins/inl 路径更新。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadWorldChild where
open import Data.Nat using (ℕ)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadWorldStart as Start
import OCF.Lean.YiXVReadOmegaInput as ΩInput
import OCF.Lean.YiXVReadOutInput as O
import OCF.Lean.YiXVReadRules as Rules
import OCF.Lean.YiXVReadCoordinates as C
suc-child : ∀ {root x} (within : S.suc x P.≤ᵀ root)
  (B : Fold.Base (J.ℓ (S.suc x))) (Z : L.Ordᶜ (T.lvl root))
  {a X} → O.Out root (S.suc x) within B Z a X →
  W.World root x (C.inside P.root within)
    (Fold.dS (J.ℓ x) (T.εh (S.suc x)) (T.ρh (S.suc x)) B a) (O.cap within Z X)
W.World.good (suc-child within B Z h) = O.Out.good h
W.World.bot (suc-child within B Z h) = O.Out.bot h
W.World.slots (suc-child within B Z h) y p v = O.Out.slots h y p (Path.ins v)

lim-child : ∀ {root f d} (within : S.lim f d P.≤ᵀ root)
  (B : Fold.Base (J.ℓ (S.lim f d))) (Z : L.Ordᶜ (T.lvl root)) (n : ℕ)
  {a X} → O.Out root (S.lim f d) within B Z a X →
  W.World root (f n) (C.inside (P.branch n) within)
    (Fold.dL (λ k → J.ℓ (f k)) (T.εh (S.lim f d)) (T.ρh (S.lim f d)) B n a) (O.cap within Z X)
W.World.good (lim-child within B Z n h) = O.Out.good h
W.World.bot (lim-child within B Z n h) = O.Out.bot h
W.World.slots (lim-child within B Z n h) y p v = O.Out.slots h y p (Path.inl n v)

module Model = Rules.Rules (S.suc S.zero) (S.suc S.zero) P.here
  (Fold.B₀ (J.ℓ (S.suc S.zero))) (W.seed (S.suc S.zero)) (Start.initial (S.suc S.zero))
actual-suc : W.World (S.suc S.zero) S.zero (P.below P.root)
  (Fold.dS S.zero (T.εh (S.suc S.zero)) (T.ρh (S.suc S.zero))
    (Fold.B₀ (J.ℓ (S.suc S.zero))) S.zero)
  (O.cap P.here (W.seed (S.suc S.zero)) (L.Ω (L.suc L.zero)))
actual-suc = suc-child P.here (Fold.B₀ (J.ℓ (S.suc S.zero))) (W.seed (S.suc S.zero)) Model.zero-out

module LimModel = Rules.Rules ΩInput.ω ΩInput.ω P.here
  (Fold.B₀ (J.ℓ ΩInput.ω)) (W.seed ΩInput.ω) (Start.initial ΩInput.ω)
actual-lim : W.World ΩInput.ω (ΩInput.nat 1) (P.below (P.branch 1))
  (Fold.dL (λ k → J.ℓ (ΩInput.nat k)) (T.εh ΩInput.ω) (T.ρh ΩInput.ω)
    (Fold.B₀ (J.ℓ ΩInput.ω)) 1 S.zero)
  (O.cap P.here (W.seed ΩInput.ω) (L.Ω (T.lvl ΩInput.ω)))
actual-lim = lim-child P.here (Fold.B₀ (J.ℓ ΩInput.ω)) (W.seed ΩInput.ω) 1 LimModel.zero-out
```
