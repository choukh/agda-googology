# YiXVFiniteCompose
> 验收文件。档位：编译定理。有限层参照侧的加法复合与前缀下界工具。尚无所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteCompose where
open import Data.Nat using (zero; suc)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteGroundCompose as G
import OCF.Lean.YiXVFiniteComposeStage as S

compose : ∀ t k m (X : I.T t) (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ t)) (Y : I.T k)
  (τ : L.Simᴵ (L.natᴵ m) (L.natᴵ k)) (Z : I.T m) → A.Gd t X → A.Gd k Y → A.Gd m Z →
  A.Le t (L.add (L.add X σ Y) (λ q → σ (τ q)) Z) (L.add X σ (L.add Y τ Z))
compose t k zero X σ Y τ Z gx gy gZ = G.compose t k X σ Y τ Z gx gy
compose zero k (suc m) X σ Y τ Z gx gy gZ with σ (τ L.zero)
... | ()
compose (suc n) k (suc m) X σ Y τ Z gx gy gZ = At.result gZ
  where
  module Stage = S.Stage n m (λ k → compose (suc n) k m)
  module At = Stage.At k X σ Y τ gx gy

assoc : ∀ t k (X Y : I.T t) (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ t)) (Z : I.T k) →
  A.Gd t X → A.Gd t Y → A.Gd k Z → A.Le t (L.add (X L.+ Y) σ Z) (X L.+ L.add Y σ Z)
assoc t k X Y σ Z gx gy gZ = compose t t k X (λ q → q) Y σ Z gx gy gZ
```
