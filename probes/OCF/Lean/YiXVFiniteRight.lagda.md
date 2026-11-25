# YiXVFiniteRight
> 验收文件。档位：编译定理。有限层参照侧的加法复合与前缀下界工具。尚无所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteRight where
open import Data.Nat using (zero; suc)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteAddStage as S
import OCF.Lean.YiXVFiniteGroundAdd as G

right : ∀ t k {X X′} → A.Le t X X′ → (σ : L.Simᴵ (L.natᴵ k) (L.natᴵ t)) (Y : I.T k) → A.Gd k Y →
  A.Le t X (L.add X′ σ Y)
right t zero {X} {X′} p σ Y gy = G.right t {X = X} {X′ = X′} p σ Y
right zero (suc k) p σ Y gy with σ L.zero
... | ()
right (suc n) (suc m) p σ Y gy = Stage.right p σ gy
  where module Stage = S.Stage n m (Add.good (suc n) m) (Add.mono (suc n) m)
```
