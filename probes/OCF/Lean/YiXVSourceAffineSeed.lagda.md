# YiXVSourceAffineSeed
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceAffineSeed where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Lean.YiLegOps as O
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteFoldOmega as Omega
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourceAffineGround as C

module Model (n : ℕ) where
  module Frame = C.Frame n (suc (suc n)) L.zero (λ q → q)
  Ω = L.Ω (L.natᴵ (suc n))
  Z = L.Ω (L.natᴵ (suc (suc n)))
  seed : U.U (suc n) (O.Ωt (J.nat (suc n))) (Frame.φ (L.add Z (λ q → L.suc q) Ω))
  seed = UB.weakU (suc n) (UB.weakU (suc n) (UB.ΩU (suc n)) (Omega.two (suc n) (suc (suc n)) L.zero (λ q → q)))
    (Frame.mono (Right.right (suc (suc n)) (suc n)
      (B.rfl (suc (suc n)) F.zero {X = Z} (proj₁ (B.Ω-model (suc (suc n)) F.zero)))
      (λ q → L.suc q) Ω (proj₁ (B.Ω-model (suc n) F.zero))))
```
