# YiXVSourceSelfInput
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceSelfInput where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Align.Level as L
open import OCF.Align.YiLvValBase using (Ψ)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteGamma as Gamma
import OCF.Lean.YiXVFiniteFoldOmega as Omega
import OCF.Lean.YiXVFiniteRight as Right
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB

ev : ∀ n → Path.Ev (J.nat n)
ev zero = tt
ev (suc n) = ev n
rt : ∀ n → Path.Rt (J.nat n)
rt zero = tt
rt (suc n) = rt n
seed : ∀ n → U.U n (O.Ωt (J.nat n)) (Ψ n (L.Ω (L.natᴵ n) L.+ L.Ω (L.natᴵ n)))
seed n = UB.weakU n (UB.weakU n (UB.ΩU n) (Omega.two n n L.zero (λ q → L.suc q)))
  (Gamma.At.ψ-mono n (Right.right n n (B.rfl n F.zero {X = L.Ω (L.natᴵ n)} (proj₁ (B.Ω-model n F.zero)))
    (λ q → q) (L.Ω (L.natᴵ n)) (proj₁ (B.Ω-model n F.zero))))
B : ∀ n → Fold.Base (J.nat n)
B n = Fold.B₀ (J.nat n)
```
