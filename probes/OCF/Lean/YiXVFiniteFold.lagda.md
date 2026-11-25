# YiXVFiniteFold
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteFoldInterface as Q
import OCF.Lean.YiXVFiniteFoldStage as S

ops : ∀ n → Q.Ops n
ops zero = Q.ops₀
ops (suc n) = S.Stage.result n (ops n)

actual : ∀ n → A.Gd n (L.ψ L.zero (λ q → L.suc q) (L.Ω (L.natᴵ n)))
actual n = Q.Ops.good (ops n) n L.zero (λ q → L.suc q) (L.Ω (L.natᴵ n)) (proj₁ (B.Ω-model n F.zero))
actual₃ : A.Gd 3 (L.ψ L.zero (λ q → L.suc q) (L.Ω (L.natᴵ 3)))
actual₃ = actual 3
```
