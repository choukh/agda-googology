# YiXVCountableFold
> 验收文件。档位：编译定理。Strong 源层与各自 Strong 公共上界下，原折叠保持辅助合法性与混合比较。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVLiteralSim as M
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiLegBlock as S
open import OCF.Lean.YiXVLvlSteps using (Strong; read-strong)
import OCF.Lean.YiXVCountableFoldInput as Q
import OCF.Lean.YiXVCountableGroundFold as G
import OCF.Lean.YiXVCountableFoldStage as Stage

ops : ∀ κ → Strong κ → Q.Ops κ
ops L.zero s = G.ops
ops (L.suc κ) s = Stage.Stage.result (L.suc κ) s (λ { L.zero → ops κ s })
ops (L.lim f step) s = Stage.Stage.result (L.lim f step) s (λ { (L.self n) → ops (f n) (proj₁ s n) })
read-ops : ∀ (X : S.Tr S.zero) → Q.Ops (T.lvl X)
read-ops X = ops (T.lvl X) (read-strong X)
nat-strong : ∀ n → Strong (L.natᴵ n)
nat-strong zero = tt
nat-strong (suc n) = nat-strong n
ω-strong : Strong L.ωᴵ
ω-strong = nat-strong , (λ n → M.canonical L.suc)
actual-own : ∀ κ (s : Strong κ) → A.Gd (L.ψ (L.zero {a = κ}) (λ q → L.suc q) (L.Ω κ))
actual-own κ s = Q.Ops.good (ops κ s) {ν = κ} {a = L.suc κ} s L.zero (λ q → L.suc q) (proj₁ (O.model κ))
actual-zero : A.Gd (L.ψ (L.suc (L.lim 1 L.zero)) (λ q → L.suc q) (L.Ω L.ωᴵ))
actual-zero = Q.Ops.good (ops L.ωᴵ ω-strong) {ν = L.zero} {a = L.suc L.ωᴵ} ω-strong (L.suc (L.lim 1 L.zero)) (λ q → L.suc q) A.omegaΩ
```
