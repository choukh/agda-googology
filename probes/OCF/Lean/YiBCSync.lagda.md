# 副本与原定义相等，证据接到第 2 站的两个实例
验收文件（导入 `YiSYReduce`，导入闭包含记号模块）；编译定理：`YiRKChain` 的副本与 `YiSYReduce`、`YiSYDesc` 的原定义逐字相等（`a₁-eq`、`feed-eq`、`chain-eq`，对变量 o、B、β、m）。
`YiSYReduce` 的继承底实例 `oᴱ`、`Bᴱ` 与标准底实例 `oᶻ` 上，换基折叠带 `rbₛ` 是闭项，现行链的每个点的孩子有满证据（`full-chainᴱ`、`full-chainᶻ`）；`YiBCReach.reach` 在两个实例的 Ok 下同形，块仍是 `yₑ`（`reachᴱ`、`reachᶻ`）。
不否定什么，不涉及值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBCSync where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiBSBase using (seen; downOk)
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiTBTab using (ωᶜ)
open import OCF.Lean.YiGIInst using (betaᴱ)
import OCF.Lean.YiRKChain as RK
import OCF.Lean.YiSYReduce as SY
open import OCF.Lean.YiBCCover using (Full; ℓₛ; rbₛ; full-child; module Sync)
open import OCF.Lean.YiBCReach using (ℓω; G; H₁; one; rω; S₁; x₀; w₀; yₑ)
```

```agda
a₁-eq : RK.a₁ ≡ SY.a₁
a₁-eq = refl

module _ (o : Ok ℓₛ) (B : Base ℓₛ) (β : Tr⁺ zero) where
  feed-eq : ∀ z → RK.Real.feed o B z ≡ SY.Sync.feed SY.a₁ o B β z
  feed-eq z = refl

  chain-eq : ∀ m → RK.Real.chain o B m ≡ SY.Sync.chain SY.a₁ o B β m
  chain-eq m = refl

Fdᴮᴱ : Tr⁺ zero
Fdᴮᴱ = Sync.Fdᴮ SY.oᴱ SY.Bᴱ (betaᴱ 2)

Fdᴮᶻ : Tr⁺ zero
Fdᴮᶻ = Sync.Fdᴮ SY.oᶻ (B₀ ℓₛ) (Ωt zero)

full-chainᴱ : ∀ m → Full (SY.a₁ (SY.Sᴱ.chain m)) (proj₂ rbₛ (SY.Sᴱ.chain m))
full-chainᴱ m = full-child (SY.Sᴱ.chain m)

full-chainᶻ : ∀ m → Full (SY.a₁ (SY.Sᶻ.chain m)) (proj₂ rbₛ (SY.Sᶻ.chain m))
full-chainᶻ m = full-child (SY.Sᶻ.chain m)

oᶻω oᴱω : Ok ℓω
oᶻω = proj₂ SY.oᶻ ωᶜ
oᴱω = proj₂ SY.oᴱ ωᶜ

reachᶻ : (B : Base ℓω) (β : Tr⁺ (G 0)) → BS.ψ ℓω oᶻω rω B (G 0) w₀ β x₀
  ≡ seen S₁ (G 0) (downOk (H₁ zero) (proj₂ (proj₂ oᶻω 1) zero) (G 0) (inc tt self)) (lift (tw 1) one) β zero
      ⊞ BS.ψ (H₁ zero) (proj₂ (proj₂ oᶻω 1) zero) (proj₂ (proj₂ rω 1) zero) (B₀ (H₁ zero)) zero (z≤ (H₁ zero)) (Ωt zero) yₑ
reachᶻ B β = refl

reachᴱ : (B : Base ℓω) (β : Tr⁺ (G 0)) → BS.ψ ℓω oᴱω rω B (G 0) w₀ β x₀
  ≡ seen S₁ (G 0) (downOk (H₁ zero) (proj₂ (proj₂ oᴱω 1) zero) (G 0) (inc tt self)) (lift (tw 1) one) β zero
      ⊞ BS.ψ (H₁ zero) (proj₂ (proj₂ oᴱω 1) zero) (proj₂ (proj₂ rω 1) zero) (B₀ (H₁ zero)) zero (z≤ (H₁ zero)) (Ωt zero) yₑ
reachᴱ B β = refl
```
