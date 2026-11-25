# 不同步引理 (构造一路): 有关系的不同步对上的结论, 闭的实例

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `low₁`: 否定一路的不同步对 `pair₁` (Ω₁ 对着 "第 3 层 Ω 树左加搬上来的 Ω₁ 树" `x₁`) 上, 折到第 2 层的输出对着 ψ₂(t₀ + Ω₁); 经接口上的 `lowKeepAsyncᶠ` 取得. `low₁ᶜ`: 标准底的闭的一例.
> `gbᶜ`: 标准底满足 `GBᶠ` (前缀为空), 所以 `LFᶠ`, `lowKeepᶠ`, `async₀⁺` 的前提可满足; `async₀⁺ᶜ`: 参照 ψ₂(Ω₂) 的闭的一例.
> `Async₀`, `Async₀ᶜ`, `Pair₀` 的否定在 [YiASNeg](YiASNeg.lagda.md), 这里不重证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiASProofMin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt)
open import OCF.Lean.YiLegFold
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiMEBase hiding (Rt)
open import OCF.Lean.YiANFam
open import OCF.Lean.YiASIface
open import OCF.Lean.YiASProofLow using (lowKeepAsyncᶠ)
open import OCF.Lean.YiASProofPair using (async₀⁺)
open import OCF.Lean.YiASNeg using (x₁; M₁; pair₁)
```

## 标准底

```agda
mΩt : ∀ i → M i (Ωᴺ i) (Ωt (fin i))
mΩt zero    = pos⁰ (Ωt zero) (Ωt-nz zero)
mΩt (suc i) = Mβ i

gbᶜ : ∀ n → GBᶠ n (B₀ (fin (suc n))) []
gbᶜ n = mkGBᶠ (λ si → ⊴r) (λ {i} si → mΩt i)
```

## 有关系的不同步对

`pair₁`: 余尾下标 0 低于目标 2, `x₁` 的头部槽位层是 2. 关系 `M₁` 经两步放宽得到; 结论由 `lowKeepAsyncᶠ` 给出 (其中放宽一步用折叠的单调性, 被放宽掉的嵌入里的 Ω₁ 树在目标层保留成槽位层 0 的结点).

```agda
low₁ : (ε : Ev (fin 3)) (ρ : Rt (fin 3)) (B : Base (fin 3)) (t₀ : E.T) → GBᶠ 2 B t₀
     → (β : Tr (fin 2)) (nβ : fin 2 ⊢ zero ◃ β) → M 2 (ψᴺ 2 t₀) β
     → M 2 (ψᴺ 2 (t₀ ++ Ωᴺ 1)) (ψs (fin 3) ε ρ B (fin 2) (ins self) β nβ x₁)
low₁ ε ρ B t₀ gb β nβ hβ =
  lowKeepAsyncᶠ (ε , ρ , B) (ins self) (β , nβ) t₀ (2 , refl) (ss s0 , refl) (hβ , gb) tt pair₁ M₁

low₁ᶜ : (ε : Ev (fin 3)) (ρ : Rt (fin 3))
      → M 2 (ψᴺ 2 (Ωᴺ 1)) (ψs (fin 3) ε ρ (B₀ (fin 3)) (fin 2) (ins self) (Ωt (fin 2)) (Ωt-nz (fin 2)) x₁)
low₁ᶜ ε ρ = low₁ ε ρ (B₀ (fin 3)) [] (gbᶜ 2) (Ωt (fin 2)) (Ωt-nz (fin 2)) (Mβ 1)

async₀⁺ᶜ : (ε : Ev (fin 3)) (ρ : Rt (fin 3))
         → M 2 (ψᴺ 2 (Ωᴺ 2)) (ψs (fin 3) ε ρ (B₀ (fin 3)) (fin 2) (ins self) (Ωt (fin 2)) (Ωt-nz (fin 2)) (Ωt (fin 3)))
async₀⁺ᶜ ε ρ = async₀⁺ ε ρ (B₀ (fin 3)) [] (gbᶜ 2) (Ωt (fin 2)) (Ωt-nz (fin 2)) (Mβ 1)
```
