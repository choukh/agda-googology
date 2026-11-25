# ψ₀(Ω_Ω+Ω₂) 未走通: 参照与树在第 1 层链上的形状, 与一条条件定理

验收文件. 编译事实: `X₂≅ : S2.X₂ ≅ X₂′` (换一个 Sim `σB`, 它在第 1 层上定义性地是 `σA`, 各项可直接交给 [YiShpEps](YiShpEps.lagda.md) 的 `fold1`); `X₂′≼ᶜ : Sync₂ → X₂′ ≼ NA.read W.T⁺ʷ` (条件定理), `Sync₂-0` 是前提的第 0 项; 第 1 项起未走通.
形状 (都是 `refl`): 参照的 ψ₁(Ω_{ℓ₀}) 字面是 ℕ 极限 (`ψ₁ᴸ-lim`, 静态前缀的对角线); 树在同一处是根位置保留的 Ω₁ 结点 (`ψ₁-top`, 派发 `dl-p₀`), 层号 1 的链点也是 (`γ₂-1`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiShpTwo where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open NA using (Ω⊴top; R₁)
open import OCF.Lean.YiDlVOne using (V2; Ψ₀; p₀)
open import OCF.Lean.YiShpOne using (σA)
open import OCF.Lean.YiShpSq using (s₂; G₂; ψ₁; Y; N₂≼T)
open import OCF.Lean.YiShpEps using (fold1; K₁)
open import OCF.Align.YiLvVal2 using (ℓ₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼)
import OCF.Align.Stage2 as S2
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 参照

`σB` 的第 1 层部分就是 `σA`; 换 Sim 不改变 ≅ 类.

```agda
σB : L.Simᴵ (L.suc (L.suc L.zero)) S2.ℓ₀
σB L.zero = L.lim 1 (L.lim 0 (L.lim 3 (L.suc L.zero)))
σB (L.suc q) = L.lim 0 q

X₂′ : L.Ordᶜ L.zero
X₂′ = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σB (L.Ω (L.suc (L.suc L.zero))))

X₂≅ : S2.X₂ L.≅ X₂′
X₂≅ = L.ψ⁰-≅ (L.add-≅ {σ = S2.σ₂} {σ′ = σB} (L.Ω-refl S2.ℓ₀) (L.Ω-refl (L.suc (L.suc L.zero))))

e₂ : ℕ → L.Ordᶜ ℓ₁
e₂ = iterᴸ (λ x → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA x)) (L.Ω ℓ₁)

X₂′-form : X₂′ ≡ L.lim (λ n → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (e₂ n)))
X₂′-form = refl

ψ₁ᴸ-lim : Σ (ℕ → L.Ordᶜ ℓ₁) (λ F → L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀) ≡ L.lim F)
ψ₁ᴸ-lim = _ , refl
```

## 2 树: 层号 1 的链与根位置的保留

```agda
γ₂ : ℕ → R₁
γ₂ = chain (suc zero) (λ η → ψ₁ (G₂ η))

N₂-chain : Ψ₀ (G.lc s₂ G₂) ≡ G.lim (λ n → Ψ₀ (G₂ (γ₂ n)))
N₂-chain = refl

dl-p₀ : W.cmpw V2 s₂ p₀ ≡ keep (inj₁ tt) refl
dl-p₀ = refl

ψ₁-top : ψ₁ G.top ≡ G.lc (inj₁ tt) K₁
ψ₁-top = refl

γ₂-1 : γ₂ 1 ≡ G.lc (inj₁ tt) (λ ζ → plus (suc zero) G.top (Y ζ))
γ₂-1 = refl
```

## 3 条件定理

前提 `Sync₂`: 参照第 n 项不高于树在层号 1 的链的第 n 点上的值. 第 0 项由 `fold1` 给出.

```agda
Sync₂ : Set
Sync₂ = ∀ n → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (e₂ n)) ≼ NA.read (Ψ₀ (G₂ (γ₂ n)))

Sync₂-0 : L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (e₂ 0)) ≼ NA.read (Ψ₀ (G₂ (γ₂ 0)))
Sync₂-0 = fold1 Ω⊴top (L.Ω-refl ℓ₁)

X₂′≼ᶜ : Sync₂ → X₂′ ≼ NA.read W.T⁺ʷ
X₂′≼ᶜ h = N₂≼T (l≼ (λ n → ≼l n (h n)))
```
