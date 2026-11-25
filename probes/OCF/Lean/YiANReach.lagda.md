# 验收: 终点层号一般的下降

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提.
> `Reach.reachG`: 给定终点层号 n₀, 记号项 t 与 n₀ 处对一切满足 `OKB`, `Hi` 的底成立的锚点, 沿后继、ℕ 极限的孩子、Ω 结点第 0 行下降到 n₀. `YiEVReach.reach` 与 `YiPHEnd.reach³` 是它的两个实例 (`reach₂`, `reach₃`).
> 不涉及上界; 一切有限层号的锚点见 [YiANLv](YiANLv.lagda.md), 用法见 [YiANEnd](YiANEnd.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiANReach where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (Ev; Rt)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiLSFold using (OKB; ok-dS; ok-dL)
open import OCF.Lean.YiT2Frame using (ok-dW)
open import OCF.Lean.YiEVReach
open import OCF.Lean.YiMEAnchor using (two)
open import OCF.Lean.YiPHBase using (three)
open import OCF.Lean.YiPHEnd using (t₃; Lo³; module AtThree)
open import OCF.Lean.YiNFOCase using (tA)
import OCF.Lean.YiRefTw2 as R2
import OCF.Align.EboLeanDef as E
open E using (HC)
open import OCF.Align.Value using (_≼_; ≼-trans)
```

## 一般的下降

`LoG ℓ ε ρ B`: t 的参照不超过层号 ℓ 的 Ω 树以 B 为底的折叠. 锚点对 n₀ 上任意的证据与路线陈述 (有限层号上它们的类型是单位类型).

```agda
module Reach (n₀ : LF) (t : E.T) where

  LoG : (ℓ : LF) → Ev ℓ → Rt ℓ → Base ℓ → Set
  LoG ℓ ε ρ B = (h : HC t) → R2.Rt h ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))

  Anchor : Set
  Anchor = (ε : Ev n₀) (ρ : Rt n₀) (B : Base n₀) → OKB n₀ B → Hi n₀ B → LoG n₀ ε ρ B

  reachG : Anchor → ∀ {ℓ} → n₀ ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → LoG ℓ ε ρ B
  reachG an ⇐r ε ρ B ok hi = an ε ρ B ok hi
  reachG an (⇐s {a} p) ε ρ B ok hi h =
    ≼-trans (reachG an p ε ρ (dS a ε ρ B zero) (ok-dS ε ρ B ok zero) (hi-dS a ε ρ B hi zero) h) (suc≽ a ε ρ B ok)
  reachG an (⇐l {g} n p) ε ρ B ok hi h =
    ≼-trans (reachG an p (ε n) (proj₁ ρ n) (dL g ε ρ B n (preΩ g n)) (ok-dL g ε ρ B ok n (preΩ g n)) (hi-dL g ε ρ B hi n (preΩ g n)) h)
      (lim≽ g ε ρ B n)
  reachG an (⇐w {k} {h = f} p) ε ρ B ok hi h =
    ≼-trans (reachG an p (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (dW k f ε ρ B zero zero) (ok-dW k f ε ρ B ok zero zero) (hi-dW k f ε ρ B hi zero zero) h)
      (Ω≽0 k f ε ρ B)
```

## 两个已有的下降是实例

```agda
reach₂ : ∀ {ℓ} → two ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo ℓ ε ρ B
reach₂ = Reach.reachG two tA (λ _ _ B ok hi → AtTwo.atTwo B ok hi)

reach₃ : ∀ {ℓ} → three ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo³ ℓ ε ρ B
reach₃ = Reach.reachG three t₃ (λ _ _ B ok hi → AtThree.atThree B ok hi)
```
