# `T⁺` 的值的计算问到保守派发丢掉的那一对

验收文件. 编译定理 `asked : NA.read (Ψ₀ N₂) ≼ NA.read NT.T⁺`: 位置 `s₂` (层号 1) 上的结点 `N₂` 在 `T⁺` 根链第 1 点的分支里 (经第一位置), 它的折叠值不高于 `T⁺`.
`asked-form`, `asked-lost` (`refl`): `N₂` 折到第 0 层时用层号 1 的链, 链的推进用派发 `cmp V₂ s₂`; 链第 1 点要算的 `top` 像里, 位置 `s₂′` 上的结点因 `lost` 被折叠成 ℕ-极限 (`could`: 层号 1 里本可保留).
不陈述丢掉的值有多少; 只把 [YiNext 回报](../../Survey/Reports-2026-11-11/YiNext.md) §3 的判断 "这一对会被 `T⁺` 第 1 项的链问到" 换成编译过的陈述.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAboveLost where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiNextAccTest using (s₂; s₂′; Ω₂; lost; could)
open import OCF.Lean.YiAboveCtx using (Ψ₀; topᶜ; up≼; Tt; gK; d)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l)

Bs₂ : Raw (suc zero) → Raw (tw 2)
Bs₂ ζ = plus (tw 2) G.top (plus (tw 2) (Kf (tw 2) Tt G.top)
  (Ψ (tw 2) (vs v0) (λ r → keep (G.suc G.top , tt , inj₂ r) refl) ζ))

N₂ : Raw (tw 2)
N₂ = G.lc s₂ Bs₂

-- 坐标 suc top 的分支: K top 之后加上 Ω₂ (= Tt (suc top)), 前面加 top
N₂≡ : plus (tw 2) G.top (plus (tw 2) (Kf (tw 2) Tt G.top) Ω₂) ≡ N₂
N₂≡ = refl

c-N : Cp (tw 2) N₂ (gK (G.suc G.top))
c-N = inj₂ (1 , inj₁ refl)

c-d : Cp zero (G.suc G.top) (d 1)
c-d = add-cp zero G.lc dnLc G.top (topᶜ zero NT.V₂ (cmp NT.V₂ p₀) (gK G.top))

c-gK : Cp (tw 2) (gK (G.suc G.top)) (gK (d 1))
c-gK = add-cp (tw 2) G.lc dnLc G.top (Kf-cp (tw 2) Tt c-d)

asked : NA.read (Ψ₀ N₂) ≼ NA.read NT.T⁺
asked = ≼-trans (up≼ c-N) (≼-trans (up≼ c-gK) (≼l 1 (≼l 1 (≼-refl _))))

asked-form : Ψ₀ N₂ ≡ G.lim (λ n → Ψ₀ (Bs₂ (chain (suc zero) (λ ζ → Ψ (suc zero) NT.V₂ (cmp NT.V₂ s₂) (Bs₂ ζ)) n)))
asked-form = refl

B′ : R → Raw (tw 2)
B′ η = plus (tw 2) G.top (plus (tw 2) (Kf (tw 2) Tt G.top)
  (Ψ (tw 2) v0 (λ r → keep (G.suc G.top , tt , inj₂ (inj₂ r)) refl) η))

asked-lost : Ψ (suc zero) NT.V₂ (cmp NT.V₂ s₂) (Bs₂ G.top) ≡
  G.lim (λ n → Ψ (suc zero) NT.V₂ (cmp NT.V₂ s₂) (B′ (chain zero (λ η → Ψ zero NT.V₂ (cmp NT.V₂ s₂′) (B′ η)) n)))
asked-lost = refl
```
