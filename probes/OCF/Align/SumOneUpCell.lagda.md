# `SumOne.T₁` 的上界 (二): 第一个带上下文的回灌

> **验收文件, 定理.** `T₁` 第 1 段里第一个 `nκ` 回灌 (上下文 $\Omega_\Omega+1$) 的格序列 `Cκ`: 第 0 格的世界字面就是站 `Sω` (`v₀≡`), 每格的世界都是 `T₁` 的位置 (`cell≼T₁`), 回灌走完的位置是 `Fb₁` (`Fb₁≤T₁`).
> 只给位置, 不给第 1 格以后的值. 入口 [SumOneUp](SumOneUp.lagda.md). `--safe --without-K --lossy-unification`, 无公设, 无洞.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneUpCell where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level hiding (below)
open import OCF.Align.Value using (_≼_; ≼l; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleVar using (trA; ≤→≼)
open import OCF.Align.TLRuleSpec using (_≤_; ≤l)
open import OCF.Align.SumOneTree using (D; D̂; top; n0; n1; _⨾_; nl; nw; sum; pt; drp)
open import OCF.Align.SumOneClosed using (T₀; T₁; E₁; Y₁; one; St; yc; zeroD; _⊕_; Step; A₁; accTop; Cl; v; κc; κΔ)
open import OCF.Align.SumOneTop using (ũ)
open import OCF.Align.SumOneAccept using (sum-drp)
open import OCF.Align.SumOneUpStation using (c₁; Sω; Pre; here; inL; skip; inl0; pre≤)
```

格序列的参数照 `Run` 在 `E₁ 0` 里展开到这个 `nκ` 时的实参写: 状态 `Yb` 是 `Y₁` 之后做了一次 `Step`, 坐标 `wb` 是此前走过的顶层前缀. `fb-pre` 由检查器核对这些实参.

```agda
wa wb : D̂ one
wa = n0 ⨾ nw C.self n0
wb = wa ⨾ nw (z⊲ one) n1

Ya Yb : St one
Ya = Y₁ ⊕ zeroD
Yb = Ya ⊕ Step Ya

Cκ : ℕ → Cl one azero top
Cκ = κc accTop ũ (z⊲ one) tt tt A₁ wb Yb

dκ : ∀ n → D azero (v (Cκ n))
dκ n = yc (κΔ accTop ũ tt A₁ (Cκ n)) (inj₁ (z⊲ (v (Cκ n)))) tt

Dκ : ℕ → D azero one
Dκ n = drp (dκ n)

fb₁ : D azero one
fb₁ = nl Dκ

Fb₁ : A
Fb₁ = sum Sω fb₁

v₀≡ : v (Cκ 0) ≡ Sω
v₀≡ = refl

fb-pre : Pre (c₁ ⨾ fb₁) (E₁ 0)
fb-pre = skip (inL (inl0 (inL here)))

Fb₁≤T₁ : Fb₁ ≤ T₁
Fb₁≤T₁ = ≤l 1 (pre≤ T₀ fb-pre)

Fb-pt : ∀ n → trA (pt Sω Dκ n) ≅ trA (v (Cκ n))
Fb-pt zero = ≅-refl⁰ (trA Sω)
Fb-pt (suc n) = sum-drp {W′ = one} (dκ n) (Fb-pt n)

Fb≅ : trA Fb₁ ≅ lim (λ n → trA (v (Cκ n)))
Fb≅ = l≅ Fb-pt

cell≼Fb : ∀ n → trA (v (Cκ n)) ≼ trA Fb₁
cell≼Fb n = ≼l n (≅→≼ (≅-sym (Fb-pt n)))

cell≼T₁ : ∀ n → trA (v (Cκ n)) ≼ trA T₁
cell≼T₁ n = ≼-trans (cell≼Fb n) (≤→≼ Fb₁≤T₁)
```
