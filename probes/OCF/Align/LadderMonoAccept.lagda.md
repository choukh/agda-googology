# 跨高度单调: 验收

> **验收文件, 不在证书的闭包内.** 记号与标签只在这里出现 (与它导入的标签阶梯). 结论写在 [LadderMono](LadderMono.lagda.md).
>
> 与 [LadderNFAccept](LadderNFAccept.lagda.md) 同样的做法: 证书 `LadderMono{Rel,Down,Main}` 只改导入, 克隆成 `LadderMonoW{Rel,Down,Main}`, 落在标签阶梯的树上. 克隆规则同 `Survey/scripts/laddernf/mk_w.py`, 代码行逐字.
>
> 1. **`Tω-cert-label`: 新证书的计值带已有的标签 $\psi_0(\Omega_{\Omega\cdot\omega})$.** `Lab (forceᴺ _ (GᴺTω ev p)) tω`, 证书 `GᴺTω` 是克隆世界的, 单调 `Tω-mono` 不读标签, 这里只是接上 `Tω-lab`.
> 2. **有限测试 (§2):** `fgh-ω`: 两个世界的 FGH 在第 0 项相等, `refl`. 不是证明.
>
> **没有做到的.** 没有跨世界的桥: 主线的 `GᴺTω` 与克隆的 `GᴺTω` 不是同一个项, 标签贴的是后者. 这与 `LadderNFAccept` 的边界相同.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderMonoAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.ScafLadderZUniform3Base using (Ev)
open import OCF.Align.ScafLadderZUniform4Base using (Fl)
open import OCF.Align.ScafLadderQTop using (tω)
open import OCF.Align.LadderNFAccept using (Tω-via-labels; Tω-lab; selfω)
open import OCF.Align.LadderNFWForce
open import OCF.Align.LadderNFWEq using (lᶻ)
open import OCF.Align.LadderMonoWMain using (GᴺTω; Tω-mono)
```

## §1 标签

```agda
Tω-cert-label : ∀ {ℓ} (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) → Lab (forceᴺ _ (GᴺTω ev p)) tω
Tω-cert-label ev p = Lab-≅ (forceᴺ-≅ (lᶻ (λ n → selfω n ev p)) (GᴺTω ev p) (Tω-via-labels ev p)) (Tω-lab ev p)
```

## §2 跨世界的有限测试

**有限测试, 不是证明.**

```agda
import OCF.Align.LadderMonoClosed as C

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

fgh-ω : C.fgh 0 ≡ FGH (forceᴺ _ (GᴺTω ev₀ zero)) 0
fgh-ω = refl

fgh-ω-val : C.fgh 0 ≡ 1
fgh-ω-val = refl
```
