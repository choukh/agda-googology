> **机械克隆, 验收用.** 由 `LadderInfWMain` 经 `Survey/scripts/ladderlab/mkworld.py` 复制, 只改模块名; 见 [LadderLab](LadderLab.lagda.md). 下面的文字是原文.

> **机械克隆, 验收用.** 由 `LadderInfMain` 经 `Survey/scripts/laddernf/mk_infw.py` 复制, 只改导入, 落在标签阶梯的世界. 见 [LadderInfAccept](LadderInfAccept.lagda.md).

# 高度抽象: 闭包定理

> **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderInf](LadderInf.lagda.md). `GᴺTᵠ m α`: 对高度结构 `𝕊` 的一切高度 $m$, 一切 $\alpha$. 从 [LadderNFMain](LadderNFMain.lagda.md) 改写, 去掉按 $m$ 的实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderInfBase
module OCF.Align.LadderLabZInfWMain (𝕊 : HtS) where

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level
open import OCF.Align.LadderLabZNFWPrefix using (toZ)
open import OCF.Align.LadderLabZNFWFloor using (Ev)
open import OCF.Align.LadderLabZNFWForce using (Goodᴺ)
open import OCF.Align.LadderLabZNFWFT using (Fl)
open import OCF.Align.LadderLabZInfWTree 𝕊
open import OCF.Align.LadderLabZInfWCx 𝕊
open import OCF.Align.LadderLabZInfWClass 𝕊
open import OCF.Align.LadderLabZInfWGood 𝕊
open import OCF.Align.LadderLabZInfWEval 𝕊 using (module EvalM)
open import OCF.Align.LadderLabZInfWOmega 𝕊
open EvalM Ω̇G public using (T̄)

Gᴺof : ∀ {m c φ χ ℓ w} {ok : Ok w} {e : Eh h₀ m w χ} {x : Q m c φ χ} → Gq g₀ m c 𝓥 x → (ev : Ev ℓ φ) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ᵠ ok e x ev z))
Gᴺof {ok = ok} {e = e} g ev z = Good→N refl (T̄ {ok = ok} {e = e} {ev = ev} {p = z} {𝓖 = 𝓥} {𝓖′ = isId} (λ { refl → tt }) (λ c → c) refl g)

GᴺTᵠ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tᵠ m α ev z))
GᴺTᵠ m α = Gᴺof (Ω̇G g₀ m α)
```
