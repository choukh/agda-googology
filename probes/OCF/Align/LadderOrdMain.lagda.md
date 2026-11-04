# 序数高度: 闭包定理

> 由 `Survey/scripts/ladderord/mk_ord.py` 从 [LadderInfMain](LadderInfMain.lagda.md) 生成, 对结构 `HtB` 参数化. **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 除了名字逐字相同. 下面的说明是原文件的.
>
> **判决: HOLDS (对结构参数, 编译过).** 结论写在 [LadderOrd](LadderOrd.lagda.md). `GᴺTᵠ m α`: 对高度结构 `𝕊` 的一切高度 $m$, 一切 $\alpha$. 从 [LadderNFMain](LadderNFMain.lagda.md) 改写, 去掉按 $m$ 的实例.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.LadderOrdMain (𝕊 : HtB) where

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (Goodᴺ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree 𝕊
open import OCF.Align.LadderOrdCx 𝕊
open import OCF.Align.LadderOrdClass 𝕊
open import OCF.Align.LadderOrdGood 𝕊
open import OCF.Align.LadderOrdEval 𝕊 using (module EvalM)
open import OCF.Align.LadderOrdOmega 𝕊
open EvalM Ω̇G public using (T̄)

Gᴺof : ∀ {m c φ χ ℓ w} {ok : Ok w} {e : Eh h₀ m w χ} {x : Q m c φ χ} → Gq g₀ m c 𝓥 x → (ev : Ev ℓ φ) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (ψ̄ᵠ ok e x ev z))
Gᴺof {ok = ok} {e = e} g ev z = Good→N refl (T̄ {ok = ok} {e = e} {ev = ev} {p = z} {𝓖 = 𝓥} {𝓖′ = isId} (λ { refl → tt }) (λ c → c) refl g)

GᴺTᵠ : ∀ m α {ℓ} (ev : Ev ℓ Fl) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Tᵠ m α ev z))
GᴺTᵠ m α = Gᴺof (Ω̇G g₀ m α)
```
