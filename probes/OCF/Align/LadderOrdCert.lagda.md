# 序数高度: 对一切码, 一切 `Ordᴵ` 的证书

> **判决: HOLDS (编译过, 无条件; 读法是判断).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 全部是 `GᴺTᵠ` 的特例, 没有新的证明. 高度结构 `HB M` 对每个码 $M$ 闭合.
>
> - `Gᵒ M α`: `Goodᴺ (toZ (Tᵒ M α ev₀ zero))`, 对一切 $M$, 一切 $\alpha$. 读作 $\psi_0(\Omega_{\Omega\cdot(1+\lVert M\rVert)+\alpha})$.
> - `Gᵖ M p α`: $M$ 之下的任何位置.
> - `Gˢ h α`: 对一切带证书 `Str η` 的 $\eta$, 高度的值与 $\eta$ 互相 `≼` (`code-val`).
> - `Gη η α`: 对一切 `η : Ordᴵ`, 无证书; 高度不低于 $\eta$ (`dom₀`), 可能更高.
> - `growᵖ M r`: $M$ 之内, $n<m$ 时第 0 行的计值严格增长 (不空的证据).
> - 检查点 `Gω·2`, `Gω²`, `Gω^ω`, `Gε₀`. `view-step` 在 $\omega^2$ 上是假的, 这里不需要它.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdCert where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev; Run)
open import OCF.Free.Force using (Goodᴺ; forceᴺ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode
open import OCF.Align.LadderOrdStr
import OCF.Align.LadderOrdTree
import OCF.Align.LadderOrdMain
import OCF.Align.LadderOrdGrow

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

Tᵖ : ∀ M → Pos (cs M) → Ordᴵ → Run Fl
Tᵖ M = OCF.Align.LadderOrdTree.Tᵠ (HB M)

Tᵒ : Code → Ordᴵ → Run Fl
Tᵒ M = Tᵖ M end

Gᵖ : ∀ M (p : Pos (cs M)) α → Goodᴺ (toZ (Tᵖ M p α ev₀ zero))
Gᵖ M p α = OCF.Align.LadderOrdMain.GᴺTᵠ (HB M) p α ev₀ zero

Gᵒ : ∀ M α → Goodᴺ (toZ (Tᵒ M α ev₀ zero))
Gᵒ M = Gᵖ M end

-- 带证书的 Ordᴵ: 高度的值就是 η
Gˢ : ∀ {η} (h : Str η) α → Goodᴺ (toZ (Tᵒ (code h) α ev₀ zero))
Gˢ h = Gᵒ (code h)

-- 不带证书的 Ordᴵ: 高度不低于 η
Gη : ∀ η α → Goodᴺ (toZ (Tᵒ ⌈ η ⌉ α ev₀ zero))
Gη η = Gᵒ ⌈ η ⌉

-- 检查点
Gω·2 : ∀ α → Goodᴺ (toZ (Tᵒ (ω·ᶜ 1) α ev₀ zero))
Gω·2 = Gᵒ (ω·ᶜ 1)

Gω² : ∀ α → Goodᴺ (toZ (Tᵒ ω²ᶜ α ev₀ zero))
Gω² = Gᵒ ω²ᶜ

Gω^ω : ∀ α → Goodᴺ (toZ (Tᵒ ω^ωᶜ α ev₀ zero))
Gω^ω = Gᵒ ω^ωᶜ

Gε₀ : ∀ α → Goodᴺ (toZ (Tᵒ ε₀ᶜ α ev₀ zero))
Gε₀ = Gᵒ ε₀ᶜ

-- 不空: M 之内, 高度严格增长
growᵖ : ∀ M {n m : Pos (cs M)} → n <ᴾ m → forceᴺ _ (Gᵖ M n zero) ≺ forceᴺ _ (Gᵖ M m zero)
growᵖ M r = OCF.Align.LadderOrdGrow.grow (HB M) r ev₀ zero
```
