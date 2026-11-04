# 序数高度的世界: 累加是 `Nx` 的一个实例

> 不含记号. 结论写在 [CumHt](CumHt.lagda.md). **这是这一路唯一导入累加 (`CumReadBase`) 的定义文件.** `next` 取自 [CumReadBase](CumReadBase.lagda.md), 保等价的部分抄自 [CumUpPsi](CumUpPsi.lagda.md) §1. 要换掉累加, 换这个文件就够.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumHtCum where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadBase using (next; next-⊲; Lg-next; _⊞_; cumA; cs)
open import OCF.Align.CumHtBase

⊞≈ : ∀ {a a′ b b′} → a ≈ᴬ a′ → b ≈ᴬ b′ → a ⊞ b ≈ᴬ a′ ⊞ b′
⊞≈ e z≈ = e
⊞≈ e (s≈ d) = s≈ (⊞≈ e d)
⊞≈ e (l≈ h) = l≈ (λ n → ⊞≈ e (h n))

cs≈ : ∀ {g g′} → (∀ n → g n ≈ᴬ g′ n) → ∀ n → cs g n ≈ᴬ cs g′ n
cs≈ h zero = h 0
cs≈ h (suc n) = ⊞≈ (cs≈ h n) (s≈ (h (suc n)))

cum≈ : ∀ {y y′ : Ord₀} → y ≅ y′ → cumA y ≈ᴬ cumA y′
cum≈ z≅ = z≈
cum≈ (s≅ e) = s≈ (cum≈ e)
cum≈ (l≅ h) = l≈ (cs≈ (λ n → cum≈ (h n)))
cum≈ (lᵢ≅ {p = ()} e h)
cum≈ (upˡ {r = ()} e)
cum≈ (upʳ {r = ()} e)

next≈ : ∀ {η η′} {y y′ : Ord₀} → η ≈ᴬ η′ → y ≅ y′ → next η y ≈ᴬ next η′ y′
next≈ e d = ⊞≈ e (s≈ (cum≈ d))

𝓝ᶜ : Nx
𝓝ᶜ = record { nxt = next ; nxt-⊲ = next-⊲ ; nxt-L = Lg-next ; nxt-≈ = next≈ }
```
