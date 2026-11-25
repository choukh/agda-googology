# YiRawFold 第 4 层：`T₃ᵐ` 的值下界

**验收文件，档位：编译定理 (下界，不是同值)。** `T₃ᵐ` 不低于参照的 ψ₀(Ω₁), ψ₀(Ω₂), ψ₀(Ω₃)。第 0 项是 `closedᵐ (fin 1)`；第 1 项的层号是 `read0 (1 + closedᵐ (fin 1))`，
它的第 0 支的第 0, 1 支字面是 `fin 2`, `fin 3`，经极限层号上 `top` 的部分和一行 (`Φᵐ-lim-row`) 落到 `closedᵐ (fin 2)`, `closedᵐ (fin 3)` 上。
不否定更高的下界。下界来自 [YiRawValBase](YiRawValBase.lagda.md), [YiRawVal2](YiRawVal2.lagda.md), [YiRawVal3](YiRawVal3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawValTw3 where

open import Data.Unit.Base using (tt)
open import OCF.Align.YiLvFoldFin using (fin)
open import OCF.Align.YiRawFoldInst using (closedᵐ)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩; plus≽)
open import OCF.Align.YiRawValBase using (lower₁ᵐ)
open import OCF.Align.YiRawVal2 using (lower₂ᵐ)
open import OCF.Align.YiRawVal3 using (lower₃ᵐ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l)
```

## 1 三条下界

第 1 项展开：`Φᵐ (lim F) … base top = lim (psum (λ i → Φᵐ (F i) … base top))`，取 `i = 0`；`F 0 = lim H`，再展开一次，
`psum` 的第 0 项是 `H 0` 那一支，第 1 项是 `H 0` 那一支加上 `H 1` 那一支。`H 0`, `H 1` 字面是 `fin 2`, `fin 3`；那两支的 (`Plain`, `Legal`) 是 `⊤` 的元素，
外部派发是全折叠，所以它们与 `closedᵐ (fin 2) tt tt`, `closedᵐ (fin 3) tt tt` 定义性相等。

```agda
T₃ᵐ-Ω₁ : L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read T₃ᵐ
T₃ᵐ-Ω₁ = ≼l 0 lower₁ᵐ

T₃ᵐ-Ω₂ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read T₃ᵐ
T₃ᵐ-Ω₂ = ≼l 1 (≼l 0 (≼l 0 lower₂ᵐ))

T₃ᵐ-Ω₃ : L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read T₃ᵐ
T₃ᵐ-Ω₃ = ≼l 1 (≼l 0 (≼l 1
  (plus≽ (closedᵐ (fin 2) tt tt) (closedᵐ (fin 3) tt tt) lower₃ᵐ)))
```
