# 世界内的构造有没有封顶 (四): 正对照

> 入口 [TLEnd](TLEnd.lagda.md). **判决: 正对照的这一步未走通. 编译过的是: 带外部输入时判据必定分不开.** 不读记号. `T₁`, `T₀` 来自 [WorldTHInst](WorldTHInst.lagda.md), 带 `HS`, 带绑定的读法在那边 (判断).
>
> | 定理 | 陈述 |
> | --- | --- |
> | `T₁-below-F` | `suc (lv T₁) ≼` `cs ⌈lv T₁⌉` 顶上第 0 行的层号: 把 `T₁` 喂给世界的行, 值就过了 `T₁` |
> | `T₁-below-Cap` | `suc (lv T₁) ≼` 以 `lv T₁` 为起点的 `Cap` |
> | `T₀<T₁ᵛ` | `T₀ ≺ T₁`: 同一族里, 第 0 行的闭包点被带绑定的树严格越过 |
> | `Target` | **陈述, 未证明:** 起点取 `T₀` 的层号时 `lvCap ≼ lv T₁` |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLEndTop where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Class using (lvG)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (_≼_; ⌈_⌉)
open import OCF.Align.LadderOrdCert using (Gᵖ)
open import OCF.Align.WorldTHInst using (T₀; T₁; HS-T₀; HS-T₁; T₀≺T₁)
open import OCF.Align.TLEndWord
open import OCF.Align.CrossMClosed using (lv⊤)

lvT₀ lvT₁ : Ordᴵ
lvT₀ = toLevel T₀ HS-T₀
lvT₁ = toLevel T₁ HS-T₁

T₁-below-F : suc lvT₁ ≼ lvG (Gᵖ (cs ⌈ lvT₁ ⌉) end zero)
T₁-below-F = above-F lvT₁

module Self = Top lvT₁

T₁-below-Cap : suc lvT₁ ≼ Self.lvCap
T₁-below-Cap = Self.word< []′
  where
  open import Data.List using ([]; List)
  open import Data.Bool using (Bool)
  []′ : List Bool
  []′ = []

T₀<T₁ᵛ : T₀ ≺ T₁
T₀<T₁ᵛ = T₀≺T₁

module From₀ = Top lvT₀

-- 闭项: 从 lv⊤ 起的类的上界
Capᵀ : Ordᶜ zero
Capᵀ = Top.Cap lv⊤

fghCap : ℕ → ℕ
fghCap = FGH Capᵀ

-- 判据要有分辨力就要这一条. 没有证明, 也没有否定
Target : Set
Target = From₀.lvCap ≼ lvT₁
```
