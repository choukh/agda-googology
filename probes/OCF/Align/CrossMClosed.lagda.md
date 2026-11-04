# 跨段 (五): 闭项与 FGH

> 入口 [CrossM](CrossM.lagda.md). **判决: HOLDS (闭项无参数, 无假设); 读法是判断; 测试明说.** `T⊤ = νT 𝒯 ωᶜ`: 塔的节点从 $M_0=\omega$ 起走累加链. `HS⊤` 是遗传步进证书, `lv⊤` 把它读回层号. 读法: $\psi_0(\Omega_{\psi_1(\Omega)})$, 判断, 见 [CrossM](CrossM.lagda.md). 第 0 个分支 `Tᵖ ωᶜ end 0` 就是带标签的 $\psi_0(\Omega_{\psi_1(1)})$ (已有的 `anchor-ω`), 与记号的第 0 项同一棵树.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ωᶜ)
open import OCF.Align.CrossMNode
open import OCF.Align.CrossMInst

T⊤ : Ordᶜ zero
T⊤ = νT 𝒯 ωᶜ

HS⊤ : HS T⊤
HS⊤ = νHS 𝒯 ωᶜ

lv⊤ : Ordᴵ
lv⊤ = νlv 𝒯 ωᶜ

fgh⊤ : ℕ → ℕ
fgh⊤ = FGH T⊤

-- 换起点: 对一切码都有
T⊤ᶜ : Code → Ordᶜ zero
T⊤ᶜ = νT 𝒯
```
