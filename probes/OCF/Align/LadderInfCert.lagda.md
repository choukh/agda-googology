# 高度抽象: 实例上的证书

> **判决: HOLDS (编译过, 无条件; 读法见下).** 结论写在 [LadderInf](LadderInf.lagda.md). 三个实例的闭包定理, 全是 `GᴺTᵠ` 的特例, 没有新的证明. 读法 (判断, 只有 `ψ₀(Ω_{Ω·(m+1)+α})` 一行由旧的标签支持).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfCert where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (Goodᴺ)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderInfNat using (HSℕ)
open import OCF.Align.LadderInfTop using (HS∞; fin; ∞)
open import OCF.Align.LadderInfTop2 using (HS₂; top) renaming (fin to fin₂)
import OCF.Align.LadderInfMain
module Iℕ = OCF.Align.LadderInfMain HSℕ
module I∞ = OCF.Align.LadderInfMain HS∞
module I₂ = OCF.Align.LadderInfMain HS₂
import OCF.Align.LadderInfTree
module Tℕ = OCF.Align.LadderInfTree HSℕ
module T∞ = OCF.Align.LadderInfTree HS∞
module T₂ = OCF.Align.LadderInfTree HS₂

ev₀ : Ev (suc zero) Fl
ev₀ = tt , (λ q → q)

-- 实例 ℕ: 与 LadderNFMain 同一条定理
Gℕ : ∀ m α → Goodᴺ (toZ (Tℕ.Tᵠ m α ev₀ zero))
Gℕ m α = Iℕ.GᴺTᵠ m α ev₀ zero

-- 实例 ℕ∪{∞}: ψ₀(Ω_{ψ₁(1)+α})
G∞ : ∀ α → Goodᴺ (toZ (T∞.Tᵠ ∞ α ev₀ zero))
G∞ α = I∞.GᴺTᵠ ∞ α ev₀ zero

G∞0 : Goodᴺ (toZ (T∞.Tᵠ ∞ zero ev₀ zero))
G∞0 = G∞ zero

-- ψ₀(Ω_{ψ₁(1)+1})
G∞1 : Goodᴺ (toZ (T∞.Tᵠ ∞ (suc zero) ev₀ zero))
G∞1 = G∞ (suc zero)

-- 实例 ω+ω: ψ₀(Ω_{Ω·(ω+n)+α}); top 1 的第 0 行读作 Ω_{ψ₁(1)+Ω}
G₂ : ∀ n α → Goodᴺ (toZ (T₂.Tᵠ (top n) α ev₀ zero))
G₂ n α = I₂.GᴺTᵠ (top n) α ev₀ zero

G₂ψ₁+Ω : Goodᴺ (toZ (T₂.Tᵠ (top 1) zero ev₀ zero))
G₂ψ₁+Ω = G₂ 1 zero
```
