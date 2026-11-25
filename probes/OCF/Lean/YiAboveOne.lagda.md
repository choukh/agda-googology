# `T⁺` 严格高过 BTBO, 不低于 ψ₀(Ω_Ω+1) (无前提)

验收文件. 编译定理: `above : L.suc D.BTBOᴵ ≼ NA.read NT.T⁺` (严格高过 BTBO), `ΩΩ+1 : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read NT.T⁺`.
参照 `ψ⁰ (suc (Ω ℓ₀))` 由 `S2.ts-label` 验收为 ψ₀(Ω_Ω+1); 它定义性地是 `lim (iter (BTBOᴵ +_) zero)`. 办法: 位置 `suc top` 是 `T⁺` 的根链第 1 点的第一位置 (`c₁`), 折叠保持第一位置 (`Ψ-cp`), 于是 `succ zero T₃` 是 `T⁺` 的第一位置, 再接 `btbo` 与 `suc-lower`.
只是下界, 不涉及上界与同值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAboveOne where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold
import OCF.Lean.YiNextTop as NT
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiNextValFin using (T₃≅; cp⊑ⁿ)
import OCF.Lean.YiBtboLower as YB
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; s≼s; ⊑→≼)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Stage2 as S2

-- 参照: Stage2 的 ψ₀(Ω_Ω+1) 代表, 种子是同一个 BTBO (定义性)
_ : L.ψ⁰ (L.Ω S2.ℓ₀) ≡ D.BTBOᴵ
_ = refl

bt₃ : D.BTBOᴵ ≼ NA.read NT.T₃
bt₃ = ≼-trans YB.btbo (≅→≼ T₃≅)

-- 根链第 1 点 = top + Φ₂ top; 沿 p₀ 结点的 top 支, 再沿 ω 倍的第 0 项, 到 top + top = suc top
c₁ : Cp (tw 2) (G.suc G.top) (chain (tw 2) NT.Φ₂ 1)
c₁ = inj₂ (inj₂ (inj₂ (0 , inj₁ refl)))

s⊑ : Cp zero (succ zero NT.T₃) NT.T⁺
s⊑ = inj₂ (1 , Ψ-cp zero NT.V₂ (λ _ → fold) c₁)

s≼ : NA.read (succ zero NT.T₃) ≼ NA.read NT.T⁺
s≼ = ⊑→≼ (NA.read (succ zero NT.T₃)) (cp⊑ⁿ (succ zero NT.T₃) NT.T⁺ s⊑)

above : L.suc D.BTBOᴵ ≼ NA.read NT.T⁺
above = ≼-trans (s≼s bt₃) NA.T₃+1≼T⁺

ΩΩ+1 : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read NT.T⁺
ΩΩ+1 = ≼-trans (NA.suc-lower {x = L.Ω S2.ℓ₀} NT.T₃ bt₃) s≼
```
