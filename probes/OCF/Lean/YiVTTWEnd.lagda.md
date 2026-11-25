# 验收: 终点闭项严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiTWEnd` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTTWEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (Ev; Rt; Ev-tw; Rt-tw)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead using (read; ◃→≺)
open import OCF.Lean.YiVTLSFold using (OKB; ok-dL)
open import OCF.Lean.YiVTLSTw1 using (h₁)
open import OCF.Lean.YiVTT2Frame using (ok-dW)
open import OCF.Lean.YiVTEBShape using (dB; br; br≼)
open import OCF.Lean.YiVTEVReach using (Hi; hi-dL; hi-dW; _⇐_; ⇐r; ⇐s; ⇐l; reach; Ω≽0; Ω≽1)
open import OCF.Lean.YiVTEVEnd using (h₂; Br0; ε′; ρ′; ok0; hi1; c₁; B₁)
open import OCF.Lean.YiVTMEAnchor using (two)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA)
open import OCF.Align.EboLeanDef using (HC)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; s≼s; ≼l; ≼-trans; ≺→s≼)
open import OCF.Lean.YiMTTab using (EBOᶻ)   -- 改: 搬到新主线的闭项
open import OCF.Lean.YiVTTw using (EBOᶻ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)

kid0 : LF → LF
kid0 (lim g) = g zero
kid0 _       = zero

strictL : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → two ⇐ kid0 ℓ
  → (h : HC tA) → O.suc (R2.Rt h) ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))
strictL zero     ε ρ B ok hi ()
strictL (suc a)  ε ρ B ok hi ()
strictL (Ωₗ k f) ε ρ B ok hi ()
strictL (lim g)  ε ρ B ok hi p h =
  ≼l 1 (≼-trans (s≼s (reach p (ε 0) (proj₁ ρ 0) (dL g ε ρ B 0 zero) (ok-dL g ε ρ B ok 0 zero) (hi-dL g ε ρ B hi 0 zero) h))
    (≺→s≼ (◃→≺ (mono⊥ (lim g) ε ρ B (◃u (cumΩ g 0) 1 (Ωt (g 1)) (Ωt-nz (g 1)))))))

path₁ : two ⇐ kid0 (h₁ c₁)
-- 改: 同 YiVTEVEnd.path₂, 带表时孩子编号不同
path₁ = ⇐l 0 (⇐l 0 (⇐l 1 ⇐r))

tA≺br2 : (h : HC tA) → O.suc (R2.Rt h) ≼ read (br 2)
tA≺br2 h =
  ≼-trans (strictL (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
            (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) hi1 {- 改: 原为 hi-dW 作用在全路径的 Hi 上 -} path₁ h)
    (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

tA≺EBO : (h : HC tA) → O.suc (R2.Rt h) ≼ read EBOᶜ
tA≺EBO h = ≼-trans (tA≺br2 h) (br≼ 2)

tA≺EBOᴿ : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW EBOᶻ
tA≺EBOᴿ h = up≼ EBOᶻ-R (tA≺EBO h)

inst : O.suc (R2.Rt hA) ≼ readRW EBOᶻ
inst = tA≺EBOᴿ hA
```
