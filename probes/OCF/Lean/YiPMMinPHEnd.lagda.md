# 最小表实例: PHEnd

参数化（工程）的最小表实例；验收文件。来源 `YiVTPHEnd`，通用下降证明引自 `YiPM` 接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMMinPHEnd where

open import OCF.Lean.YiPMTable using (tbᶠ)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; Ev-tw; Rt-tw)
import OCF.Lean.YiPMFold
open OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ
open import OCF.Lean.YiLSRead using (read)
import OCF.Lean.YiPMLSFold
open OCF.Lean.YiPMLSFold.F OCF.Lean.YiPMTable.tbᶠ using (OKB; ok-dS; ok-dL)
import OCF.Lean.YiPMLSTw1
open OCF.Lean.YiPMLSTw1.F OCF.Lean.YiPMTable.tbᶠ using (h₁)
import OCF.Lean.YiPMT2Frame
open OCF.Lean.YiPMT2Frame.F OCF.Lean.YiPMTable.tbᶠ using (ok-dW)
import OCF.Lean.YiPMEBShape
open OCF.Lean.YiPMEBShape.F OCF.Lean.YiPMTable.tbᶠ using (dB; br; br≼)
import OCF.Lean.YiPMEVReach
open OCF.Lean.YiPMEVReach.F OCF.Lean.YiPMTable.tbᶠ
open import OCF.Lean.YiPMMinEVEnd using (h₂; Br0; ε′; ρ′; ok0; hi1; c₁; B₁)
import OCF.Lean.YiMEBase as MB
import OCF.Lean.YiPMMEAnchor
open OCF.Lean.YiPMMEAnchor.F OCF.Lean.YiPMTable.tbᶠ using (one; two; Mβ₀; ψ₀ᵗ; ψ₁ᵗ; module G¹)
open import OCF.Lean.YiMWLow using (rd≼; tΩ; sem0)
import OCF.Lean.YiPMPHBase
open OCF.Lean.YiPMPHBase.F OCF.Lean.YiPMTable.tbᶠ using (three; u₂; Mβ₂; module G²)
import OCF.Lean.YiPMPHCtx
open OCF.Lean.YiPMPHCtx.F OCF.Lean.YiPMTable.tbᶠ using (module Ctx3)
import OCF.Lean.YiRefTw2 as R2
import OCF.Align.EboLeanDef as E
open E using (HC; fsn; ψ; natT; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
import OCF.Align.EboLeanBase as B
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.StandardOmega using (NF₁; n[]; n∷; nψ; sC; Bnd₁; vh; vd; vs; vt; bnd[];
  Flat; f[]; f∷; flatVis; flatBnd; f1; fΩ; nf1; nfβ)
open import OCF.Lean.YiNFOCase using (ΩΩ; tA; tB; nA₁; nfB; z<; f2; nf2₁; flatG; flatGB; n1ᴮ; n2ᴮ; nΩΩᴮ)
open import OCF.Lean.YiNFO using (mono<)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiMTTab using (EBOᶻ)   -- 改: 搬到新主线的闭项
open import OCF.Lean.YiPMMinTw using (EBOᶻ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)

import OCF.Lean.YiPMPHEnd as Generic
open Generic.F OCF.Lean.YiPMTable.tbᶠ public

path₃ : three ⇐ h₁ c₁
-- 改: 带表时链的起点是 `next 1`, 它的第 2 个孩子的层号是 3 (原来是后继下 ℕ 极限的第 1 个孩子)
path₃ = ⇐l 0 (⇐l 0 (⇐l 0 (⇐l 2 ⇐r)))

low3 : Lo³ (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
low3 = reach³ path₃ (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
  (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) hi1 {- 改: 原为 hi-dW 作用在全路径的 Hi 上 -}

t₃≼br2 : (h : HC t₃) → R2.Rt h ≼ read (br 2)
t₃≼br2 h = ≼-trans (low3 h) (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

t₃≼EBO : (h : HC t₃) → R2.Rt h ≼ read EBOᶜ
t₃≼EBO h = ≼-trans (t₃≼br2 h) (br≼ 2)

t₃≼EBOᴿ : (h : HC t₃) → R2.Rt h ≼ readRW EBOᶻ
t₃≼EBOᴿ h = up≼ EBOᶻ-R (t₃≼EBO h)

inst₃ : R2.Rt h₃ ≼ readRW EBOᶻ
inst₃ = t₃≼EBOᴿ h₃

tA≺EBOᴿ′ : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW EBOᶻ
tA≺EBOᴿ′ h = ≼-trans (A≺3 h h₃) inst₃
```
