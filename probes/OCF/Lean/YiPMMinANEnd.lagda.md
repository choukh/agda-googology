# 最小表实例: ANEnd

参数化（工程）的最小表实例；验收文件。来源 `YiVTANEnd`，通用下降证明引自 `YiPM` 接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMMinANEnd where

open import OCF.Lean.YiPMTable using (tbᶠ)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; Ev-tw; Rt-tw)
import OCF.Lean.YiPMFold
open OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ
open import OCF.Lean.YiLSRead using (read)
import OCF.Lean.YiPMLSFold
open OCF.Lean.YiPMLSFold.F OCF.Lean.YiPMTable.tbᶠ using (OKB)
import OCF.Lean.YiPMLSTw1
open OCF.Lean.YiPMLSTw1.F OCF.Lean.YiPMTable.tbᶠ using (h₁)
import OCF.Lean.YiPMT2Frame
open OCF.Lean.YiPMT2Frame.F OCF.Lean.YiPMTable.tbᶠ using (ok-dW)
import OCF.Lean.YiPMEBShape
open OCF.Lean.YiPMEBShape.F OCF.Lean.YiPMTable.tbᶠ using (dB; br; br≼)
import OCF.Lean.YiPMEVReach
open OCF.Lean.YiPMEVReach.F OCF.Lean.YiPMTable.tbᶠ using (Hi; hi-dW; _⇐_; ⇐r; ⇐s; ⇐l; Ω≽0; Ω≽1)
open import OCF.Lean.YiPMMinEVEnd using (h₂; Br0; ε′; ρ′; ok0; hi1; c₁; B₁)
import OCF.Lean.YiMEBase as MB
open import OCF.Lean.YiMWLow using (rd≼; tΩ; sem0)
open import OCF.Lean.YiPMMinPHEnd using (t₃)
import OCF.Lean.YiRefTw2 as R2
import OCF.Align.EboLeanDef as E
open E using (HC; fsn; ψ; natT; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
import OCF.Align.EboLeanBase as B
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Standard using (Ctbl; c[]; c∷)
open import OCF.Align.StandardOmega using (NF₁; n[]; n∷; nψ; sC; Bnd₁; vh; vd; vs; vt; bnd[];
  Flat; f[]; f∷; flatVis; flatBnd; f1; fΩ; nf1; nfβ)
open import OCF.Lean.YiNFOCase using (ΩΩ; tA; nA₁; z<; flatG; flatGB; n1ᴮ; nΩΩᴮ)
open import OCF.Lean.YiNFO using (mono<)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiMTTab using (EBOᶻ)   -- 改: 搬到新主线的闭项
open import OCF.Lean.YiPMMinTw using (EBOᶻ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
import OCF.Lean.YiPMANFam
open OCF.Lean.YiPMANFam.F OCF.Lean.YiPMTable.tbᶠ using (fin; ψᴺ; Ωᴺ)
import OCF.Lean.YiPMANLv
open OCF.Lean.YiPMANLv.F OCF.Lean.YiPMTable.tbᶠ using (module Lv)
import OCF.Lean.YiPMANReach
open OCF.Lean.YiPMANReach.F OCF.Lean.YiPMTable.tbᶠ using (module Reach)

import OCF.Lean.YiPMANEnd as Generic
open Generic.F OCF.Lean.YiPMTable.tbᶠ public

kid : LF → ℕ → LF
kid (lim g) n = g n
kid x       _ = x

pre : LF → LF
pre (suc a) = a
pre x       = x

G : ℕ → LF
-- 改: 带表时链的起点是 `next 1`, 前三步之后直接是 ℕ 极限层号, 第 k 个孩子是 `fin (k+1)`
G k = kid (kid (kid (kid (h₁ c₁) 0) 0) 0) k

one : Tr zero
one = suc zero

num : ℕ → Tr zero
num zero    = zero
num (suc j) = suc (num j)

shape : ∀ k → G k ≡ zero ⊕ ↑ zero (iter (one +_) one k)
shape k = refl

one+ : ∀ j → one + num j ≡ num (suc j)
one+ zero    = refl
one+ (suc j) = cong suc (one+ j)

I≡ : ∀ k → iter (one +_) one k ≡ num (suc k)
I≡ zero    = refl
I≡ (suc k) = trans (cong (one +_) (I≡ k)) (one+ (suc k))

ι-num : ∀ j → ι zero (num j) ≡ num j
ι-num zero    = refl
ι-num (suc j) = cong suc (ι-num j)

↑num : ∀ j → ↑ zero (num j) ≡ fin j
↑num zero    = refl
↑num (suc j) = cong suc (↑num j)

0⊕ : ∀ j → zero ⊕ fin j ≡ fin j
0⊕ zero    = refl
0⊕ (suc j) = cong suc (0⊕ j)

gk : ∀ k → G k ≡ fin (suc k)
gk k = trans (shape k)
  (trans (cong (λ x → zero ⊕ ↑ zero x) (I≡ k))
    (trans (cong (zero ⊕_) (↑num (suc k))) (0⊕ (suc k))))

pathN : ∀ m → fin (suc (suc (suc m))) ⇐ h₁ c₁
pathN m = ⇐l 0 (⇐l 0 (⇐l 0 (⇐l (suc (suc m)) (subst (fin (suc (suc (suc m))) ⇐_) (sym (gk (suc (suc m)))) ⇐r))))

module _ (m : ℕ) where
  open Reach (fin (suc (suc (suc m)))) (tN m)

  lowN : LoG (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
  lowN = reachG (AtN.atN m) (pathN m) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
    (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) hi1 {- 改: 原为 hi-dW 作用在全路径的 Hi 上 -}

  tN≼br2 : (h : HC (tN m)) → R2.Rt h ≼ read (br 2)
  tN≼br2 h = ≼-trans (lowN h) (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

  tN≼EBO : (h : HC (tN m)) → R2.Rt h ≼ read EBOᶜ
  tN≼EBO h = ≼-trans (tN≼br2 h) (br≼ 2)

  tN≼EBOᴿ : (h : HC (tN m)) → R2.Rt h ≼ readRW EBOᶻ
  tN≼EBOᴿ h = up≼ EBOᶻ-R (tN≼EBO h)

  instN : R2.Rt (hN m) ≼ readRW EBOᶻ
  instN = tN≼EBOᴿ (hN m)
```
