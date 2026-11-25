# 精简块的统一表接口

参数化（工程），数学内容与 `YiTBFam`、`YiLTFold`、`YiLTLim`、`YiLTKid` 相同；验收文件。
这些证明本已量化任意表；此处复用原证明，统一有限、自身、极限与 Ω 形状入口，实例只选表。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMThin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; proj₁)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Tr⁺)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; rb-no; ψ)
open import OCF.Lean.YiMTTab using (rbᶻ)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLLow using (Sb; pth)
open import OCF.Lean.YiLRBridge using (τ; τ₂)
open import OCF.Lean.YiRBFam using (Pt; pt)
open import OCF.Lean.YiHCRel using (M⁰)
open import OCF.Lean.YiANFam using (ψᴺ)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiTBFam as F
import OCF.Lean.YiLTFold as H
import OCF.Lean.YiLTLim as W
import OCF.Lean.YiLTKid as K
open K using (ℓ¹)
import OCF.Lean.YiLTLift as LL

Tables : Set
Tables = (ℓ : L) → Rb ℓ

module For (rows : Tables) where
  Qu : ∀ {t} (o : Ok zero) (B : Base zero) (w : zero ≤ zero) (b : Tr⁺ zero)
     → M⁰ (ψᴺ 0 t) (proj₁ b) → ∀ {s y} → M⁰ s y
     → M⁰ (ψᴺ 0 (t ++ s)) (proj₁ (ψ zero o (rows zero) B zero w b y))
  Qu o B = H.Qu o (rows zero) B

  module Self (N : ℕ) (o : Ok (fn (suc N))) (B : Base (fn (suc N))) (β : Tr⁺ (fn (suc N))) =
    H.Self N o (rows (fn (suc N))) B β

  module Finite where
    open H public using (LF; chain; sΩ-LF; LFA; LFAB; LFP; LFPB)
    open F public using (ψ-⊵; feedF; feed≡; cb)

  module Limit (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : (n : ℕ) → G n ≤ G (suc n))
      (canR : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R n) ≡ pth s) where
    module LT = W.LimT G d eG R canR
    module LU = W.LimU G d eG R canR
    module Fold (oc : (k : ℕ) → Ok (G k)) (B : Base LT.Lω) (t₀ : E.T) (gb : LT.GBω B t₀) =
      LT.Fold oc (rows LT.Lω) B t₀ gb
    module Uniform (oc : (k : ℕ) → Ok (G k)) (B : Base LT.Lω) (t₀ : E.T) (gb : LT.GBω B t₀)
      (ws : ∀ n → zero ≤ G n) (P : ∀ n → Pt (d n) 0)
      (q : ∀ n → τ {j = 0} (eG n) (ws n) ≡ pt (P n)) =
      LU.FoldU oc (rows LT.Lω) B t₀ gb ws P q

  module Ω = K.Top K.o¹ (rows ℓ¹) [] (K.Sem.Kidˢ (rows ℓ¹))
  module Lift = LL.Inst (rows ℓ¹)

module Empty = For rb-no
module Minimum = For rbᶻ
```
