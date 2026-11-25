# 验收: 终点层号一般的下降 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiANReach` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTANReach where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (Ev; Rt)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiVTLSFold using (OKB; ok-dS; ok-dL)
open import OCF.Lean.YiVTT2Frame using (ok-dW)
open import OCF.Lean.YiVTEVReach
open import OCF.Lean.YiVTMEAnchor using (two)
open import OCF.Lean.YiVTPHBase using (three)
open import OCF.Lean.YiVTPHEnd using (t₃; Lo³; module AtThree)
open import OCF.Lean.YiNFOCase using (tA)
import OCF.Lean.YiRefTw2 as R2
import OCF.Align.EboLeanDef as E
open E using (HC)
open import OCF.Align.Value using (_≼_; ≼-trans)

module Reach (n₀ : LF) (t : E.T) where

  LoG : (ℓ : LF) → Ev ℓ → Rt ℓ → Base ℓ → Set
  LoG ℓ ε ρ B = (h : HC t) → R2.Rt h ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))

  Anchor : Set
  Anchor = (ε : Ev n₀) (ρ : Rt n₀) (B : Base n₀) → OKB n₀ B → Hi n₀ B → LoG n₀ ε ρ B

  reachG : Anchor → ∀ {ℓ} → n₀ ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → LoG ℓ ε ρ B
  reachG an ⇐r ε ρ B ok hi = an ε ρ B ok hi
  reachG an (⇐s {a} p) ε ρ B ok hi h =
    ≼-trans (reachG an p ε ρ (dS a ε ρ B zero) (ok-dS ε ρ B ok zero) (hi-dS a ε ρ B hi zero) h) (suc≽ a ε ρ B ok)
  reachG an (⇐l {g} n p) ε ρ B ok hi h =
    ≼-trans (reachG an p (ε n) (proj₁ ρ n) (dL g ε ρ B n (preΩ g n)) (ok-dL g ε ρ B ok n (preΩ g n)) (hi-dL g ε ρ B hi n (preΩ g n)) h)
      (lim≽ g ε ρ B n)
  reachG an (⇐w {k} {h = f} p) ε ρ B ok hi h =
    ≼-trans (reachG an p (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (dW k f ε ρ B zero zero) (ok-dW k f ε ρ B ok zero zero) (hi-dW k f ε ρ B hi zero zero) h)
      (Ω≽0 k f ε ρ B)

reach₂ : ∀ {ℓ} → two ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo ℓ ε ρ B
reach₂ = Reach.reachG two tA (λ _ _ B ok hi → AtTwo.atTwo B ok hi)

reach₃ : ∀ {ℓ} → three ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo³ ℓ ε ρ B
reach₃ = Reach.reachG three t₃ (λ _ _ B ok hi → AtThree.atThree B ok hi)
```
