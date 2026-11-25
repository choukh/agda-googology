# 按表参数化: ANReach 的下降部分

参数化（工程），数学内容与 `YiVTANReach` 的下降部分相同；具体路径与出口另列，验收文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMANReach where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Unit using (⊤; tt)
  open import Data.Product using (_,_; proj₁; proj₂)

  open import OCF.Lean.YiLegBlock renaming (L to LF)
  open import OCF.Lean.YiLegOps
  open import OCF.Lean.YiLegPath using (Ev; Rt)
  import OCF.Lean.YiPMFold
  open OCF.Lean.YiPMFold.F tb
  open import OCF.Lean.YiLSRead using (read)
  import OCF.Lean.YiPMLSFold
  open OCF.Lean.YiPMLSFold.F tb using (OKB; ok-dS; ok-dL)
  import OCF.Lean.YiPMT2Frame
  open OCF.Lean.YiPMT2Frame.F tb using (ok-dW)
  import OCF.Lean.YiPMEVReach
  open OCF.Lean.YiPMEVReach.F tb
  import OCF.Lean.YiPMMEAnchor
  open OCF.Lean.YiPMMEAnchor.F tb using (two)
  import OCF.Lean.YiPMPHBase
  open OCF.Lean.YiPMPHBase.F tb using (three)
  import OCF.Lean.YiPMPHEnd
  open OCF.Lean.YiPMPHEnd.F tb using (t₃; Lo³; module AtThree)
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
