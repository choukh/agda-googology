# 最小表实例: Hi

参数化（工程）的最小表实例；验收文件。来源 `YiVTHi`，通用下降证明引自 `YiPM` 接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMMinHi where

open import OCF.Lean.YiPMTable using (tbᶠ)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; inb; Ev-tw; Rt-tw)
import OCF.Lean.YiPMFold
open OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ
open import OCF.Lean.YiLSRead using (read; limcum≽)
import OCF.Lean.YiPMLSFold
open OCF.Lean.YiPMLSFold.F OCF.Lean.YiPMTable.tbᶠ using (OKB)
import OCF.Lean.YiPMLSTw1
open OCF.Lean.YiPMLSTw1.F OCF.Lean.YiPMTable.tbᶠ using (h₁; lower-↑)
import OCF.Lean.YiPMT2Frame
open OCF.Lean.YiPMT2Frame.F OCF.Lean.YiPMTable.tbᶠ using (IsLim)
import OCF.Lean.YiPMEBBtbo
open OCF.Lean.YiPMEBBtbo.F OCF.Lean.YiPMTable.tbᶠ using (Start; module Chain; module Lemmas; module Btbo)
open import OCF.Lean.YiPMMinEmb using (rowT; rowG)
open import OCF.Align.BTBOFullEmb using (Ψ-emb)
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
open import OCF.Align.YiBtValBT using (module D)

module HiΩ (B : Base (tw 1)) (ok : OKB (tw 1) B) (st : Start B) where
  open Chain B using (pt)
  open Btbo B ok st using (emb; chainV)

  hiΩ : (c : Tr zero) → IsLim c → (w : zero ≤ h₁ c) (b : Tr zero) (nb : zero ⊢ zero ◃ b)
    → D.BTBOᴵ ≼ read (ψs (tw 1) (Ev-tw 1) (Rt-tw 1) B zero (inb c w) b nb (Ωt (tw 1)))
  hiΩ c lc w b nb =
    kp-ind (tw 1) (Ev-tw 1) (Rt-tw 1) (inj₁ (inj₁ tt)) (inb c w) (λ X → D.BTBOᴵ ≼ read X)
      {K = λ q cv → Ω q (λ z → rowT B c w b nb (cv z))} (λ ())
      (l≼ (λ n → ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n))))
        (limcum≽ (λ k → rowT B c w b nb (pt k))
          (λ k → nzs (tw 1) (Ev-tw 1) (Rt-tw 1) B zero (inb c w) b nb (up zero (pt k) (Ωt (h₁ (pt k))) (Ωt-nz (h₁ (pt k)))))
          (suc (proj₁ (chainV n)))
          (≼-trans (lower-↑ (pt (suc (proj₁ (chainV n))))) (rowG B c lc w b nb (pt (suc (proj₁ (chainV n)))))))))
```
