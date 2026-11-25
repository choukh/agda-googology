# 最小表实例: EVTw2

参数化（工程）的最小表实例；验收文件。来源 `YiVTEVTw2`，通用下降证明引自 `YiPM` 接口。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMMinEVTw2 where

open import OCF.Lean.YiPMTable using (tbᶠ)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; inb)
import OCF.Lean.YiPMFold
open OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ
open import OCF.Lean.YiLSRead using (read; limcum≽; plus≽)
import OCF.Lean.YiPMLSFold
open OCF.Lean.YiPMLSFold.F OCF.Lean.YiPMTable.tbᶠ using (OKB; ok-B₀)
import OCF.Lean.YiPMLSTw1
open OCF.Lean.YiPMLSTw1.F OCF.Lean.YiPMTable.tbᶠ using (h₁; εh; ρh; G; G-nz; pt)
import OCF.Lean.YiPMLSBtbo
open OCF.Lean.YiPMLSBtbo.F OCF.Lean.YiPMTable.tbᶠ using (btbo-tw1)
import OCF.Lean.YiPMT2Frame
open OCF.Lean.YiPMT2Frame.F OCF.Lean.YiPMTable.tbᶠ using (ε¹; ρ¹; β; zc; rowβ; nzβ; ββ≼tw2; ok-dW; IsLim)
open import OCF.Lean.YiPMMinEmb using (rowT; rowG)
import OCF.Lean.YiDropRow as DR
import OCF.Lean.YiPMEVReach
open OCF.Lean.YiPMEVReach.F OCF.Lean.YiPMTable.tbᶠ
import OCF.Lean.YiPMMEAnchor
open OCF.Lean.YiPMMEAnchor.F OCF.Lean.YiPMTable.tbᶠ using (two)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA)
open import OCF.Align.EboLeanDef using (HC)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Lean.YiMTTab using (twᶻ)
open import OCF.Lean.YiPMMinTw using (twᶻ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)

Kβ : (c : Tr zero) (w : zero ≤ h₁ c) (q : Pos zero) → (Br zero q → Tr zero) → Tr zero
Kβ c w q cv = Ω q (λ z → ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (inb c w) (Ωt zero) (Ωt-nz zero)
  (up zero (cv z) (Ωt (h₁ (cv z))) (Ωt-nz (h₁ (cv z)))))

-- 改: 带表时各行不再都是 `1 + G (pt n)`; 只对字面是 ℕ 极限的孩子 c 陈述, 各行不低于 `G (pt n)` 由 `YiVTEmb.rowG` 给出.
compβ : (c : Tr zero) → IsLim c → (w : zero ≤ h₁ c)
  → read (twᶜ 1) ≼ read (ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (inb c w) (Ωt zero) (Ωt-nz zero) β)
compβ c lc w = kp-ind (tw 1) ε¹ ρ¹ (inj₁ (inj₁ tt)) (inb c w) (λ X → read (twᶜ 1) ≼ read X) {K = Kβ c w} (λ ())
  (DR.limc≼cum (λ n → G (pt n)) (λ n → rowT (B₀ (tw 1)) c w (Ωt zero) (Ωt-nz zero) (pt n)) (λ n → G-nz (pt n))
    (λ n → rowG (B₀ (tw 1)) c lc w (Ωt zero) (Ωt-nz zero) (pt n)))

BWc : Base (h₁ (zc 1))
BWc = dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) (zc 1) β

row1-form : rowβ 1 ≡ ψ⊥ (h₁ (zc 1)) (εh (zc 1)) (ρh (zc 1)) BWc (Ωt (h₁ (zc 1)))
row1-form = refl

okW : OKB (h₁ (zc 1)) BWc
okW = ok-dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) (ok-B₀ (tw 1)) (zc 1) β

hiW : Hi (h₁ (zc 1)) BWc
hiW = btbo-tw1 , λ w → ≼-trans btbo-tw1 (compβ (zc 1) tt w)

path₁ : two ⇐ h₁ (zc 1)
path₁ = ⇐l 0 (⇐l 0 (⇐l 1 ⇐r))

low1 : Lo (h₁ (zc 1)) (εh (zc 1)) (ρh (zc 1)) BWc
low1 = reach path₁ (εh (zc 1)) (ρh (zc 1)) BWc okW hiW

tA≼tw2 : (h : HC tA) → R2.Rt h ≼ read (twᶜ 2)
tA≼tw2 h = ≼-trans (low1 h) (≼-trans (limcum≽ rowβ nzβ 1 (≼-refl _)) ββ≼tw2)

tA≼tw2ᴿ : (h : HC tA) → R2.Rt h ≼ readRW (twᶻ 2)   -- 改: 搬到新主线的闭项
tA≼tw2ᴿ h = up≼ (twᶻ-R 2) (tA≼tw2 h)

inst-tw2 : R2.Rt hA ≼ readRW (twᶻ 2)
inst-tw2 = tA≼tw2ᴿ hA
```
