# 验收: 塔第 2 项不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (V131 的塔一侧) (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiEVTw2` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTEVTw2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; inb)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead using (read; limcum≽; plus≽)
open import OCF.Lean.YiVTLSFold using (OKB; ok-B₀)
open import OCF.Lean.YiVTLSTw1 using (h₁; εh; ρh; G; G-nz; pt)
open import OCF.Lean.YiVTLSBtbo using (btbo-tw1)
open import OCF.Lean.YiVTT2Frame using (ε¹; ρ¹; β; zc; rowβ; nzβ; ββ≼tw2; ok-dW; IsLim)
open import OCF.Lean.YiVTEmb using (rowT; rowG)
import OCF.Lean.YiDropRow as DR
open import OCF.Lean.YiVTEVReach
open import OCF.Lean.YiVTMEAnchor using (two)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA)
open import OCF.Align.EboLeanDef using (HC)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Lean.YiMTTab using (twᶻ)
open import OCF.Lean.YiVTTw using (twᶻ-R)
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
