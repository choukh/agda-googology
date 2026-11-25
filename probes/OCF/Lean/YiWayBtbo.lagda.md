# BTBO 是产出端折叠的闭项 `TΛᵖ` 的下界 (无前提)

验收文件. 编译定理 `btbo-Twᵖ2 : D.BTBOᴵ ≼ NA.read (P.Twᵖ 2)`, `btbo-TΛᵖ : D.BTBOᴵ ≼ NA.read P.TΛᵖ`, 都无前提, 只用下界. [YiDlVBtbo](YiDlVBtbo.lagda.md) 搬到 [YiProdFold](YiProdFold.lagda.md): 互模拟经 [YiWayRel](YiWayRel.lagda.md); 链点下一步的派发 `dl′ zero _` 定义性地是 `fold′`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWayBtbo where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLeanCore as M
import OCF.Lean.YiLeanFold as MF
import OCF.Lean.YiLeanTw3 as MT
import OCF.Lean.YiLeanAccFin as MA
import OCF.Lean.YiNextCore as N
import OCF.Lean.YiNextBase as NB
import OCF.Lean.YiNextAcc as NA
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiZipWay as Z
open import OCF.Lean.YiCtxAnn using (noM; noP)
open import OCF.Lean.YiCtxFold using (evF)
open import OCF.Lean.YiZipFold using (dl′)
import OCF.Lean.YiProdFold as P
open import OCF.Lean.YiNextValRel
open import OCF.Lean.YiNextValLgl
open import OCF.Lean.YiWayRel
open WayRel dl′ evF
open import OCF.Lean.YiDlVBtbo using (Vw; lvRʷ; psum≽)
import OCF.Lean.YiBtboLower as YB
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
```

## 1 观察与链点

```agda
FRᵖ : ∀ {a a′} → RR M.zero N.zero a a′ → ∀ l l′ → LglR M.zero N.zero a a′ l l′ → ∀ {Sb x′} →
  XRᵖ M.zero N.zero MT.⌜ a ⌝ NB.⌜ a′ ⌝ {Sb} (λ _ → MF.fold) x′ →
  RR M.zero N.zero (MT.F a l) (P.Ψᵖ N.zero (Vw a′ l′) Sb x′ N.G.top noM noP)
FRᵖ d l l′ lr xr = ΨRᵖ lz (lvRʷ d l l′ lr) xr rt noM noP

FLRᵖ : ∀ {a a′} (d : RR M.zero N.zero a a′) l l′ (lr : LglR M.zero N.zero a a′ l l′) → ∀ {Sb x′}
  (xr : XRᵖ M.zero N.zero MT.⌜ a ⌝ NB.⌜ a′ ⌝ {Sb} (λ _ → MF.fold) x′) →
  LglR M.zero N.zero (MT.F a l) (P.Ψᵖ N.zero (Vw a′ l′) Sb x′ N.G.top noM noP) (MT.F-lgl a l)
    (P.Ψᵖ-lgl N.zero (Vw a′ l′) Sb x′ N.G.top noM noP tt)
FLRᵖ d l l′ lr xr = ΨLglRᵖ lz (lvRʷ d l l′ lr) xr rt tt

Pᵖ : ℕ → WL.Pk N.zero
Pᵖ = P.ptsΩ N.zero NB.⌜_⌝ Vw

ptRᵖ : ∀ n → Σ (RR M.zero N.zero (MT.Pt.co (MT.pts n)) (WL.Pk.co (Pᵖ n)))
  λ _ → LglR M.zero N.zero (MT.Pt.co (MT.pts n)) (WL.Pk.co (Pᵖ n)) (MT.Pt.lw (MT.pts n)) (WL.Pk.lw (Pᵖ n))
ptRᵖ zero = rt , tt
ptRᵖ (suc n) = plusR lz d (FRᵖ d _ _ lr (λ _ _ _ _ → tt)) ,
  plusLglR lz d (FRᵖ d _ _ lr (λ _ _ _ _ → tt)) lr (FLRᵖ d _ _ lr (λ _ _ _ _ → tt))
  where
  d = proj₁ (ptRᵖ n)
  lr = proj₂ (ptRᵖ n)

obsᵖ : ℕ → NB.R
obsᵖ n = P.Ψᵖ N.zero (Vw (WL.Pk.co (Pᵖ n)) (WL.Pk.lw (Pᵖ n))) (λ _ → ⊥) (λ _ _ → Z.fold′) N.G.top noM noP

obs≅ᵖ : ∀ n → MA.read (MT.obs (MT.pts n)) L.≅ NA.read (obsᵖ n)
obs≅ᵖ n = read≅ (FRᵖ (proj₁ (ptRᵖ n)) _ _ (proj₂ (ptRᵖ n)) (λ _ _ _ _ → tt))
```

## 2 下界

```agda
Tw2-formᵖ : P.Twᵖ 2 ≡ N.G.lim (NB.psum N.zero obsᵖ)
Tw2-formᵖ = refl

T₃≼Twᵖ2 : MA.read MT.T₃ ≼ NA.read (P.Twᵖ 2)
T₃≼Twᵖ2 = l≼ (λ n → ≼l n (≼-trans (≅→≼ (obs≅ᵖ n)) (psum≽ obsᵖ n)))

btbo-Twᵖ2 : D.BTBOᴵ ≼ NA.read (P.Twᵖ 2)
btbo-Twᵖ2 = ≼-trans YB.btbo T₃≼Twᵖ2

Twᵖ≼TΛᵖ : ∀ n → NA.read (P.Twᵖ n) ≼ NA.read P.TΛᵖ
Twᵖ≼TΛᵖ n = ≼l n (psum≽ P.Twᵖ n)

btbo-TΛᵖ : D.BTBOᴵ ≼ NA.read P.TΛᵖ
btbo-TΛᵖ = ≼-trans btbo-Twᵖ2 (Twᵖ≼TΛᵖ 2)
```
