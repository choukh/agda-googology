# 龙骨原型: 塔第 1 项与龙骨第 1 项不低于 BTBO 的参照 (K(1))

> 验收文件 (读回 `YiBRValue.readRW`). 编译定理, 无前提: 原型折叠 (`YiKDFold`) 上 `btbo-tw1ᴰ : D.BTBOᴵ ≼ readRW (twᶜ 1)` 与 `btbo-kl1 : D.BTBOᴵ ≼ readRW (klᶜ 1)` (后者沿规范路径 `zp`); `twᶜ 1` 与主线的读回 `≅` (`same-tw1ᴰ`).
> 做法照 `YiKATw1` 与 `YiKCSem.btbo-b′`: 链的每一行落在不含 Ω 形状的层号 `zero ⊕ ↑ zero z` 上, 用 [YiKDRel](YiKDRel.lagda.md) 的 `AK`, `SK` 对 F2; 龙骨一侧的行是 F2 的 `K`, 读回与 `G` 同值 (`KG`). 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKDTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKDPath
open import OCF.Lean.YiKDFold
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel hiding (RelE)
open import OCF.Lean.YiBRLem hiding (E→L; E-at; E-at⁼)
open import OCF.Lean.YiBROps hiding (emb-R; emb-mono-R)
open import OCF.Lean.YiBRFold using (iterR)
open import OCF.Lean.YiBRTw using (↑-L)
open import OCF.Lean.YiKDRel
open import OCF.Lean.YiKDKeel using (klᶜ; klᶜ⁺; Fc; Ok-kl)
open import OCF.Lean.YiLSTw1 using (G; G-nz; K; pt; KG)
open import OCF.Lean.YiDropRow using (limc≼cum)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiBRValue using (readRW; up≼; rel≅; same-tw)
import OCF.Lean.YiRWFold as RW
import OCF.Align.Level as L
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
```

## 形状

```agda
h₁ᴷ : Tr zero → L
h₁ᴷ z = zero ⊕ ↑ zero z

o₁ : Ok (tw 1)
o₁ = Ok-tw 1

GK : Tr zero → Tr⁺ zero
GK z = ψ (h₁ᴷ z) (proj₂ o₁ z) (λ i u → Ωt i) zero (z≤ (h₁ᴷ z)) (Ωt zero) (proj₁ (Ωt (h₁ᴷ z)))

sK : Tr zero → Tr zero
sK z = proj₁ (ψ (h₁ᴷ z) (proj₂ o₁ z) (λ i u → Ωt i) zero (self ∙ kh o₁ z) (Ωt zero) (proj₁ (Ωt (h₁ᴷ z))))

form : twᶜ 1 ≡ proj₁ (limc⁺ (λ n → GK (iter sK zero n)))
form = refl
```

## 路径与链

`kh o₁ z` 是证书读出的路径, 与 F2 的 `lift` 相关.

```agda
ab-W : ∀ {a a′ b b′} (e : OkO a b) → RelL b b′ → RelW (ab→≤ (ab⊕ a b e)) (F.lift a′ b′)
ab-W e lz         = wself
ab-W e (lS r)     = winuS (ab-W (proj₂ e tt) r)
ab-W e (lL r)     = winuL (λ n → ab-W (proj₂ e n) (r n))
ab-W e (lΩ rk rh) = winuΩ (λ c c′ rc → ab-W (proj₂ e c) (rh c c′ rc))

rG : {z : Tr zero} {z′ : F.Tr F.zero} (r : RelT zero F.zero z z′)
   → RelT zero F.zero (proj₁ (GK z)) (G z′) × RelD zero F.zero (proj₂ (GK z)) (G-nz z′)
rG r = AK (h₁-EK r) (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK (h₁-EK r))) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (E→LK (h₁-EK r)))

rK : (z : Tr zero) (z′ : F.Tr F.zero) (r : RelT zero F.zero z z′) → RelT zero F.zero (sK z) (K z′)
rK z z′ r = proj₁ (SK (h₁-EK r) (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK (h₁-EK r)))
  (∙-R wself (idl-R (ab-W (OkO↑ zero zero tt self z) (↑-L lz r)))) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (E→LK (h₁-EK r))))

ch : (n : ℕ) → RelT zero F.zero (iter sK zero n) (pt n)
ch = iterR (RelT zero F.zero) iz rK
```

## 塔第 1 项

```agda
twᶜ-RD1 : RelT zero F.zero (twᶜ 1) (F.twᶜ 1)
twᶜ-RD1 = limc-R (λ n → GK (iter sK zero n)) (λ n → proj₁ (rG (ch n))) (λ n → proj₂ (rG (ch n)))

btbo-tw1ᴰ : D.BTBOᴵ ≼ readRW (twᶜ 1)
btbo-tw1ᴰ = up≼ twᶜ-RD1 btbo-tw1

same-tw1ᴰ : readRW (twᶜ 1) L.≅ readRW (RW.twᶜ 1)
same-tw1ᴰ = L.≅-trans (rel≅ twᶜ-RD1) (L.≅-sym (same-tw 1))
```

## 龙骨第 1 项

`klᶜ 1` 的行与回灌都是 `Fc` (`YiKDKeel.keel-chain`), 即上面的 `sK` 带非零; 逐项对 F2 的 `K (pt n)`.

```agda
K-nz : (x : F.Tr F.zero) → F._⊢_◃_ F.zero F.zero (K x)
K-nz x = F.nzs _ _ _ (F.B₀ _) F.zero _ (F.suc F.zero) F.◃s (F.Ωt _)

rF : (z : Tr zero) (z′ : F.Tr F.zero) (r : RelT zero F.zero z z′)
   → RelT zero F.zero (proj₁ (Fc o₁ z)) (K z′) × RelD zero F.zero (proj₂ (Fc o₁ z)) (K-nz z′)
rF z z′ r = SK (h₁-EK r) (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK (h₁-EK r)))
  (∙-R wself (idl-R (ab-W (OkO↑ zero zero tt self z) (↑-L lz r)))) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (E→LK (h₁-EK r)))

klᶜ-R1 : RelT zero F.zero (klᶜ 1) (F.limc (λ n → K (pt n)) (λ n → K-nz (pt n)))
klᶜ-R1 = limc-R (λ n → Fc o₁ (iter sK zero n)) (λ n → proj₁ (rF _ _ (ch n))) (λ n → proj₂ (rF _ _ (ch n)))

btbo-kl1 : D.BTBOᴵ ≼ readRW (klᶜ 1)
btbo-kl1 = up≼ klᶜ-R1 (≼-trans btbo-tw1
  (limc≼cum (λ n → G (pt n)) (λ n → K (pt n)) (λ n → G-nz (pt n)) (λ n → ≅→≼ (L.≅-sym (KG (pt n))))))
```
