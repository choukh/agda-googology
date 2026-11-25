# 候选 A 的塔第 1 项不低于 BTBO 的参照

> 验收文件 (读回 `YiBRValue.readRW`), 树、折叠、合法性一行不改. 编译定理, 无前提: 候选 A 的塔第 1 项与 F2 的塔第 1 项逐构造子相关 (`twᶜ-RK1`), 所以 `btbo-tw1ᴷ : D.BTBOᴵ ≼ readRW (twᶜ 1)` (候选 A 的 `YiKVFold.twᶜ`), 且与主线的塔第 1 项读回 `≅` (`same-tw1ᴷ`).
> 做法: 塔第 1 项是 Ω 结点链的部分和 (`form`, `refl`); 链的每一行与回灌一步都落到读出层号 `zero ⊕ ↑ zero z` 上 (不含 Ω 形状), 用 [YiKARel](YiKARel.lagda.md) 的 `AK`, `SK`. 候选 A 在这一项上不经分支侧一行 (左项都是零). 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKATw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel hiding (RelE)
open import OCF.Lean.YiBRLem hiding (E→L; E-at; E-at⁼)
open import OCF.Lean.YiBROps hiding (emb-R; emb-mono-R)
open import OCF.Lean.YiBRFold using (iterR)
open import OCF.Lean.YiBRTw using (↑-L)
open import OCF.Lean.YiKARel
open import OCF.Lean.YiLSTw1 using (G; G-nz; K; pt)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiBRValue using (readRW; up≼; rel≅; same-tw)
import OCF.Lean.YiRWFold as RW
import OCF.Align.Level as L
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.Value using (_≼_)
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
ab-W : ∀ {a a′ b b′} → RelL b b′ → RelW (ab→≤ (ab⊕ a b)) (F.lift a′ b′)
ab-W lz         = wself
ab-W (lS r)     = winuS (ab-W r)
ab-W (lL r)     = winuL (λ n → ab-W (r n))
ab-W (lΩ rk rh) = winuΩ (λ c c′ rc → ab-W (rh c c′ rc))

rG : {z : Tr zero} {z′ : F.Tr F.zero} (r : RelT zero F.zero z z′)
   → RelT zero F.zero (proj₁ (GK z)) (G z′) × RelD zero F.zero (proj₂ (GK z)) (G-nz z′)
rG r = AK (h₁-EK r) (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK (h₁-EK r))) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (E→LK (h₁-EK r)))

rK : (z : Tr zero) (z′ : F.Tr F.zero) (r : RelT zero F.zero z z′) → RelT zero F.zero (sK z) (K z′)
rK z z′ r = proj₁ (SK (h₁-EK r) (λ i u → Ωt i) (F.B₀ _) (B₀-RK (E→LK (h₁-EK r)))
  (∙-R wself (idl-R (ab-W (↑-L lz r)))) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (E→LK (h₁-EK r))))

ch : (n : ℕ) → RelT zero F.zero (iter sK zero n) (pt n)
ch = iterR (RelT zero F.zero) iz rK
```

## 塔第 1 项

```agda
twᶜ-RK1 : RelT zero F.zero (twᶜ 1) (F.twᶜ 1)
twᶜ-RK1 = limc-R (λ n → GK (iter sK zero n)) (λ n → proj₁ (rG (ch n))) (λ n → proj₂ (rG (ch n)))

btbo-tw1ᴷ : D.BTBOᴵ ≼ readRW (twᶜ 1)
btbo-tw1ᴷ = up≼ twᶜ-RK1 btbo-tw1

same-tw1ᴷ : readRW (twᶜ 1) L.≅ readRW (RW.twᶜ 1)
same-tw1ᴷ = L.≅-trans (rel≅ twᶜ-RK1) (L.≅-sym (same-tw 1))
```
