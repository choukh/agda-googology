# 验收: 终点闭项不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照, 严格高于 BTBO 的参照 (V131)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提: `tA≼EBOᴿ : (h : HC tA) → R2.Rt h ≼ readRW EBOᶜ` (主线精简块), 推论 `btbo≺EBOᴿ : L.suc D.BTBOᴵ ≼ readRW EBOᶜ`; F2 上是 `tA≼EBO`.
> 做法: 取 `EBOᶜ` 的第 2 支 (`YiEBShape.br 2`), 不经 Into. 它的底沿 Ω 结点第 0 个孩子收窄后, `b⊥` 是第 1 支 (不低于 BTBO), 第 0 层各分量是回退一行的输出, 不低于塔第 1 项 (`hi0`); 再走第 1 行与 ℕ 极限、后继的孩子到层号 2 (`path₂`), 用 [YiEVReach](YiEVReach.lagda.md) 的 `reach`.
> 不涉及上界; 不经最小见证 V.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEVEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; inb; ink; Ev; Rt; Ev-tw; Rt-tw)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; plus≽)
open import OCF.Lean.YiLSFold using (OKB)
open import OCF.Lean.YiLSTw1 using (h₁)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiT2Frame using (ok-dW)
open import OCF.Lean.YiEBShape using (dB; Fn; br; br≼; ok-dB)
open import OCF.Lean.YiEBBtbo using (btbo-dB1)
import OCF.Lean.YiDropRow as DR
open import OCF.Lean.YiEVReach
open import OCF.Lean.YiMEAnchor using (two)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA; btbo≺A)
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanTree using (hc-tower)
open import OCF.Lean.YiEXRow using (labR)
open import OCF.Align.Stage2 using (Lab-uniq)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; s≼s; ≼-trans; ≅→≼)
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiBRTw using (EBOᶜ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
```

## 第 2 支收窄到第 0 个孩子

`Br0`: 第 2 支的底在 Ω 结点层号 `tw 2` 的第 0 个孩子 (层号 `tw 1`) 上. 它的 `b⊥` 就是第 1 支; 第 0 层分量 (经 `inb zero` 的一切路径) 是前缀 `cumΩ tw 1` 朝第 0 层的折叠, 末一行是回退一行, 输出形如 `_ + ι zero (twᶜ 1)` (由 `hi0` 的类型检查确认).

```agda
h₂ : Tr (tw 1) → LF
h₂ c = tw 1 ⊕ ↑ (tw 1) c

Br0 : Base (tw 1)
Br0 = dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2) zero zero

ε′ : Ev (tw 1)
ε′ = proj₂ (proj₂ (Ev-tw 2) zero)

ρ′ : Rt (tw 1)
ρ′ = proj₂ (Rt-tw 2) zero

ok0 : OKB (tw 1) Br0
ok0 = ok-dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2) (ok-dB 2) zero zero

hi0 : Hi (tw 1) Br0
hi0 = btbo-dB1 , λ w → ≼-trans btbo-tw1 (plus≽ _ (ι zero (twᶜ 1)) (≅→≼ (L.≅-sym (DR.ι₀≅ (twᶜ 1)))))
```

## 第 1 行, 下降到层号 2

第 1 行的孩子下标是 `next Z`, Z 是上面的第 0 层分量 (`c₁-form`, 有限测试); 层号沿 ℕ 极限的孩子 0, 0, 0, 后继, 孩子 0 走到 2.

```agda
c₁ : Tr zero
c₁ = c1Ω zero h₁ ε′ ρ′ Br0

c₁-form : c₁ ≡ next (bs Br0 zero (ink self)) (ns Br0 zero (ink self))
c₁-form = refl

B₁ : Base (h₁ c₁)
B₁ = dW zero h₁ ε′ ρ′ Br0 c₁ zero

path₂ : two ⇐ h₁ c₁
path₂ = ⇐l 0 (⇐l 0 (⇐l 0 (⇐s (⇐l 0 ⇐r))))

low2 : Lo (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
low2 = reach path₂ (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
  (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) (hi-dW zero h₁ ε′ ρ′ Br0 hi0 c₁ zero)
```

## 终点

```agda
tA≼br2 : (h : HC tA) → R2.Rt h ≼ read (br 2)
tA≼br2 h = ≼-trans (low2 h) (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

tA≼EBO : (h : HC tA) → R2.Rt h ≼ read EBOᶜ
tA≼EBO h = ≼-trans (tA≼br2 h) (br≼ 2)

tA≼EBOᴿ : (h : HC tA) → R2.Rt h ≼ readRW RW.EBOᶜ
tA≼EBOᴿ h = up≼ EBOᶜ-R (tA≼EBO h)
```

## 推论: 严格高于 BTBO 的参照

BTBO 的参照与 ψ₀(Ω_Ω) 的记号树同标签 (`Lab-uniq`), 后者严格低于 tA 的 (`YiNFOCase.btbo≺A`).

```agda
btbo≼row₂ : D.BTBOᴵ ≼ R2.Rt (hc-tower 2)
btbo≼row₂ = ≅→≼ (L.≅-sym (Lab-uniq (labR (hc-tower 2)) BTBO-label))

btbo≺EBOᴿ : L.suc D.BTBOᴵ ≼ readRW RW.EBOᶜ
btbo≺EBOᴿ = ≼-trans (s≼s btbo≼row₂) (≼-trans (btbo≺A (hc-tower 2) hA) (tA≼EBOᴿ hA))
```
