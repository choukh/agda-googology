# 验收: 塔第 2 项不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (V131 的塔一侧)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提: `tA≼tw2 : (h : HC tA) → R2.Rt h ≼ read (twᶜ 2)` (F2), 主线精简块上 `tA≼tw2ᴿ` (`readRW`).
> 做法: `β + β` 的折叠的第 1 行 (`YiT2Frame.rowβ 1`) 的底由 β 折出, `b⊥` 是塔第 1 项, 第 0 层分量对一切路径不低于它 (`compβ`); 沿 ℕ 极限的孩子 0, 0, 1 走到层号 2 (`path₁`), 用 [YiEVReach](YiEVReach.lagda.md) 的 `reach`; 再经 `ββ≼tw2`.
> 不经最小见证 V 本身, 没有证 `read V ≼ read (twᶜ 2)`; 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEVTw2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; inb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; limcum≽; plus≽)
open import OCF.Lean.YiLSFold using (OKB; ok-B₀)
open import OCF.Lean.YiLSTw1 using (h₁; εh; ρh; G; G-nz; pt)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiT2Frame using (ε¹; ρ¹; β; zc; rowβ; nzβ; ββ≼tw2; ok-dW)
import OCF.Lean.YiDropRow as DR
open import OCF.Lean.YiEVReach
open import OCF.Lean.YiMEAnchor using (two)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA)
open import OCF.Align.EboLeanDef using (HC)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼)
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiBRTw using (twᶜ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
```

## β 折到第 0 层, 沿任一孩子的路径

目标是第 0 层, 保留判定 `kp` 只可能给默认的一支 (第 0 层没有槽位); 默认一支的各行是 `1 + G (pt n)`, 与路径无关.

```agda
Kβ : (c : Tr zero) (w : zero ≤ h₁ c) (q : Pos zero) → (Br zero q → Tr zero) → Tr zero
Kβ c w q cv = Ω q (λ z → ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (inb c w) (Ωt zero) (Ωt-nz zero)
  (up zero (cv z) (Ωt (h₁ (cv z))) (Ωt-nz (h₁ (cv z)))))

compβ : (c : Tr zero) (w : zero ≤ h₁ c)
  → read (twᶜ 1) ≼ read (ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (inb c w) (Ωt zero) (Ωt-nz zero) β)
compβ c w = kp-ind (tw 1) ε¹ ρ¹ (inj₁ (inj₁ tt)) (inb c w) (λ X → read (twᶜ 1) ≼ read X) {K = Kβ c w} (λ ())
  (DR.limc≼cum (λ n → G (pt n)) (λ n → Ωt zero + ι zero (G (pt n))) (λ n → G-nz (pt n))
    (λ n → plus≽ (Ωt zero) (ι zero (G (pt n))) (≅→≼ (L.≅-sym (DR.ι₀≅ (G (pt n)))))))
```

## `β + β` 的第 1 行

```agda
BWc : Base (h₁ (zc 1))
BWc = dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) (zc 1) β

row1-form : rowβ 1 ≡ ψ⊥ (h₁ (zc 1)) (εh (zc 1)) (ρh (zc 1)) BWc (Ωt (h₁ (zc 1)))
row1-form = refl

okW : OKB (h₁ (zc 1)) BWc
okW = ok-dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) (ok-B₀ (tw 1)) (zc 1) β

hiW : Hi (h₁ (zc 1)) BWc
hiW = btbo-tw1 , λ w → ≼-trans btbo-tw1 (compβ (zc 1) w)

path₁ : two ⇐ h₁ (zc 1)
path₁ = ⇐l 0 (⇐l 0 (⇐l 1 ⇐r))

low1 : Lo (h₁ (zc 1)) (εh (zc 1)) (ρh (zc 1)) BWc
low1 = reach path₁ (εh (zc 1)) (ρh (zc 1)) BWc okW hiW
```

## 塔第 2 项

```agda
tA≼tw2 : (h : HC tA) → R2.Rt h ≼ read (twᶜ 2)
tA≼tw2 h = ≼-trans (low1 h) (≼-trans (limcum≽ rowβ nzβ 1 (≼-refl _)) ββ≼tw2)

tA≼tw2ᴿ : (h : HC tA) → R2.Rt h ≼ readRW (RW.twᶜ 2)
tA≼tw2ᴿ h = up≼ (twᶜ-R 2) (tA≼tw2 h)
```

实例 (前提可满足): `YiNFOCase.hA` 是 tA 的一个推导.

```agda
inst-tw2 : R2.Rt hA ≼ readRW (RW.twᶜ 2)
inst-tw2 = tA≼tw2ᴿ hA
```
