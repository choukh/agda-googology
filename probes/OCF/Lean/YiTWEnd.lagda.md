# 验收: 终点闭项严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `tA≺EBOᴿ : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW RW.EBOᶜ` (主线精简块); F2 上是 `tA≺EBO`.
> 做法: `strictL`, ℕ 极限层号上 Ω 树的第 0 行经 `YiEVReach.reach` 不低于参照, 第 1 行字面地在第 0 行之上, 所以整个折叠严格更高; 代入 [YiEVEnd](YiEVEnd.lagda.md) 的层号 `h₁ c₁` 与底 `B₁`.
> 只是 "参照的后继不高于终点", 不给出终点的值; 不涉及上界. 不经最小见证 V (见证一侧在 [YiTWLow](YiTWLow.lagda.md)).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTWEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (Ev; Rt; Ev-tw; Rt-tw)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; ◃→≺)
open import OCF.Lean.YiLSFold using (OKB; ok-dL)
open import OCF.Lean.YiLSTw1 using (h₁)
open import OCF.Lean.YiT2Frame using (ok-dW)
open import OCF.Lean.YiEBShape using (dB; br; br≼)
open import OCF.Lean.YiEVReach using (Hi; hi-dL; hi-dW; _⇐_; ⇐r; ⇐s; ⇐l; reach; Ω≽0; Ω≽1)
open import OCF.Lean.YiEVEnd using (h₂; Br0; ε′; ρ′; ok0; hi0; c₁; B₁)
open import OCF.Lean.YiMEAnchor using (two)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA; hA)
open import OCF.Align.EboLeanDef using (HC)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; s≼s; ≼l; ≼-trans; ≺→s≼)
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiBRTw using (EBOᶜ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
```

## ℕ 极限层号: 第 1 行严格在第 0 行之上

量化域: 一切 ℕ 极限层号, 证据, 路线, 满足 `OKB` 与 `Hi` 的底; 前提是第 0 个孩子沿下降路径到层号 2 (`kid0`).

```agda
kid0 : LF → LF
kid0 (lim g) = g zero
kid0 _       = zero

strictL : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → two ⇐ kid0 ℓ
  → (h : HC tA) → O.suc (R2.Rt h) ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))
strictL zero     ε ρ B ok hi ()
strictL (suc a)  ε ρ B ok hi ()
strictL (Ωₗ k f) ε ρ B ok hi ()
strictL (lim g)  ε ρ B ok hi p h =
  ≼l 1 (≼-trans (s≼s (reach p (ε 0) (proj₁ ρ 0) (dL g ε ρ B 0 zero) (ok-dL g ε ρ B ok 0 zero) (hi-dL g ε ρ B hi 0 zero) h))
    (≺→s≼ (◃→≺ (mono⊥ (lim g) ε ρ B (◃u (cumΩ g 0) 1 (Ωt (g 1)) (Ωt-nz (g 1)))))))
```

## 终点

层号 `h₁ c₁` 的第 0 个孩子沿 ℕ 极限的孩子 0, 0, 后继, 孩子 0 走到 2 (`path₁`, 由类型检查确认); 其余与 `YiEVEnd.tA≼br2` 同.

```agda
path₁ : two ⇐ kid0 (h₁ c₁)
path₁ = ⇐l 0 (⇐l 0 (⇐s (⇐l 0 ⇐r)))

tA≺br2 : (h : HC tA) → O.suc (R2.Rt h) ≼ read (br 2)
tA≺br2 h =
  ≼-trans (strictL (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
            (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) (hi-dW zero h₁ ε′ ρ′ Br0 hi0 c₁ zero) path₁ h)
    (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

tA≺EBO : (h : HC tA) → O.suc (R2.Rt h) ≼ read EBOᶜ
tA≺EBO h = ≼-trans (tA≺br2 h) (br≼ 2)

tA≺EBOᴿ : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW RW.EBOᶜ
tA≺EBOᴿ h = up≼ EBOᶜ-R (tA≺EBO h)

inst : O.suc (R2.Rt hA) ≼ readRW RW.EBOᶜ
inst = tA≺EBOᴿ hA
```
