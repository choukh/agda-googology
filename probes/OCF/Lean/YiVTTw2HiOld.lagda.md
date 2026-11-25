# 对照: 原主线塔第 2 项的同一条更高下界

> 验收文件 (读记号), 不进成品. 编译定理, 无前提 (新写): [YiVTTw2Hi](YiVTTw2Hi.lagda.md) 的证明原样写在原 F2 块 (`YiLegFold`) 与原主线闭项 `YiRWFold.twᶜ 2` 上: t₃, tN m, tω 的参照都不高于原塔第 2 项 (`tω≼tw2`, `tω≼tw2ᴿ`).
> 用处: 说明 "新塔第 2 项能证到 ψ₀(Ω_Ω+ψ₁(Ω_ω))" 不是比较表带来的差别, 原塔第 2 项此前记录的最高下界 `YiEVTw2.tA≼tw2ᴿ` 可以同样抬高. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTTw2HiOld where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; limcum≽)
open import OCF.Lean.YiLSTw1 using (h₁; εh; ρh)
open import OCF.Lean.YiT2Frame using (zc; rowβ; nzβ; ββ≼tw2)
open import OCF.Lean.YiEVTw2 using (BWc; okW; hiW)
open import OCF.Lean.YiEVReach using (_⇐_; ⇐r; ⇐l)
open import OCF.Lean.YiPHBase using (three)
open import OCF.Lean.YiPHEnd using (t₃; h₃; Lo³; reach³)
open import OCF.Lean.YiANFam using (fin)
open import OCF.Lean.YiANReach using (module Reach)
open import OCF.Lean.YiANEnd using (tN; nN₁; hN; module AtN; kid; one; I≡; ↑num; 0⊕)
open import OCF.Lean.YiANLim using (tω; nfω; lt; hΩω)
open import OCF.Lean.YiNFO using (mono<; ↓suc)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; l≼; ≼-refl; ≼-trans)
open import OCF.Lean.YiBRValue using (readRW; up≼)
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiBRTw using (twᶜ-R)
```

## 路径

`zc 1` 是 `next X`, X 的第 0 项是 `next 1`, `next 1` 的第 k 项是 k + 1 (`shape`, `refl`).

```agda
G : ℕ → LF
G k = kid (kid (kid (h₁ (zc 1)) 0) 0) k

shape : ∀ k → G k ≡ zero ⊕ ↑ zero (iter (one +_) one k)
shape k = refl

gk : ∀ k → G k ≡ fin (suc k)
gk k = trans (shape k) (trans (cong (λ x → zero ⊕ ↑ zero x) (I≡ k)) (trans (cong (zero ⊕_) (↑num (suc k))) (0⊕ (suc k))))

path₃ : three ⇐ h₁ (zc 1)
path₃ = ⇐l 0 (⇐l 0 (⇐l 2 ⇐r))

pathN : ∀ m → fin (suc (suc (suc m))) ⇐ h₁ (zc 1)
pathN m = ⇐l 0 (⇐l 0 (⇐l (suc (suc m)) (subst (fin (suc (suc (suc m))) ⇐_) (sym (gk (suc (suc m)))) ⇐r)))
```

## 塔第 2 项

```agda
row1≼tw2 : read (rowβ 1) ≼ read (twᶜ 2)
row1≼tw2 = ≼-trans (limcum≽ rowβ nzβ 1 (≼-refl _)) ββ≼tw2

t₃≼tw2 : (h : HC t₃) → R2.Rt h ≼ read (twᶜ 2)
t₃≼tw2 h = ≼-trans (reach³ path₃ (εh (zc 1)) (ρh (zc 1)) BWc okW hiW h) row1≼tw2

tN≼tw2 : ∀ m (h : HC (tN m)) → R2.Rt h ≼ read (twᶜ 2)
tN≼tw2 m h = ≼-trans (reachG (AtN.atN m) (pathN m) (εh (zc 1)) (ρh (zc 1)) BWc okW hiW h) row1≼tw2
  where open Reach (fin (suc (suc (suc m)))) (tN m)

tω≼tw2 : (h : HC tω) → R2.Rt h ≼ read (twᶜ 2)
tω≼tw2 (h0 ())
tω≼tw2 (h1 () _)
tω≼tw2 (hω e hs) = l≼ (λ n → ≼-trans (↓suc (mono< (nfω n) (nN₁ n) (hs n) (hN n) (lt n))) (tN≼tw2 n (hN n)))
```

## 搬到精简块的闭项

```agda
t₃≼tw2ᴿ : (h : HC t₃) → R2.Rt h ≼ readRW (RW.twᶜ 2)
t₃≼tw2ᴿ h = up≼ (twᶜ-R 2) (t₃≼tw2 h)

tω≼tw2ᴿ : (h : HC tω) → R2.Rt h ≼ readRW (RW.twᶜ 2)
tω≼tw2ᴿ h = up≼ (twᶜ-R 2) (tω≼tw2 h)

instω : R2.Rt hΩω ≼ readRW (RW.twᶜ 2)
instω = tω≼tw2ᴿ hΩω
```
