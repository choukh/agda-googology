# 新塔第 2 项的更高下界: ψ₀(Ω_Ω+ψ₁(Ω_ω)) 的参照

> 验收文件 (读记号), 不进成品. 编译定理, 无前提 (新写): 在带表的 F2 对照块上, `β + β` 的第 1 行的底 `BWc` (`YiVTEVTw2`) 沿孩子 0, 0, 2 走到层号 3, 沿孩子 0, 0, m+2 走到 `fin (m+3)`; 用 `YiVTPHEnd.reach³` 与 `YiVTANReach.reachG` 得 t₃, tN m, 再取上确界得 tω 都不高于塔第 2 项 (`tω≼tw2`), 经 `YiVTTw.twᶻ-R` 搬到新主线 (`tω≼twᶻ2`, `tω≼twᶻ`).
> 原主线在同一处的同文证明见 [YiVTTw2HiOld](YiVTTw2HiOld.lagda.md) (原 F2 上也成立), 所以这不是新旧两个闭项之间的差别. 不涉及上界; 没有比较 `twᶻ 2` 与原塔第 2 项.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTTw2Hi where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead using (read; limcum≽)
open import OCF.Lean.YiVTLSTw1 using (h₁; εh; ρh)
open import OCF.Lean.YiVTT2Frame using (zc; rowβ; nzβ; ββ≼tw2)
open import OCF.Lean.YiVTEVTw2 using (BWc; okW; hiW)
open import OCF.Lean.YiVTEVReach using (_⇐_; ⇐r; ⇐l)
open import OCF.Lean.YiVTPHBase using (three)
open import OCF.Lean.YiVTPHEnd using (t₃; h₃; Lo³; reach³)
open import OCF.Lean.YiVTANFam using (fin)
open import OCF.Lean.YiVTANReach using (module Reach)
open import OCF.Lean.YiVTANEnd using (tN; nN₁; hN; module AtN; kid; one; I≡; ↑num; 0⊕)
open import OCF.Lean.YiVTANLim using (tω; nfω; lt; hΩω)
open import OCF.Lean.YiNFO using (mono<; ↓suc)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; l≼; ≼-refl; ≼-trans)
open import OCF.Lean.YiBRValue using (readRW; up≼)
open import OCF.Lean.YiMTTab using (twᶻ)
open import OCF.Lean.YiVTTw using (twᶻ-R)
open import OCF.Lean.YiMTKeel using (tw≼ᶻ)
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
t₃≼twᶻ2 : (h : HC t₃) → R2.Rt h ≼ readRW (twᶻ 2)
t₃≼twᶻ2 h = up≼ (twᶻ-R 2) (t₃≼tw2 h)

tω≼twᶻ2 : (h : HC tω) → R2.Rt h ≼ readRW (twᶻ 2)
tω≼twᶻ2 h = up≼ (twᶻ-R 2) (tω≼tw2 h)

tω≼twᶻ : (n : ℕ) (h : HC tω) → R2.Rt h ≼ readRW (twᶻ (suc (suc n)))
tω≼twᶻ zero    h = tω≼twᶻ2 h
tω≼twᶻ (suc n) h = ≼-trans (tω≼twᶻ n h) (tw≼ᶻ (suc (suc n)))

inst₃ : R2.Rt h₃ ≼ readRW (twᶻ 2)
inst₃ = t₃≼twᶻ2 h₃

instω : R2.Rt hΩω ≼ readRW (twᶻ 2)
instω = tω≼twᶻ2 hΩω
```
