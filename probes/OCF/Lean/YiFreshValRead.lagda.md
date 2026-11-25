# 空白页的块: 第 0 层的读回

> 验收文件. 编译定理: 空白页第 0 层的树 (只有零, 后继, ℕ 极限) 读成参照框架的第 0 层树 `read`; 加法, `ι`, `next`, `cum` 的读回与值序的基本性质; 合法树的读回有证书 `HS`.
> 不否定什么, 不涉及上界. 用在 [YiFreshValTw1](YiFreshValTw1.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFreshValRead where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t; Leg)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ≼-+ʳ; +-mono)
import OCF.Align.RR4MonoFragment as MF
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 读回

```agda
T₀ : Set
T₀ = L.Ordᶜ L.zero

read : Tr zero → T₀
read zero        = L.zero
read (suc x)     = L.suc (read x)
read (lim f)     = L.lim (λ n → read (f n))
read (Ω () _)
read (up _ () _)

read-+ : (x y : Tr zero) → read (x + y) L.≅ (read x L.+ read y)
read-+ x zero        = L.≅-refl⁰ (read x)
read-+ x (suc y)     = L.s≅ (read-+ x y)
read-+ x (lim f)     = L.l≅ (λ n → read-+ x (f n))
read-+ x (Ω () _)
read-+ x (up _ () _)

read-ι : (x : Tr zero) → read (ι zero x) L.≅ read x
read-ι zero        = L.z≅
read-ι (suc x)     = L.s≅ (read-ι x)
read-ι (lim f)     = L.l≅ (λ n → read-ι (f n))
read-ι (Ω () _)
read-ι (up _ () _)
```

## 值序

```agda
plus≽ : (a : Tr zero) {y : T₀} (b : Tr zero) → y ≼ read b → y ≼ read (a + b)
plus≽ a b q = ≼-trans q (≼-trans (MF.≼-+ˡ (read a) (read b)) (≅→≼ (L.≅-sym (read-+ a b))))

plus≼ : (a : Tr zero) {y : T₀} (b : Tr zero) → y ≼ read a → y ≼ read (a + b)
plus≼ a b q = ≼-trans q (≼-trans (≼-+ʳ (read a) (read b)) (≅→≼ (L.≅-sym (read-+ a b))))

ι≽ : {y : T₀} (x : Tr zero) → y ≼ read x → y ≼ read (ι zero x)
ι≽ x q = ≼-trans q (≅→≼ (L.≅-sym (read-ι x)))

cum≽ : (F : ℕ → Tr zero) (n : ℕ) {y : T₀} → y ≼ read (F n) → y ≼ read (cum F n)
cum≽ F zero    q = q
cum≽ F (suc n) q = plus≽ (cum F n) (F (suc n)) q

limcum≽ : (F : ℕ → Tr zero) (n : ℕ) {y : T₀} → y ≼ read (F n) → y ≼ read (lim (cum F))
limcum≽ F n q = ≼l n (cum≽ F n q)

next≽ : (b : Tr zero) {Y : T₀} → Y ≼ read b → L.lim (iterᴸ (Y L.+_) L.zero) ≼ read (next b)
next≽ b {Y} q = l≼ λ where
    zero    → z≼
    (suc n) → ≼l n (go n)
  where
  go : ∀ n → iterᴸ (Y L.+_) L.zero (suc n) ≼ read (iter (b +_) b n)
  go zero    = q
  go (suc n) = ≼-trans (+-mono q (go n)) (≅→≼ (L.≅-sym (read-+ b (iter (b +_) b n))))

next≼ : (b : Tr zero) {y : T₀} → y ≼ read b → y ≼ read (next b)
next≼ b q = ≼l 0 q
```

## 合法树的读回有证书

第一位置序在第 0 层给出前驱包含, 由此合法树的读回 `HS`.

```agda
◃⊑ : {x y : Tr zero} → zero ⊢ x ◃ y → read x L.⊑ read y
◃⊑ ◃s       h = L.≺s h
◃⊑ (◃l n)   h = L.≺l n h
◃⊑ (◃w {p = ()})
◃⊑ (◃u {c = ()} _)
◃⊑ (◃c {c = ()} _)
◃⊑ (◃t d e) h = ◃⊑ e (◃⊑ d h)

HS-read : (x : Tr zero) → Leg zero x → L.HS (read x)
HS-read zero        h = L.hz
HS-read (suc x)     h = L.hs (HS-read x h)
HS-read (lim f) (hf , adj) = L.hl (λ n → HS-read (f n) (hf n)) (λ n → ◃⊑ (adj n))
HS-read (Ω () _)    h
HS-read (up _ () _) h
```
