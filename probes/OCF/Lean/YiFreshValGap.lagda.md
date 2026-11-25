# 空白页的块: tw 1 这一站的缺口

> 验收文件. 编译定理: 后继层号上以自身为目标的折叠, 对右加的 Ω 树只是加法 (`self-add`, `self-Ω`, 任意底与层号); `G 2` 的形状 (`G2-form`, 第 1 层的链每步是 "自身折叠再 next"); `G (pt 1)` 的第 0 项就是 `G 2` (`h-pt1`, `G-pt1`); 参照 Ω₁·ω ≼ ψ₁(Ω₁) (`ref-mul`); `LOWER` 推出 ψ⁰(Ω₂) ≼ read (G (pt 1)) (`LOWER⇒Ω₂`); 第 1 层够得着参照 `lower-1 : ψ⁰(Ω₁) ≼ read (G 1)`. 有限测试: `z₂-1`.
> 判断 (纸面, 未经独立审核): 第 1 层的链点是 Ω₁·ω^k, `G 2` 约为 ψ₀(Ω₁·ω^ω) = ε_{ω^ω}, 参照的 ψ⁰(Ω₂) 是 BHO; 于是 [YiFreshValTw1](YiFreshValTw1.lagda.md) 的 `LOWER` 在 m = 1 不成立, `Tw1` 远低于 BTBO.
> 原因在自身目标上 `up` 原样保留 (孩子层的树不被折叠), 不在回退. 不否定路线: 没有编译的上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFreshValGap where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold
open import OCF.Lean.YiFreshValTw1 using (G; h₁; pt; κ; LOWER)
open import OCF.Lean.YiFreshValRead using (read; next≽; next≼; limcum≽)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼i; ≼l; l≼; ≼-refl; ≼-trans; ≅→≼; ⊑→≼; ψ⁰-mono⁰)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 自身目标的折叠是加法

参照里 ψ₁(x + Ω₁) 的分支是 ψ₁(x + u), 对 u 是乘法; 这里自身目标上的嵌入 `up` 原样保留, 所以加一个 Ω 树只多一个 Ω 树.

```agda
self-add : (a : LF) (B : Base (suc a)) (x : Tr (suc a)) →
  ψs (suc a) B (suc a) self (x + Ωt (suc a)) ≡ ψs (suc a) B (suc a) self x + Ωt (suc a)
self-add a B x = refl

self-Ω : (a : LF) (B : Base (suc a)) →
  ψs (suc a) B (suc a) self (Ωt (suc a)) ≡ bs B (suc a) self + Ωt (suc a)
self-Ω a B = refl
```

## `G 2` 与 `G (pt 1)`

```agda
one two : LF
one = suc zero
two = suc one

z₂ : ℕ → Tr one
z₂ = iter (λ c → next (ψs one (B₀ one) one self c)) zero

G2-form : G (suc (suc zero)) ≡ lim (cum (λ k → next (ψ⊥ one (B₀ one) (z₂ k))))
G2-form = refl

z₂-1 : z₂ 1 ≡ next (Ωt one)
z₂-1 = refl

hdL : LF → LF
hdL (lim g) = g 0
hdL a       = a

hdT : Tr zero → Tr zero
hdT (lim f) = f 0
hdT x       = x

h-pt1 : hdL (h₁ (pt 1)) ≡ two
h-pt1 = refl

G-pt1 : hdT (G (pt 1)) ≡ G (suc (suc zero))
G-pt1 = refl
```

## 参照一侧

```agda
Ω₁ : L.Ordᶜ (L.suc L.zero)
Ω₁ = L.Ω (L.suc L.zero)

ref-mul : L.lim (iterᴸ (Ω₁ L.+_) L.zero) ≼
  L.ψ {k = L.suc L.zero} {ℓ = L.suc (L.suc L.zero)} L.zero (λ r → L.suc r) Ω₁
ref-mul = ≼i (L.suc L.zero) (L.s≅ L.z≅) (≼-refl _)

two⊑κ1 : L.suc (L.suc L.zero) L.⊑ᴵ κ 1
two⊑κ1 = L.s⊑ (L.s≅ L.z≅) (L.lim 0 L.zero)

LOWER⇒Ω₂ : LOWER → L.ψ⁰ (L.Ω (L.suc (L.suc L.zero))) ≼ read (G (pt 1))
LOWER⇒Ω₂ low = ≼-trans (⊑→≼ _ (L.Ψ⁰-mono two⊑κ1)) (low 1)
```

## 对照: 第 1 层上够得着参照 (`lower-1`, 无前提)

第 0 层的树没有 `up`, 第 1 层的链不经过上面的加法; 参照的链从 Ω₀ = 1 起, 这里从 0 起, 差一步.

```agda
w₁ : ℕ → Tr zero
w₁ = iter (λ c → next (ψs zero (B₀ zero) zero self c)) zero

G1-form : G (suc zero) ≡ lim (cum (λ k → next (ψ⊥ zero (B₀ zero) (w₁ k))))
G1-form = refl

F⊥ : (x : Tr zero) → L.ψ⁰ (read x) ≼ read (ψ⊥ zero (B₀ zero) x)
F⊥ zero        = ≼-refl _
F⊥ (suc x)     = next≽ (ψ⊥ zero (B₀ zero) x) (F⊥ x)
F⊥ (lim f)     = l≼ (λ n → ≼l n (F⊥ (f n)))
F⊥ (Ω () _)
F⊥ (up _ () _)

Fs : (x : Tr zero) → L.ψ⁰ (read x) ≼ read (ψs zero (B₀ zero) zero self x)
Fs zero        = ≼-refl _
Fs (suc x)     = next≽ (ψs zero (B₀ zero) zero self x) (Fs x)
Fs (lim f)     = l≼ (λ n → ≼l n (Fs (f n)))
Fs (Ω () _)
Fs (up _ () _)

δ₁ : ℕ → L.Ordᶜ L.zero
δ₁ = iterᴸ (λ x → L.ψ {k = L.zero} {ℓ = L.suc L.zero} L.zero (λ r → L.suc r) x) (L.suc L.zero)

chain₁ : ∀ n → δ₁ n ≼ read (w₁ (suc n))
chain₁ zero    = next≼ (suc zero) (≼-refl _)
chain₁ (suc n) =
  ≼-trans (≅→≼ (L.≅-sym (L.ψ⁰≅ψ (L.≅-refl⁰ (δ₁ n)))))
  (≼-trans (ψ⁰-mono⁰ (chain₁ n))
  (next≼ (ψs zero (B₀ zero) zero self (w₁ (suc n))) (Fs (w₁ (suc n)))))

lower-1 : L.ψ⁰ (L.Ω (L.suc L.zero)) ≼ read (G (suc zero))
lower-1 = l≼ (λ n → limcum≽ (λ k → next (ψ⊥ zero (B₀ zero) (w₁ k))) (suc n)
  (≼-trans (ψ⁰-mono⁰ (chain₁ n)) (next≼ (ψ⊥ zero (B₀ zero) (w₁ (suc n))) (F⊥ (w₁ (suc n))))))
```
