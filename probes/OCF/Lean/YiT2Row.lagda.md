# 塔第 2 项 (四): 行对孩子下标的单调, 陈述与已证的一段

> 验收文件. 判决: 陈述 `RowMono` (塔第 n+1 项里, 孩子下标沿第一位置序走一步, 行的值不降) 没有证, 也没有否定; 它只对塔的规范行 (标准底, 塔自带的证据与路线) 陈述, 不对一切底 (后者被 `YiLPNoBM.no-bm-all` 否定).
> 编译定理, 无前提: `row≽` (孩子下标取零的那一行, 即塔第 n 项, 不高于每一行), 由 `YiT2Desc.desc` 沿 `lift¹` 得出; 沿路取出的证据与路线等于塔第 n 项的 (`ev-lift`, `rt-lift`).
> 不给出什么: 起点不是零的一步没有证. 判断: `◃l (suc n)` 与非零分支的一步要 "孩子的底换成标准底值不升", 这里没有.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiT2Row where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiT2Desc using (_⊑¹_; ev¹; rt¹; lift¹; desc)
open import OCF.Align.Value using (_≼_)
```

## 行与陈述

```agda
lev : (n : ℕ) → Tr (tw n) → L
lev n c = tw n ⊕ ↑ (tw n) c

rowAt : (n : ℕ) → Tr (tw n) → Tr zero
rowAt n c = ψ₀ (lev n c) (proj₂ (proj₂ (Ev-tw (suc n)) c)) (proj₂ (Rt-tw (suc n)) c) (Ωt (lev n c))

RowMono : ℕ → Set
RowMono n = {c c′ : Tr (tw n)} → tw n ⊢ c ◃ c′ → read (rowAt n c) ≼ read (rowAt n c′)
```

## 已证的一段: 起点是零

```agda
ev-lift : (a b : L) (ea : Ev a) (eb : EvO a b) → ev¹ (lift¹ a b) (Ev⊕ a b ea eb) ≡ ea
ev-lift a zero     ea eb = refl
ev-lift a (suc b)  ea eb = ev-lift a b ea eb
ev-lift a (lim g)  ea eb = ev-lift a (g zero) ea (eb zero)
ev-lift a (Ωₗ k h) ea (v , ek , eb) = ev-lift a (h zero) ea (eb zero)

rt-lift : (a b : L) (ra : Rt a) (rb : RtP b) → rt¹ (lift¹ a b) (Rt⊕ a b ra rb) ≡ ra
rt-lift a zero     ra rb        = refl
rt-lift a (suc b)  ra rb        = rt-lift a b ra rb
rt-lift a (lim g)  ra (rb , R)  = rt-lift a (g zero) ra (rb zero)
rt-lift a (Ωₗ k h) ra (rk , rb) = rt-lift a (h zero) ra (rb zero)

row≽ : (n : ℕ) (c : Tr (tw n)) → read (twᶜ n) ≼ read (rowAt n c)
row≽ n c =
  subst₂ (λ e r → read (ψ₀ (tw n) e r (Ωt (tw n))) ≼ read (rowAt n c))
    (ev-lift (tw n) (↑ (tw n) c) (Ev-tw n) (EvO↑ (tw n) (tw n) (Ev-tw n) self c))
    (rt-lift (tw n) (↑ (tw n) c) (Rt-tw n) (RtP↑ (tw n) (Rt-tw n) c))
    (desc (lift¹ (tw n) (↑ (tw n) c)) (proj₂ (proj₂ (Ev-tw (suc n)) c)) (proj₂ (Rt-tw (suc n)) c))
```
