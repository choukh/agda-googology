# 空白页的块: tw 1 这一站与 BTBO

> 验收文件. 站定在 `Tw1 = ψ₀ (tw 1) (Ωt (tw 1))` (k = 0). `Tw1-form` (`refl`): 它是 `G (pt n)` 的部分和的极限, 链 `pt (m+1) = 1 + G (pt m)`, `G x` 是层号 `tw 0 ⊕ ↑x` 上的 ψ₀(Ω).
> 条件定理 `btbo-tw1 : LOWER → V3F → D.BTBOᴵ ≼ read Tw1`. 两条前提只在链点上陈述, m = 0 处是定理 (`LOWER-0`, `V3F-0`); 链与 `YiBtboLower` 同形 (值序不变量, `V1`, `V2′`, 平移).
> 判断 (纸面, 见 [YiFreshValGap](YiFreshValGap.lagda.md)): `LOWER` 在 m = 1 不成立, 这条条件定理很可能是空的. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFreshValTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold
open import OCF.Lean.YiFreshLegal using (Leg; +-leg; ι-leg; ψ₀-leg; Ωt-leg)
open import OCF.Lean.YiFreshValRead

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ⊑→≼; ≼l; l≼)
open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open S using (ordᴰ)
open S using () renaming (iter to iterᴸ)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOFullEb using (module Blocks)
open import OCF.Align.BTBOFullV3 using (𝕋₀; bkᴵ)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
open import OCF.Align.BTBOFullLv using (SV-L)
open import OCF.Align.BTBOFull using (St-bk; bk≅γ)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-∘)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.NoCumsum as N
open import OCF.Lean.YiBtboV2 using (Mono; mz; ms; ml; V2′)
import OCF.Lean.YiPEStep as PS

module WT = Blocks 𝕋₀
```

## 1 这一站的形状

`h₁ c` 是 `tw 1` 的分支 c 的层号, `G x` 是那一层上的 ψ₀(Ω). 第 0 层的偏移折叠就是 `B₀`, 所以分支上的折叠恰是 `G`.

```agda
h₁ : Tr zero → LF
h₁ c = tw 0 ⊕ ↑ (tw 0) c

G : Tr zero → Tr zero
G x = ψ₀ (h₁ x) (Ωt (h₁ x))

st : Tr zero → Tr zero
st x = suc zero + ι zero (G x)

pt : ℕ → Tr zero
pt = iter st zero

Tw1 : Tr zero
Tw1 = ψ₀ (tw 1) (Ωt (tw 1))

Tw1-form : Tw1 ≡ lim (cum (λ n → G (pt n)))
Tw1-form = refl

G-leg : (x : Tr zero) → Leg zero (G x)
G-leg x = ψ₀-leg (h₁ x) (Ωt (h₁ x)) (Ωt-leg (h₁ x))

st-leg : (x : Tr zero) → Leg zero (st x)
st-leg x = +-leg (suc zero) (ι zero (G x)) tt (ι-leg zero (G x) (G-leg x))

pt-leg : ∀ m → Leg zero (pt m)
pt-leg zero    = tt
pt-leg (suc m) = st-leg (pt m)

lvl : (x : Tr zero) → Leg zero x → L.Ordᴵ
lvl x l = L.toLevel (read x) (HS-read x l)

κ : ℕ → L.Ordᴵ
κ m = lvl (pt m) (pt-leg m)
```

## 2 抄成 src 的第 0 层树

```agda
cp : Tr zero → S.Ord₀
cp zero        = S.zero
cp (suc a)     = S.suc (cp a)
cp (lim f)     = S.lim (λ n → cp (f n))
cp (Ω () _)
cp (up _ () _)

cp≅ : (x : Tr zero) → tr₀ (cp x) L.≅ read x
cp≅ zero        = L.z≅
cp≅ (suc a)     = L.s≅ (cp≅ a)
cp≅ (lim f)     = L.l≅ (λ n → cp≅ (f n))
cp≅ (Ω () _)
cp≅ (up _ () _)

Mono-cp : (x : Tr zero) → Leg zero x → Mono (tr₀ (cp x))
Mono-cp zero        l = mz
Mono-cp (suc a)     l = ms (Mono-cp a l)
Mono-cp (lim f) (hf , adj) = ml (λ n → Mono-cp (f n) (hf n))
  (λ n → ≼-trans (≅→≼ (cp≅ (f n)))
    (≼-trans (⊑→≼ (read (f n)) (◃⊑ (adj n))) (≅→≼ (L.≅-sym (cp≅ (f (suc n)))))))
Mono-cp (Ω () _)    l
Mono-cp (up _ () _) l
```

## 3 两条前提

`LOWER`: 链点的层号上, 空白页的 ψ₀(Ω) 不低于参照的 ψ⁰(Ω). `V3F`: 链点的累加规范化层号嵌进空白页折叠值的字面前驱 (`YiBtboLower.V3m` 的空白页版).

```agda
LOWER : Set
LOWER = ∀ m → L.ψ⁰ (L.Ω (κ m)) ≼ read (G (pt m))

V3F : Set
V3F = ∀ m → WT.Eb (ordᴰ (cp (pt m))) (read (G (pt m)))

LOWER-0 : L.ψ⁰ (L.Ω (κ 0)) ≼ read (G (pt 0))
LOWER-0 = next≽ (suc zero) (≼-refl (L.suc L.zero))

V3F-0 : WT.Eb (ordᴰ (cp (pt 0))) (read (G (pt 0)))
V3F-0 = WT.Eb-zero
```

## 4 平移: 折叠值的层号嵌进下一个链点的层号

```agda
shift : ∀ x (l : Leg zero x) →
  PEmb (L.toLevel (read (G x)) (HS-read (G x) (G-leg x))) (lvl (st x) (st-leg x))
shift x l =
  PS.PEmb-≅ʳ (PS.PEmb-≅ʳ (PS.PEmb-shift (L.toLevel one h1) (L.toLevel (read (G x)) hG))
    (L.≅ᴵ-sym (PS.toLevel-+ one (read (G x)) h1 hG hsum)))
    (L.toLevel-≅ hsum (HS-read (st x) (st-leg x)) (L.≅-sym e))
  where
  one : T₀
  one = L.suc L.zero
  h1 : L.HS one
  h1 = L.hs L.hz
  hG : L.HS (read (G x))
  hG = HS-read (G x) (G-leg x)
  e : read (st x) L.≅ (one L.+ read (G x))
  e = L.≅-trans (read-+ (suc zero) (ι zero (G x))) (L.add-≅ (L.≅-refl⁰ one) (read-ι (G x)))
  hsum : L.HS (one L.+ read (G x))
  hsum = PS.HS-≅ (HS-read (st x) (st-leg x)) e
```

## 5 链与下界 (条件定理)

```agda
module Chain (low : LOWER) (v3 : V3F) where
  emb : ∀ n m → D.γ n ≼ read (pt m) → PEmb (D.L n) (κ (suc m))
  emb n m w =
    PEmb-∘ (PW₃ (V1 (SV-L n)))
    (PEmb-∘ (PW₁ (V2′ (bkᴵ (N.L n)) (cp η) (St-bk (SV-L n)) (Mono-cp η l) w′))
    (PEmb-∘ (PW₂ (HS-read (G η) (G-leg η)) (v3 m))
            (shift η l)))
    where
    η = pt m
    l = pt-leg m
    w′ : tr₀ (bkᴵ (N.L n)) ≼ tr₀ (cp η)
    w′ = ≼-trans (≅→≼ (bk≅γ n)) (≼-trans w (≅→≼ (L.≅-sym (cp≅ η))))

  lowc : ∀ k → L.ψ⁰ (L.Ω (κ k)) ≼ read (pt (suc k))
  lowc k = plus≽ (suc zero) (ι zero (G (pt k))) (ι≽ (G (pt k)) (low k))

  chainV : ∀ n → Σ ℕ (λ m → D.γ n ≼ read (pt m))
  chainV zero    = 1 , plus≼ (suc zero) (ι zero (G zero)) (≼-refl (L.suc L.zero))
  chainV (suc n) = suc (suc m) , ≼-trans (Ψ-emb (emb n m w)) (lowc (suc m))
    where
    m = proj₁ (chainV n)
    w = proj₂ (chainV n)

  btbo : D.BTBOᴵ ≼ read Tw1
  btbo = l≼ (λ n → ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n))))
    (limcum≽ (λ k → G (pt k)) (suc (proj₁ (chainV n))) (low (suc (proj₁ (chainV n))))))

btbo-tw1 : LOWER → V3F → D.BTBOᴵ ≼ read Tw1
btbo-tw1 low v3 = Chain.btbo low v3
```
