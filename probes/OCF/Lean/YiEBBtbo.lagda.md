# 终点 `EBOᶜ` 不低于 BTBO (无前提, 不经 Into)

> 验收文件. 编译定理, 无前提: `btbo-EBO : D.BTBOᴵ ≼ read EBOᶜ`, 由第 1 支直接得出.
> 一般底: `btbo-B` 对层号 `tw 1` 上满足 `OKB` 且满足起点条件 `Start B` (Ω 结点链的起点 `bs B zero (ink self)` 与底 `b⊥ B` 逐点同形, `E`) 的一切底, 链点 `pt`, `form`, `LOWER`, `V3F`, `KG` 都对这个底陈述; 第 1 支的底满足两条 (`ok-dB 1`, `start-dB1`). 只有 `KG` 用到起点条件.
> 不否定什么, 不涉及上界. 各支的形状在 [YiEBShape](YiEBShape.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEBBtbo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here; emb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLSFold using (OKB; ok-B₀; lower)
open import OCF.Lean.YiLSTw1 using (h₁; εh; ρh; wh; nl-↑; corr-↑; lvl; E; ez; es; E-next; E→≅; eq0; LiftP-∙)
open import OCF.Lean.YiLSBtbo using (cp; cp≅; Mono-cp; V3)
open import OCF.Lean.YiEBShape using (dB; Fn; br≼; ok-dB; transferP)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼)
open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open S using (ordᴰ)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOFullEb using (module Blocks)
open import OCF.Align.BTBOFullV3 using (𝕋₀; bkᴵ)
open import OCF.Align.BTBOFullV1 using (V1; PW₁; PW₂; PW₃)
open import OCF.Align.BTBOFullLv using (SV-L)
open import OCF.Align.BTBOFull using (St-bk; bk≅γ)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-∘; PEmb-⊑)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.NoCumsum as N
open import OCF.Lean.YiBtboV2 using (V2′)
import OCF.Lean.YiPEStep as PS

module WT = Blocks 𝕋₀
```

## 一般底上的链点

`Bc B x`: 第 x 个孩子的底, 它的分量就是 B 的分量 (`b⊥`, 以及 `bs B j (inb x w)`).

```agda
Start : Base (tw 1) → Set
Start B = E (bs B zero (ink self)) (b⊥ B)

module Chain (B : Base (tw 1)) where
  β : Tr zero
  β = bs B zero (ink self)
  nβ : zero ⊢ zero ◃ β
  nβ = ns B zero (ink self)

  Bc : (x : Tr zero) → Base (h₁ x)
  Bc x = dW zero h₁ (Ev-tw 1) (Rt-tw 1) B x zero

  G : Tr zero → Tr zero
  G x = ψ⊥ (h₁ x) (εh x) (ρh x) (Bc x) (Ωt (h₁ x))

  G-nz : (x : Tr zero) → zero ⊢ zero ◃ G x
  G-nz x = nz⊥ (h₁ x) (εh x) (ρh x) (Bc x) (Ωt (h₁ x))

  K : Tr zero → Tr zero
  K x = ψs (h₁ x) (εh x) (ρh x) (Bc x) zero (wh x) β nβ (Ωt (h₁ x))

  pt : ℕ → Tr zero
  pt = iter K zero

  form : Fn 1 B ≡ limc (λ n → G (pt n)) (λ n → G-nz (pt n))
  form = refl
```

## `LOWER`, `V3F`, `KG` 对一般底

```agda
module Lemmas (B : Base (tw 1)) (ok : OKB (tw 1) B) where
  open Chain B

  okc : (x : Tr zero) → OKB (h₁ x) (Bc x)
  okc x = proj₁ ok , λ j w → proj₂ ok j (inb x w)

  κ : ℕ → L.Ordᴵ
  κ m = lvl (pt m)

  LOWER : ∀ m → L.ψ⁰ (L.Ω (κ m)) ≼ read (G (pt m))
  LOWER m = lower (nl-↑ (pt m)) (εh (pt m)) (ρh (pt m)) (Bc (pt m)) (okc (pt m)) (corr-↑ (pt m) (HSr (pt m)))

  V3F : ∀ m → WT.Eb (ordᴰ (cp (pt m))) (read (G (pt m)))
  V3F m = proj₁ (V3 (pt m) (εh (pt m)) (ρh (pt m)) (Bc (pt m)) (λ j w → proj₂ ok j (inb (pt m) w)))

  pt1 : L.suc L.zero ≼ read (pt 1)
  pt1 = ≼l 0 (⊴→≼ (proj₂ ok zero (ink self)))

module Btbo (B : Base (tw 1)) (ok : OKB (tw 1) B) (st : Start B) where
  open Chain B
  open Lemmas B ok

  KG : (x : Tr zero) → read (K x) L.≅ read (G x)
  KG x = E→≅ (eq0 (h₁ x) (εh x) (ρh x) (Bc x) (wh x) (LiftP-∙ zero (↑ zero x) self tt) β nβ st (Ωt (h₁ x)))

  shift : ∀ x → PEmb (L.toLevel (read (G x)) (HSr (G x))) (lvl (K x))
  shift x = PS.PEmb-≅ʳ (PEmb-⊑ L.⊑ᴵ-refl)
    (L.toLevel-≅ (HSr (G x)) (HSr (K x)) (L.≅-sym (KG x)))

  emb : ∀ n m → D.γ n ≼ read (pt m) → PEmb (D.L n) (κ (suc m))
  emb n m w =
    PEmb-∘ (PW₃ (V1 (SV-L n)))
    (PEmb-∘ (PW₁ (V2′ (bkᴵ (N.L n)) (cp η) (St-bk (SV-L n)) (Mono-cp η) w′))
    (PEmb-∘ (PW₂ (HSr (G η)) (V3F m))
            (shift η)))
    where
    η = pt m
    w′ : tr₀ (bkᴵ (N.L n)) ≼ tr₀ (cp η)
    w′ = ≼-trans (≅→≼ (bk≅γ n)) (≼-trans w (≅→≼ (L.≅-sym (cp≅ η))))

  lowc : ∀ k → L.ψ⁰ (L.Ω (κ k)) ≼ read (pt (suc k))
  lowc k = ≼-trans (LOWER k) (≅→≼ (L.≅-sym (KG (pt k))))

  chainV : ∀ n → Σ ℕ (λ m → D.γ n ≼ read (pt m))
  chainV zero    = 1 , pt1
  chainV (suc n) = suc (suc (proj₁ (chainV n))) ,
    ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n)))) (lowc (suc (proj₁ (chainV n))))

  btbo-B : D.BTBOᴵ ≼ read (Fn 1 B)
  btbo-B = l≼ (λ n → ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n))))
    (limcum≽ (λ k → G (pt k)) (λ k → G-nz (pt k)) (suc (proj₁ (chainV n))) (LOWER (suc (proj₁ (chainV n))))))
```

## 第 1 支

第 1 支的底: Ω 结点链的起点与底都是 `next (suc zero)` (`start-dB1`, 对照 `YiLPInto.chain-B₁`).

```agda
start-dB1 : Start (dB 1)
start-dB1 = E-next (es ez)

start-dB1≡ : bs (dB 1) zero (ink self) ≡ b⊥ (dB 1)
start-dB1≡ = refl

btbo-dB1 : D.BTBOᴵ ≼ read (Fn 1 (dB 1))
btbo-dB1 = Btbo.btbo-B (dB 1) (ok-dB 1) start-dB1

btbo-EBO : D.BTBOᴵ ≼ read EBOᶜ
btbo-EBO = ≼-trans btbo-dB1 (br≼ 1)

btbo-EBO′ : D.BTBOᴵ ≼ read EBOᶜ
btbo-EBO′ = transferP D.BTBOᴵ 1 Start start-dB1 (λ B ok st → Btbo.btbo-B B ok st)
```

对照: 标准底是这里的一个实例, 重新得出 `YiLSBtbo.btbo-tw1` 的陈述.

```agda
btbo-B₀ : D.BTBOᴵ ≼ read (twᶜ 1)
btbo-B₀ = Btbo.btbo-B (B₀ (tw 1)) (ok-B₀ (tw 1)) (es ez)
```
