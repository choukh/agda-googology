# 终点 `EBOᶜ` 不低于 BTBO (无前提, 不经 Into) (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiEBBtbo` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTEBBtbo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here; emb)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiVTLSFold using (OKB; ok-B₀; lower)
open import OCF.Lean.YiVTLSTw1 using (h₁; εh; ρh; wh; nl-↑; corr-↑; lvl; E; ez; es; E-next; E→≅; eq0; LiftP-∙)
open import OCF.Lean.YiVTLSBtbo using (cp; cp≅; Mono-cp; V3)
open import OCF.Lean.YiVTEBShape using (dB; Fn; br≼; ok-dB; transferP)

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

btbo-B₀ : D.BTBOᴵ ≼ read (twᶜ 1)
btbo-B₀ = Btbo.btbo-B (B₀ (tw 1)) (ok-B₀ (tw 1)) (es ez)
```
