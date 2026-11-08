# 原全底与全塔合法化的分支覆盖

使用构造侧冻结的 `legS/legT`，没有复制合法化。每种类的原坐标
沿其起源 step 变成后继；其合法性是在该真正低层种类结构上表达的。
全部 raw 树的覆盖与低层合法坐标的保持均统一于 n 与塔高度 m。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRichLegValueRun where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb; FX)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL)
open import OCF.Lean.ThirdRichLegIf
open import OCF.Lean.ThirdRichLegBuild
open import OCF.Lean.ThirdRichLegValueIf
open import OCF.Lean.ThirdRichLegValueTheta using (module Capture)
import OCF.Lean.Fold1If as V

bumpS : ∀ n κ → E (Sb n) κ → E (Sb n) κ
bumpT : ∀ n m κ → E (Tw (Sb n) m) κ → E (Tw (Sb n) m) κ
bumpS zero () d
bumpS (suc n) (inj₁ _ , inj₂ _) d = hs d
bumpS (suc n) (inj₁ _ , inj₁ κ) d = bumpS n κ d
bumpS (suc n) (inj₂ e , κ) d = bumpT n (hs e) κ d
bumpT n hz κ d = bumpS n κ d
bumpT n (hs m) (inj₂ _) d = hs d
bumpT n (hs m) (inj₁ κ) d = bumpT n m κ d
bumpT n (hl f) (i , κ) d = bumpT n (f i) κ d
bumpT n (hΩ κ₀ h) (e , κ) d = bumpT n (h e) κ d

LegalS : ∀ n κ → E (Sb n) κ → Set
LegalT : ∀ n m κ → E (Tw (Sb n) m) κ → Set
LegalS zero () d
LegalS (suc n) (inj₁ _ , inj₂ _) d = LgB d
LegalS (suc n) (inj₁ _ , inj₁ κ) d = LegalS n κ d
LegalS (suc n) (inj₂ e , κ) d = LegalT n (hs e) κ d
LegalT n hz κ d = LegalS n κ d
LegalT n (hs m) (inj₂ _) d = LgB d
LegalT n (hs m) (inj₁ κ) d = LegalT n m κ d
LegalT n (hl f) (i , κ) d = LegalT n (f i) κ d
LegalT n (hΩ κ₀ h) (e , κ) d = LegalT n (h e) κ d

bumpS-legal : ∀ n κ d → LegalS n κ d → LegalS n κ (bumpS n κ d)
bumpT-legal : ∀ n m κ d → LegalT n m κ d → LegalT n m κ (bumpT n m κ d)
bumpS-legal zero () d l
bumpS-legal (suc n) (inj₁ _ , inj₂ _) d l = l
bumpS-legal (suc n) (inj₁ _ , inj₁ κ) d l = bumpS-legal n κ d l
bumpS-legal (suc n) (inj₂ e , κ) d l = bumpT-legal n (hs e) κ d l
bumpT-legal n hz κ d l = bumpS-legal n κ d l
bumpT-legal n (hs m) (inj₂ _) d l = l
bumpT-legal n (hs m) (inj₁ κ) d l = bumpT-legal n m κ d l
bumpT-legal n (hl f) (i , κ) d l = bumpT-legal n (f i) κ d l
bumpT-legal n (hΩ κ₀ h) (e , κ) d l = bumpT-legal n (h e) κ d l

module _ {T : KS} where
  captureS : ∀ n (c : Ctx T (Sb n)) κ g d → g d ≼ʳ θS n c κ g (bumpS n κ d)
  captureT : ∀ n m (c : Ctx T (Tw (Sb n) m)) κ g d → g d ≼ʳ θT n m c κ g (bumpT n m κ d)
  captureS zero c () g d
  captureS (suc n) c (inj₁ _ , inj₂ _) g d = Capture.branch (viaL {F = FX (Sb n)} c (inj₁ tt)) g d
  captureS (suc n) c (inj₁ _ , inj₁ κ) g d = captureS n (viaS (viaL {F = FX (Sb n)} c (inj₁ tt))) κ g d
  captureS (suc n) c (inj₂ e , κ) g d = captureT n (hs e) (viaL {F = FX (Sb n)} c (inj₂ e)) κ g d
  captureT n hz c κ g d = captureS n c κ g d
  captureT n (hs m) c (inj₂ _) g d = Capture.branch c g d
  captureT n (hs m) c (inj₁ κ) g d = captureT n m (viaS c) κ g d
  captureT n (hl f) c (i , κ) g d = captureT n (f i) (viaL c i) κ g d
  captureT n (hΩ κ₀ h) c (e , κ) g d = captureT n (h e) (viaL c e) κ g d

module CompleteCover {S : KS} (A : AllKinds S)
  (capture : ∀ κ g d → Σ (E S κ) (λ e → g d ≼ʳ AllKinds.θK A here κ g e)) where
  open Complete A

  partial-cover : ∀ f n → f n ≼ʳ partial f n
  partial-cover f zero = reflʳ (f zero)
  partial-cover f (suc n) = right (partial f n) (f (suc n))

  inflate : ∀ a → a ≼ʳ leg a
  inflate hz = rz
  inflate (hs a) = rs (inflate a)
  inflate (hl f) = rl (λ n → ri n (rt (inflate (f n)) (partial-cover (λ j → leg (f j)) n)))
  inflate (hΩ κ g) = ro (λ d → go d (capture κ (λ e → leg (g e)) d)) where
    go : ∀ d → Σ (E S κ) (λ e → leg (g d) ≼ʳ AllKinds.θK A here κ (λ x → leg (g x)) e) →
      Σ (E S κ) (λ e → g d ≼ʳ AllKinds.θK A here κ (λ x → leg (g x)) e)
    go d (e , p) = e , rt (inflate (g d)) p

inflateS : ∀ n a → a ≼ʳ legS n a
inflateS n = CompleteCover.inflate (allS n) (λ κ g d → bumpS n κ d , captureS n here κ g d)

inflateT : ∀ n m a → a ≼ʳ legT n m a
inflateT n m = CompleteCover.inflate (allT n m) (λ κ g d → bumpT n m κ d , captureT n m here κ g d)

zero-inflate : ∀ (a : Cd) → a V.≤ᵛ legS zero a
zero-inflate a = zero-sound (inflateS zero a)
```

没有任何输入合法前提，因此也覆盖原全部地板与所有 raw 分支函数。
`bumpS-legal/bumpT-legal` 明确给出实际选取坐标的低层合法性保持，
但不保持某个给定世界的可入界。高层结论是全 raw 分支的树值覆盖，
尚非旧 `Φ/ΦX` 的输出比较，亦不是新的具名序数强度。
