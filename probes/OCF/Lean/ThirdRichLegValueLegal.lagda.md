# 只量化合法低层坐标的实际覆盖

本篇重新证明合法坐标域上的覆盖，不从 raw 共尾关系偷换量词。
Ω 左分支只量化该种类起源 step 的合法低层树；右侧选择的实际
坐标仍是 `bump`，其合法性由已证 `bump-legal` 给出。此域不等于
某一个世界的界内坐标，故仍不声明原动态折叠保持这个关系。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ThirdRichLegValueLegal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb; FX)
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL)
open import OCF.Lean.ThirdRichLegIf
open import OCF.Lean.ThirdRichLegBuild
open import OCF.Lean.ThirdRichLegValueRun using (LegalS; LegalT; bumpS; bumpT; bumpS-legal; bumpT-legal)
import OCF.Lean.Fold1If as V
open import OCF.Lean.NegFold1Base using (≤ᵛ-trans)

module Domain (S : KS) (P : ∀ κ → E S κ → Set) where
  data Cover : HB S → HB S → Set where
    cz : ∀ {b} → Cover hz b
    cs : ∀ {a b} → Cover a b → Cover (hs a) (hs b)
    cr : ∀ {a b} → Cover a b → Cover a (hs b)
    cl : ∀ {f b} → (∀ n → Cover (f n) b) → Cover (hl f) b
    ci : ∀ {a f} n → Cover a (f n) → Cover a (hl f)
    co : ∀ {κ f g} → (∀ d → P κ d → Σ (E S κ) (λ e → P κ e × Cover (f d) (g e))) →
      Cover (hΩ κ f) (hΩ κ g)
    cu : ∀ {a κ g} → Σ (E S κ) (P κ) → (∀ e → P κ e → Cover a (g e)) → Cover a (hΩ κ g)
    ct : ∀ {a b c} → Cover a b → Cover b c → Cover a c

  reflexive : ∀ a → Cover a a
  reflexive hz = cz
  reflexive (hs a) = cs (reflexive a)
  reflexive (hl f) = cl (λ n → ci n (reflexive (f n)))
  reflexive (hΩ κ g) = co (λ d ld → d , ld , reflexive (g d))

  module Inhabited (inh : ∀ κ → Σ (E S κ) (P κ)) where
    left : ∀ a b → Cover a (a ⊞ b)
    left a hz = reflexive a
    left a (hs b) = cr (left a b)
    left a (hl f) = ci 0 (left a (f 0))
    left a (hΩ κ g) = cu (inh κ) (λ e _ → left a (g e))

  right : ∀ a b → Cover b (a ⊞ b)
  right a hz = cz
  right a (hs b) = cs (right a b)
  right a (hl f) = cl (λ n → ci n (right a (f n)))
  right a (hΩ κ g) = co (λ d ld → d , ld , right a (g d))

botS : ∀ n κ → LegalS n κ (bot (Sb n) κ)
botT : ∀ n m κ → LegalT n m κ (bot (Tw (Sb n) m) κ)
botS zero ()
botS (suc n) (inj₁ _ , inj₂ _) = tt
botS (suc n) (inj₁ _ , inj₁ κ) = botS n κ
botS (suc n) (inj₂ e , κ) = botT n (hs e) κ
botT n hz κ = botS n κ
botT n (hs m) (inj₂ _) = tt
botT n (hs m) (inj₁ κ) = botT n m κ
botT n (hl f) (i , κ) = botT n (f i) κ
botT n (hΩ κ₀ h) (e , κ) = botT n (h e) κ

module Capture {T : KS} (P : ∀ κ → E T κ → Set)
  (inh : ∀ κ → Σ (E T κ) (P κ)) where
  open Domain T P
  open Inhabited inh

  branch : ∀ {U} (c : Ctx T (step U)) g d → Cover (g d) (New.θ c g (hs d))
  branch c g d = ct (right (New.θ c g d) (g d)) (left (New.θ c g d ⊞ g d) (g (hs d)))

  source : ∀ n (c : Ctx T (Sb n)) κ g d → Cover (g d) (θS n c κ g (bumpS n κ d))
  tower : ∀ n m (c : Ctx T (Tw (Sb n) m)) κ g d → Cover (g d) (θT n m c κ g (bumpT n m κ d))
  source zero c () g d
  source (suc n) c (inj₁ _ , inj₂ _) g d = branch (viaL {F = FX (Sb n)} c (inj₁ tt)) g d
  source (suc n) c (inj₁ _ , inj₁ κ) g d = source n (viaS (viaL {F = FX (Sb n)} c (inj₁ tt))) κ g d
  source (suc n) c (inj₂ e , κ) g d = tower n (hs e) (viaL {F = FX (Sb n)} c (inj₂ e)) κ g d
  tower n hz c κ g d = source n c κ g d
  tower n (hs m) c (inj₂ _) g d = branch c g d
  tower n (hs m) c (inj₁ κ) g d = tower n m (viaS c) κ g d
  tower n (hl f) c (i , κ) g d = tower n (f i) (viaL c i) κ g d
  tower n (hΩ κ₀ h) c (e , κ) g d = tower n (h e) (viaL c e) κ g d

module CompleteCover {S : KS} (P : ∀ κ → E S κ → Set) (A : AllKinds S)
  (capture : ∀ κ g d → P κ d → Σ (E S κ) (λ e → P κ e × Domain.Cover S P (g d) (AllKinds.θK A here κ g e))) where
  open Domain S P
  open Complete A

  partial-cover : ∀ f n → Cover (f n) (partial f n)
  partial-cover f zero = reflexive (f zero)
  partial-cover f (suc n) = right (partial f n) (f (suc n))

  inflate : ∀ a → Cover a (leg a)
  inflate hz = cz
  inflate (hs a) = cs (inflate a)
  inflate (hl f) = cl (λ n → ci n (ct (inflate (f n)) (partial-cover (λ j → leg (f j)) n)))
  inflate (hΩ κ g) = co (λ d ld → go d (capture κ (λ e → leg (g e)) d ld)) where
    go : ∀ d → Σ (E S κ) (λ e → P κ e × Cover (leg (g d)) (AllKinds.θK A here κ (λ x → leg (g x)) e)) →
      Σ (E S κ) (λ e → P κ e × Cover (g d) (AllKinds.θK A here κ (λ x → leg (g x)) e))
    go d (e , le , p) = e , le , ct (inflate (g d)) p

inflateS : ∀ n a → Domain.Cover (Sb n) (LegalS n) a (legS n a)
inflateS n = CompleteCover.inflate (LegalS n) (allS n) (λ κ g d ld → bumpS n κ d , bumpS-legal n κ d ld ,
  Capture.source (LegalS n) (λ κ → bot (Sb n) κ , botS n κ) n here κ g d)

inflateT : ∀ n m a → Domain.Cover (Tw (Sb n) m) (LegalT n m) a (legT n m a)
inflateT n m = CompleteCover.inflate (LegalT n m) (allT n m) (λ κ g d ld → bumpT n m κ d , bumpT-legal n m κ d ld ,
  Capture.tower (LegalT n m) (λ κ → bot (Tw (Sb n) m) κ , botT n m κ) n m here κ g d)

zero-sound : ∀ {a b : Cd} → Domain.Cover S⊥ (LegalS zero) a b → a V.≤ᵛ b
zero-sound Domain.cz = V.z≤
zero-sound (Domain.cs p) = V.s≤s (zero-sound p)
zero-sound (Domain.cr p) = V.≤s (zero-sound p)
zero-sound (Domain.cl p) = V.l≤ (λ n → zero-sound (p n))
zero-sound (Domain.ci n p) = V.≤l n (zero-sound p)
zero-sound (Domain.co {κ = ()} p)
zero-sound (Domain.cu {κ = ()} e p)
zero-sound (Domain.ct p q) = ≤ᵛ-trans (zero-sound p) (zero-sound q)
```

所有种类的域非空由 `botS/botT` 实填，Ω 统一下界规则本身也显式
要求域非空。无输入合法前提，无坐标值单调前提；零层有标准值桥。
本篇没有从覆盖反推路径，也没有证明同一旧世界可以访问所选新坐标。
