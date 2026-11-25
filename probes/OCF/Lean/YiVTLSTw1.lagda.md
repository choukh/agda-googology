# 合法块上塔第 1 项: 链点上的 `LOWER` 与 ψ₀(Ω_ω) 下界 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiLSTw1` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTLSTw1 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath hiding (eq; lt; gt; here)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead
open import OCF.Lean.YiLSRel using (Corr; cz; cs; cl)
open import OCF.Lean.YiVTLSFold using (NL; n0; n+; nω; OKB; ok-B₀; lower)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼)

h₁ : Tr zero → LF
h₁ x = tw 0 ⊕ ↑ (tw 0) x

εh : (x : Tr zero) → Ev (h₁ x)
εh x = proj₂ (proj₂ (Ev-tw 1) x)

ρh : (x : Tr zero) → Rt (h₁ x)
ρh x = proj₂ (Rt-tw 1) x

wh : (x : Tr zero) → zero ≤ h₁ x
wh x = self ∙ lift zero (↑ zero x)

G : Tr zero → Tr zero
G x = ψ₀ (h₁ x) (εh x) (ρh x) (Ωt (h₁ x))

G-nz : (x : Tr zero) → zero ⊢ zero ◃ G x
G-nz x = nz⊥ (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (Ωt (h₁ x))

K : Tr zero → Tr zero
K x = ψs (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) zero (wh x) (suc zero) ◃s (Ωt (h₁ x))

pt : ℕ → Tr zero
pt = iter K zero

tw1-form : twᶜ 1 ≡ limc (λ n → G (pt n)) (λ n → G-nz (pt n))
tw1-form = refl

nl-↑ : (x : Tr zero) → NL (h₁ x)
nl-↑ zero          = n0
nl-↑ (suc x)       = n+ (nl-↑ x)
nl-↑ (lim f a)     = nω (λ n → nl-↑ (f n))
nl-↑ (Ω () _)
nl-↑ (up _ () _ _)

corr-↑ : (x : Tr zero) (h : L.HS (read x)) → Corr (L.toLevel (read x) h) (h₁ x)
corr-↑ zero          h = cz
corr-↑ (suc x)       h = cs (corr-↑ x (L.hs⁻ h))
corr-↑ (lim f a)     h = cl (λ n → corr-↑ (f n) (L.hl₁ h n))
  (λ n → L.toLevel-≺ (L.hl₁ h n) (L.hl₁ h (suc n)) (◃→≺ (a n)))
corr-↑ (Ω () _)      h
corr-↑ (up _ () _ _) h

lvl : Tr zero → L.Ordᴵ
lvl x = L.toLevel (read x) (HSr x)

lower-↑ : (x : Tr zero) → L.ψ⁰ (L.Ω (lvl x)) ≼ read (G x)
lower-↑ x = lower (nl-↑ x) (εh x) (ρh x) (B₀ (h₁ x)) (ok-B₀ (h₁ x)) (corr-↑ x (HSr x))

κ : ℕ → L.Ordᴵ
κ m = lvl (pt m)

LOWER : ∀ m → L.ψ⁰ (L.Ω (κ m)) ≼ read (G (pt m))
LOWER m = lower-↑ (pt m)

ω-tw1 : L.ψ⁰ (L.Ω (κ 1)) ≼ read (twᶜ 1)
ω-tw1 = limcum≽ (λ n → G (pt n)) (λ n → G-nz (pt n)) 1 (LOWER 1)

data E : Tr zero → Tr zero → Set where
  ez : E zero zero
  es : ∀ {a b} → E a b → E (suc a) (suc b)
  el : ∀ {f g a b} → (∀ n → E (f n) (g n)) → E (lim f a) (lim g b)

E-+ : ∀ {a a′ b b′} → E a a′ → E b b′ → E (a + b) (a′ + b′)
E-+ ea ez     = ea
E-+ ea (es e) = es (E-+ ea e)
E-+ ea (el h) = el (λ n → E-+ ea (h n))

E-next : ∀ {b b′} {nb : zero ⊢ zero ◃ b} {nb′ : zero ⊢ zero ◃ b′} → E b b′ → E (next b nb) (next b′ nb′)
E-next {b} {b′} e = el go
  where
  go : ∀ n → E (iter (b +_) b n) (iter (b′ +_) b′ n)
  go zero    = e
  go (suc n) = E-+ e (go n)

E-cum : (F F′ : ℕ → Tr zero) {a : ∀ n → zero ⊢ cum F n ◃ cum F (suc n)} {b : ∀ n → zero ⊢ cum F′ n ◃ cum F′ (suc n)}
  → (∀ n → E (F n) (F′ n)) → E (lim (cum F) a) (lim (cum F′) b)
E-cum F F′ h = el go
  where
  go : ∀ n → E (cum F n) (cum F′ n)
  go zero    = h zero
  go (suc n) = E-+ (go n) (h (suc n))

E→≅ : ∀ {a b} → E a b → read a L.≅ read b
E→≅ ez     = L.z≅
E→≅ (es e) = L.s≅ (E→≅ e)
E→≅ (el h) = L.l≅ (λ n → E→≅ (h n))

LiftP : ∀ {j ℓ} → j ≤ ℓ → Set
LiftP self      = ⊤
LiftP (ins w)   = LiftP w
LiftP (inl n w) = ⊥
LiftP (inlu ws) = ∀ n → LiftP (ws n)
LiftP (ink w)   = ⊥
LiftP (inb c w) = ⊥
LiftP (inu ws)  = ∀ c → LiftP (ws c)

LiftP-∙ : ∀ {ℓ} (a b : LF) (w : ℓ ≤ a) → LiftP w → LiftP (w ∙ lift a b)
LiftP-∙ a zero     w lw = lw
LiftP-∙ a (suc b)  w lw = LiftP-∙ a b w lw
LiftP-∙ a (lim g)  w lw = λ n → LiftP-∙ a (g n) w lw
LiftP-∙ a (Ωₗ k h) w lw = λ c → LiftP-∙ a (h c) w lw

eq0 : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (w : zero ≤ ℓ) → LiftP w
    → (β : Tr zero) (nβ : zero ⊢ zero ◃ β) → E β (b⊥ B)
    → (x : Tr ℓ) → E (ψs ℓ ε ρ B zero w β nβ x) (ψ⊥ ℓ ε ρ B x)
eq0 ℓ ε ρ B w lw β nβ e zero      = e
eq0 ℓ ε ρ B w lw β nβ e (suc x)   = E-next (eq0 ℓ ε ρ B w lw β nβ e x)
eq0 ℓ ε ρ B w lw β nβ e (lim f a) = el (λ n → eq0 ℓ ε ρ B w lw β nβ e (f n))
eq0 ℓ ε ρ B w lw β nβ e (Ω p g) =
  kp-ind ℓ ε ρ p w (λ X → E X (ψ⊥ ℓ ε ρ B (Ω p g))) (λ ())
    (E-cum _ _ (λ n → eq0 ℓ ε ρ B w lw β nβ e (g _)))
eq0 zero     ε ρ B w         lw β nβ e (up x () y e′)
eq0 (suc a)  ε ρ B (ins w)   lw β nβ e (up x _ y e′) =
  eq0 a ε ρ (dS a ε ρ B x) w lw _ _ (eq0 (suc a) ε ρ B (ins w) lw β nβ e x) y
eq0 (lim g)  ε (ρc , R) B (inlu ws) lw β nβ e (up x m y e′) =
  eq0 (g m) (ε m) (ρc m) (dL g ε (ρc , R) B m x) (ws m) (lw m) _ _ (eq0 (lim g) ε (ρc , R) B (inlu ws) lw β nβ e x) y
eq0 (Ωₗ k h) ε ρ B (inu ws)  lw β nβ e (up x c y e′) =
  eq0 (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) (ws c) (lw c) _ _
    (eq0 (Ωₗ k h) ε ρ B (inu ws) lw β nβ e x) y

KG : (x : Tr zero) → read (K x) L.≅ read (G x)
KG x = E→≅ (eq0 (h₁ x) (εh x) (ρh x) (B₀ (h₁ x)) (wh x) (LiftP-∙ zero (↑ zero x) self tt) (suc zero) ◃s (es ez) (Ωt (h₁ x)))
```
