# Prefix (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Prefix](../../Align/Prefix.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Prefix where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Uniform using (Uniform)
open import OCF.Free.Lab.Symbolic using (Fs; Fst; Mlev; Ctx; Pt; pt; lvP; Γᶜ; χᶜ; χᶜ-step; σ1; X₂ᵗ)
import OCF.Free.Lab.NoCumsum as N
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; Lab-≅)
open import OCF.Free.Lab.Label using (BTBO-label)
open import OCF.Free.Lab.Stage2 using (γ′ᴱ; t2)
open import OCF.Free.Lab.Standard using (Ctbl; c[]; c∷) renaming (d₀ to d₀ᴰ)
import OCF.Free.Lab.StandardOmega as SΩ
open import OCF.Free.Lab.SystemOmega using (occ<; Occ; oh; od; ot)
open import OCF.Free.Prefix public
```

```agda
open Ord-Ord using (iter)
open Restr renaming (eq to eqᴿ; lt to ltᴿ)
open E using (T; Cmp; lt; eq; gt; cof; cofA; cofψ₊; cmpᵀ; natT; fsT; fsn; fsTc; cΩ; cω; _<ᵀ_) renaming (ψ to ψᵗ)
open SΩ using (NF₁; cofin₁; diag₁-desc-NF; walkD)
```

## §1 接口核对: H1–H4

```agda
H1-cmp : ∀ x xs → cmpᵀ (natT 1) (x ∷ xs) ≡ gt → ⊥
H1-cmp (ψᵗ [] [])      []      ()
H1-cmp (ψᵗ [] [])      (_ ∷ _) ()
H1-cmp (ψᵗ [] (_ ∷ _)) _       ()
H1-cmp (ψᵗ (_ ∷ _) _)  _       ()

H1-pen : ∀ x xs → cofA (x ∷ xs) (cΩ []) ≡ cΩ []
H1-pen x xs = go (cmpᵀ (natT 1) (x ∷ xs)) (H1-cmp x xs) where
  go : ∀ m → (m ≡ gt → ⊥) → cofψ₊ (x ∷ xs) [] m ≡ cΩ []
  go lt _ = refl
  go eq _ = refl
  go gt h = ⊥-elim (h refl)

H1-fsT : ∀ x xs y ys → cof (y ∷ ys) ≡ cΩ [] → ∀ η →
         fsT (ψᵗ (x ∷ xs) (y ∷ ys) ∷ []) η ≡ ψᵗ (x ∷ xs) (fsT (y ∷ ys) η) ∷ []
H1-fsT x xs y ys e η with cof (y ∷ ys) | e
... | .(cΩ []) | refl = go (cmpᵀ (natT 1) (x ∷ xs)) (H1-cmp x xs) where
  go : ∀ m → (m ≡ gt → ⊥) → fsTc (x ∷ xs) (y ∷ ys) [] m η ≡ ψᵗ (x ∷ xs) (fsT (y ∷ ys) η) ∷ []
  go lt _ = refl
  go eq _ = refl
  go gt h = ⊥-elim (h refl)
```

```agda
toX₂ : List ℕ
toX₂ = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ []

X₂-NF : NF₁ X₂ᵗ
X₂-NF = diag₁-desc-NF (walkD d₀ᴰ toX₂ (refl , refl , refl , refl , refl , refl , tt))
```

## §2 新树族 (Symbolic §3 的修改版)

```agda
open Restrˢ
```

## §3 前缀栈折叠 $\psi^P$

```agda
data Frame (ℓ : Ordᴵ) : Set where
  fΩ̂ : zero <ᴵ ℓ → Frame ℓ
  fT  : ∀ {k} → Ordˢ k → Simᴵ k ℓ → Frame ℓ

liftF : ∀ {ℓ ℓ′} → Simᴵ ℓ ℓ′ → Frame ℓ → Frame ℓ′
liftF ρ (fΩ̂ z)   = fΩ̂ (ρ z)
liftF ρ (fT x σ) = fT x (λ q → ρ (σ q))

liftV : ∀ {ℓ ℓ′ n} → Simᴵ ℓ ℓ′ → Vec (Frame ℓ) n → Vec (Frame ℓ′) n
liftV ρ []      = []
liftV ρ (f ∷ P) = liftF ρ f ∷ liftV ρ P

onlyΩ̂ : ∀ {ℓ n} → Vec (Frame ℓ) n → Bool
onlyΩ̂ []           = true
onlyΩ̂ (fΩ̂ _ ∷ P)   = onlyΩ̂ P
onlyΩ̂ (fT _ _ ∷ P) = false

z<suc : ∀ {i ℓ} → zero <ᴵ ℓ → i <ᴵ ℓ → zero <ᴵ suc i
z<suc z p with <ᴵ-dec z p
... | injᵃ (via z≅ r) = suc r
... | injᵇ (via e ())
... | injᶜ z≅ = zero

record Base (i : Ordᴵ) (n : ℕ) : Set where
  constructor base
  field
    cb  : Ordᴵ
    tgt : i <ᴵ cb
    stk : Vec (Frame cb) n
    one : zero <ᴵ cb
open Base

rebase′ : ∀ {i ℓ n} → Bool → i <ᴵ ℓ → zero <ᴵ ℓ → Vec (Frame ℓ) n → Base i n
rebase′ {i} {n = n} true  p z P = base (suc i) zero (replicate n (fΩ̂ (z<suc z p))) (z<suc z p)
rebase′ {ℓ = ℓ}    false p z P = base ℓ p P z

rebase : ∀ {i ℓ n} → i <ᴵ ℓ → zero <ᴵ ℓ → Vec (Frame ℓ) n → Base i n
rebase p z P = rebase′ (onlyΩ̂ P) p z P
```

```agda
ψᴾ : ∀ (n : ℕ) {i k ℓ} → i <ᴵ ℓ → Simᴵ k ℓ → Vec (Frame ℓ) n → Ordˢ k → Ordˢ i
ψᴾ n p σ P (suc a) = lim (iter (ψᴾ n p σ P a +ˢ_) zero)
ψᴾ n p σ P (lim f) = lim (λ m → ψᴾ n p σ P (f m))
ψᴾ n p σ P (limᵢ {i = j} q f) with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = limᵢ r (λ y → ψᴾ n p σ P (f (intoˢ (<→◃ q) (tr⁻ˢ e (outˢ (<→◃ r) y)))))
... | injᵇ _ = lim (λ m → ψᴾ n p σ P (f (intoˢ (<→◃ q) (iter (λ x → ψᴾ n (σ q) σ P (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
... | injᶜ _ = lim (λ m → ψᴾ n p σ P (f (intoˢ (<→◃ q) (iter (λ x → ψᴾ n (σ q) σ P (f (intoˢ (<→◃ q) x))) (Ωˢ j) m))))
ψᴾ n p σ P (up zero x)     = ψᴾ n p (λ q → σ (suc q)) P x
ψᴾ n p σ P (up (self m) x) = ψᴾ n p (λ q → σ (lim m q)) P x
ψᴾ n {k = zero}    p σ P (ŝ c t₀ g) = ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (ψᴾ n p σ P t₀) (λ η e → ψᴾ n p σ P (g η e))
ψᴾ n {k = suc _}   p σ P (ŝ c t₀ g) = ŝ c (ψᴾ n p σ P t₀) (λ η e → ψᴾ n p σ P (g η e))
ψᴾ n {k = lim _ _} p σ P (ŝ c t₀ g) = ŝ c (ψᴾ n p σ P t₀) (λ η e → ψᴾ n p σ P (g η e))
ψᴾ n p σ P (ĉᴸ c t₀ g o₀ o) = ĉᴸ c t₀ g (ψᴾ n p σ P o₀) (λ η e → ψᴾ n p σ P (o η e))
ψᴾ zero    p σ []            zero = Ωˢ _
ψᴾ (suc n) p σ (fT x σ′ ∷ P) zero = ψᴾ n p σ′ P x
ψᴾ (suc n) p σ (fΩ̂ z ∷ P)    zero =
  ŝ (cb B) (ψᴾ n (tgt B) (σ1 (one B)) (stk B) (Ωˢ (suc zero)))
           (λ η e → ψᴾ n {ℓ = Mlev (cb B) η e} (lim 0 (tgt B)) (λ q → lim 1 q) (liftV (λ q → lim 0 q) (stk B)) (Ωˢ η))
  where B = rebase p z P
```

## §4 `Goodᶻ`/`force` 对 `ĉᴸ`

```agda
outs : (C : Ctx) → Ordᶜ zero → ((η : Ordᴵ) → Ctx.c C ⊑ᴵ η → Ordᶜ zero) → ℕ → Ordᶜ zero
outs C O₀ O zero    = O₀
outs C O₀ O (suc k) = O (lvP C (Γᶜ C k)) (Pt.dx (Γᶜ C k))

outs-HS : (C : Ctx) {O₀ : Ordᶜ zero} {O : (η : Ordᴵ) → Ctx.c C ⊑ᴵ η → Ordᶜ zero} →
          HS O₀ → (∀ η e → HS (O η e)) → ∀ n → HS (outs C O₀ O n)
outs-HS C h₀ h zero    = h₀
outs-HS C h₀ h (suc k) = h _ _

outs-step : (C : Ctx) {O₀ : Ordᶜ zero} {O : (η : Ordᴵ) → Ctx.c C ⊑ᴵ η → Ordᶜ zero} →
            (∀ η e → O₀ ⊑⁰ O η e) → (∀ η e η′ e′ → η ⊑ᴵ η′ → O η e ⊑⁰ O η′ e′) →
            ∀ n → outs C O₀ O n ⊑⁰ outs C O₀ O (suc n)
outs-step C m₀ m zero    = m₀ _ _
outs-step C m₀ m (suc k) = m _ _ _ _ (toLevel-⊑ (Pt.hx (Γᶜ C k)) (Pt.hx (Γᶜ C (suc k))) (χᶜ-step C k))

data Goodᶻ : Z → Set
force    : (x : Z) → Goodᶻ x → Ordᶜ zero
force-HS : (x : Z) (G : Goodᶻ x) → HS (force x G)

data Goodᶻ where
  gz : Goodᶻ zero
  gs : ∀ {x} → Goodᶻ x → Goodᶻ (suc x)
  gl : ∀ {f : ℕ → Z} (G : ∀ n → Goodᶻ (f n)) →
       (∀ n → force (f n) (G n) ⊑⁰ force (f (suc n)) (G (suc n))) → Goodᶻ (lim f)
  gc : ∀ {c t₀ o₀} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z}
       (G₀ : Goodᶻ t₀) (Gg : ∀ η e → Goodᶻ (g η e)) →
       c ⊑ᴵ toLevel (force t₀ G₀) (force-HS t₀ G₀) →
       (∀ η e → c ⊑ᴵ toLevel (force (g η e) (Gg η e)) (force-HS (g η e) (Gg η e))) →
       (∀ η e → force t₀ G₀ ⊑⁰ force (g η e) (Gg η e)) →
       (∀ η e η′ e′ → η ⊑ᴵ η′ → force (g η e) (Gg η e) ⊑⁰ force (g η′ e′) (Gg η′ e′)) →
       (Go₀ : Goodᶻ o₀) (Go : ∀ η e → Goodᶻ (o η e)) →
       (∀ η e → force o₀ Go₀ ⊑⁰ force (o η e) (Go η e)) →
       (∀ η e η′ e′ → η ⊑ᴵ η′ → force (o η e) (Go η e) ⊑⁰ force (o η′ e′) (Go η′ e′)) →
       Goodᶻ (ĉᴸ c t₀ g o₀ o)

force zero    gz        = zero
force (suc x) (gs G)    = suc (force x G)
force (lim f) (gl G st) = lim (λ n → force (f n) (G n))
force (ĉᴸ c t₀ g o₀ o) (gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  lim (outs (record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
                    ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
                    ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE })
            (force o₀ Go₀) (λ η e → force (o η e) (Go η e)))

force-HS zero    gz        = hz
force-HS (suc x) (gs G)    = hs (force-HS x G)
force-HS (lim f) (gl G st) = hl (λ n → force-HS (f n) (G n)) st
force-HS (ĉᴸ c t₀ g o₀ o) (gc G₀ Gg d₀ dE m₀ mE Go₀ Go mo₀ mo) =
  hl (outs-HS C (force-HS o₀ Go₀) (λ η e → force-HS (o η e) (Go η e)))
     (outs-step C mo₀ mo)
  where C = record { c = c ; t₀ = force t₀ G₀ ; E = λ η e → force (g η e) (Gg η e)
                   ; h₀ = force-HS t₀ G₀ ; hE = λ η e → force-HS (g η e) (Gg η e)
                   ; d₀ = d₀ ; dE = dE ; m₀ = m₀ ; mE = mE }

-- the pure chain (o = g) is literally Symbolic's Tᶜ
```

## §5 空栈与 Level 的 $\psi$: 异族互模拟

```agda
module _ (ℓ : Ordᴵ) (Rh : (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set) where
  data H₊ : ∀ {ℓ′} → Ordˢ ℓ → Ordᶜ ℓ′ → Set where
    z~  : ∀ {ℓ′} → H₊ {ℓ′} zero zero
    s~  : ∀ {ℓ′} {a : Ordˢ ℓ} {b : Ordᶜ ℓ′} → H₊ a b → H₊ (suc a) (suc b)
    l~  : ∀ {ℓ′} {f : ℕ → Ordˢ ℓ} {g : ℕ → Ordᶜ ℓ′} → (∀ n → H₊ (f n) (g n)) → H₊ (lim f) (lim g)
    lᵢ~ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : Uˢ j (<→◃ p) → Ordˢ ℓ} {g : U j′ (<→◃ q) → Ordᶜ ℓ′} →
          j ≅ᴵ j′ →
          (∀ (x : Ordˢ j) (y : Ordᶜ j′) → Rh j (<→◃ p) (intoˢ (<→◃ p) x) y → H₊ (f (intoˢ (<→◃ p) x)) (g (into (<→◃ q) y))) →
          H₊ (limᵢ p f) (limᵢ q g)
    upˡ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : Uˢ k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → Rh k (◃₁→◃ r) x b → H₊ (up r x) b
    upʳ : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : U k (◃₁→◃ r)} {a : Ordˢ ℓ} → H₊ a (out (◃₁→◃ r) y) → H₊ a (up r y)

Rh : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → Uˢ i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set
Rh i zero         x b = H₊ i Rh x b
Rh i (suc r)      x b = Rh i r x b
Rh _ (self {f} n) x b = H₊ (f n) Rh x b
Rh i (lim n r)    x b = Rh i r x b

infix 4 _~_
_~_ : ∀ {ℓ₁ ℓ₂} → Ordˢ ℓ₁ → Ordᶜ ℓ₂ → Set
_~_ {ℓ₁} = H₊ ℓ₁ Rh

Rh→~ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordᶜ ℓ′} → Rh i r (intoˢ r x) b → x ~ b
Rh→~ zero      e = e
Rh→~ (suc r)   e = Rh→~ r e
Rh→~ (self n)  e = e
Rh→~ (lim n r) e = Rh→~ r e

~→Rh : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordˢ i} {b : Ordᶜ ℓ′} → x ~ b → Rh i r (intoˢ r x) b
~→Rh zero      e = e
~→Rh (suc r)   e = ~→Rh r e
~→Rh (self n)  e = e
~→Rh (lim n r) e = ~→Rh r e
```

```agda
trˢ-~    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ a} {y : Ordᶜ ℓ′} → x ~ y → trˢ e x ~ y
tr⁻ˢ-~   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordˢ b} {y : Ordᶜ ℓ′} → x ~ y → tr⁻ˢ e x ~ y
backˢ-~  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (resˢ q e))} {v : Ordᶜ ℓ′} → u ~ v → backˢ (resˢ q e) u ~ v
back⁻ˢ-~ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordˢ (repˢ (res⁻ˢ q e))} {v : Ordᶜ ℓ′} → u ~ v → backˢ (res⁻ˢ q e) u ~ v

trˢ-~ e z~      = z~
trˢ-~ e (s~ d)  = s~ (trˢ-~ e d)
trˢ-~ e (l~ h)  = l~ (λ n → trˢ-~ e (h n))
trˢ-~ e (lᵢ~ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ~ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (resˢ q e))) ej) λ u v d →
    subst (λ w → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) w))) ~ g (into (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (resˢ q e))) u))
          (trˢ-~ e (h _ v (~→Rh (<→◃ q) (backˢ-~ q e (Rh→~ (<→◃ (ltˢ (resˢ q e))) d)))))
trˢ-~ (s≅ e) (upˡ {r = zero} d)   = upˡ (trˢ-~ e d)
trˢ-~ (l≅ h) (upˡ {r = self n} d) = upˡ (trˢ-~ (h n) d)
trˢ-~ e (upʳ d) = upʳ (trˢ-~ e d)

tr⁻ˢ-~ e z~      = z~
tr⁻ˢ-~ e (s~ d)  = s~ (tr⁻ˢ-~ e d)
tr⁻ˢ-~ e (l~ h)  = l~ (λ n → tr⁻ˢ-~ e (h n))
tr⁻ˢ-~ e (lᵢ~ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ~ (≅ᴵ-trans (≅ᴵ-sym (eqˢ (res⁻ˢ q e))) ej) λ u v d →
    subst (λ w → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) w))) ~ g (into (<→◃ q₂) v))
          (sym (out-intoˢ (<→◃ (ltˢ (res⁻ˢ q e))) u))
          (tr⁻ˢ-~ e (h _ v (~→Rh (<→◃ q) (back⁻ˢ-~ q e (Rh→~ (<→◃ (ltˢ (res⁻ˢ q e))) d)))))
tr⁻ˢ-~ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr⁻ˢ-~ e d)
tr⁻ˢ-~ (l≅ h) (upˡ {r = self n} d) = upˡ (tr⁻ˢ-~ (h n) d)
tr⁻ˢ-~ e (upʳ d) = upʳ (tr⁻ˢ-~ e d)

backˢ-~ zero      (s≅ e) d = tr⁻ˢ-~ e d
backˢ-~ (suc q)   (s≅ e) d = backˢ-~ q e d
backˢ-~ (lim n q) (l≅ h) d = backˢ-~ q (h n) d

back⁻ˢ-~ zero      (s≅ e) d = trˢ-~ e d
back⁻ˢ-~ (suc q)   (s≅ e) d = back⁻ˢ-~ q e d
back⁻ˢ-~ (lim n q) (l≅ h) d = back⁻ˢ-~ q (h n) d

-- 旧族一侧的搬运不可见
~-tr    : ∀ {a b ℓ} (e : a ≅ᴵ b) {x : Ordˢ ℓ} {y : Ordᶜ a} → x ~ y → x ~ tr e y
~-tr⁻   : ∀ {a b ℓ} (e : a ≅ᴵ b) {x : Ordˢ ℓ} {y : Ordᶜ b} → x ~ y → x ~ tr⁻ e y
~-back  : ∀ {j a b ℓ} (q : j <ᴵ a) (e : a ≅ᴵ b) {x : Ordˢ ℓ} {u : Ordᶜ (rep (res q e))} → x ~ u → x ~ back (res q e) u
~-back⁻ : ∀ {j a b ℓ} (q : j <ᴵ b) (e : a ≅ᴵ b) {x : Ordˢ ℓ} {u : Ordᶜ (rep (res⁻ q e))} → x ~ u → x ~ back (res⁻ q e) u

~-tr e z~     = z~
~-tr e (s~ d) = s~ (~-tr e d)
~-tr e (l~ h) = l~ (λ n → ~-tr e (h n))
~-tr e (lᵢ~ {p = p} {q = q} {f = f} {g = g} ej h) =
  lᵢ~ (≅ᴵ-trans ej (eqᴿ (res q e))) λ x v d →
    subst (λ w → f (intoˢ (<→◃ p) x) ~ tr e (g (into (<→◃ q) (back (res q e) w))))
          (sym (out-into (<→◃ (ltᴿ (res q e))) v))
          (~-tr e (h x _ (~→Rh (<→◃ p) (~-back q e (Rh→~ (<→◃ p) d)))))
~-tr e (upˡ {r = zero} d)   = upˡ (~-tr e d)
~-tr e (upˡ {r = self n} d) = upˡ (~-tr e d)
~-tr (s≅ e) (upʳ {r = zero} d)   = upʳ (~-tr e d)
~-tr (l≅ h) (upʳ {r = self n} d) = upʳ (~-tr (h n) d)

~-tr⁻ e z~     = z~
~-tr⁻ e (s~ d) = s~ (~-tr⁻ e d)
~-tr⁻ e (l~ h) = l~ (λ n → ~-tr⁻ e (h n))
~-tr⁻ e (lᵢ~ {p = p} {q = q} {f = f} {g = g} ej h) =
  lᵢ~ (≅ᴵ-trans ej (eqᴿ (res⁻ q e))) λ x v d →
    subst (λ w → f (intoˢ (<→◃ p) x) ~ tr⁻ e (g (into (<→◃ q) (back (res⁻ q e) w))))
          (sym (out-into (<→◃ (ltᴿ (res⁻ q e))) v))
          (~-tr⁻ e (h x _ (~→Rh (<→◃ p) (~-back⁻ q e (Rh→~ (<→◃ p) d)))))
~-tr⁻ e (upˡ {r = zero} d)   = upˡ (~-tr⁻ e d)
~-tr⁻ e (upˡ {r = self n} d) = upˡ (~-tr⁻ e d)
~-tr⁻ (s≅ e) (upʳ {r = zero} d)   = upʳ (~-tr⁻ e d)
~-tr⁻ (l≅ h) (upʳ {r = self n} d) = upʳ (~-tr⁻ (h n) d)

~-back zero      (s≅ e) d = ~-tr⁻ e d
~-back (suc q)   (s≅ e) d = ~-back q e d
~-back (lim n q) (l≅ h) d = ~-back q (h n) d

~-back⁻ zero      (s≅ e) d = ~-tr e d
~-back⁻ (suc q)   (s≅ e) d = ~-back⁻ q e d
~-back⁻ (lim n q) (l≅ h) d = ~-back⁻ q (h n) d
```

```agda
Ω~ : ∀ {a b} → a ≅ᴵ b → Ωˢ a ~ Ω b
Ω~ z≅     = s~ z~
Ω~ (s≅ e) = lᵢ~ e (λ x y d → upˡ (upʳ d))
Ω~ (l≅ h) = l~ (λ n → upˡ (upʳ (Ω~ (h n))))

add~ : ∀ {k₁ ℓ₁ k₂ ℓ₂} {σ : Simᴵ k₁ ℓ₁} {σ′ : Simᴵ k₂ ℓ₂} {a : Ordˢ ℓ₁} {a′ : Ordᶜ ℓ₂} {b : Ordˢ k₁} {b′ : Ordᶜ k₂} →
       a ~ a′ → b ~ b′ → addˢ a σ b ~ add a′ σ′ b′
add~ ea z~     = ea
add~ ea (s~ e) = s~ (add~ ea e)
add~ ea (l~ h) = l~ (λ n → add~ ea (h n))
add~ ea (upˡ {r = zero} e)   = add~ ea e
add~ ea (upˡ {r = self n} e) = add~ ea e
add~ ea (upʳ {r = zero} e)   = add~ ea e
add~ ea (upʳ {r = self n} e) = add~ ea e
add~ {σ = σ} {σ′ = σ′} {a = a} {a′ = a′} ea (lᵢ~ {p = q} {q = q′} {f = f} {g = g} e h) = lᵢ~ e λ x y d →
  subst₂ (λ u v → addˢ a σ (f (intoˢ (<→◃ q) u)) ~ add a′ σ′ (g (into (<→◃ q′) v)))
         (sym (out-intoˢ (<→◃ (σ q)) x)) (sym (out-into (<→◃ (σ′ q′)) y))
         (add~ ea (h x y (~→Rh (<→◃ q) (Rh→~ (<→◃ (σ q)) d))))

ψ~ : ∀ {i i′ k₁ ℓ₁ k₂ ℓ₂} {p : i <ᴵ ℓ₁} {σ : Simᴵ k₁ ℓ₁} {p′ : i′ <ᴵ ℓ₂} {σ′ : Simᴵ k₂ ℓ₂}
     {a : Ordˢ k₁} {b : Ordᶜ k₂} → i ≅ᴵ i′ → a ~ b → ψᴾ 0 p σ [] a ~ ψ p′ σ′ b
ψ~ ei z~ = Ω~ ei
ψ~ ei (s~ e) = l~ (iter-R _~_ (λ e′ → add~ (ψ~ ei e) e′) z~)
ψ~ ei (l~ h) = l~ (λ n → ψ~ ei (h n))
ψ~ ei (upˡ {r = zero} e)   = ψ~ ei e
ψ~ ei (upˡ {r = self n} e) = ψ~ ei e
ψ~ ei (upʳ {r = zero} e)   = ψ~ ei e
ψ~ ei (upʳ {r = self n} e) = ψ~ ei e
ψ~ {p = p} {σ = σ} {p′ = p′} {σ′ = σ′} ei (lᵢ~ {p = q} {q = q′} {f = f} {g = g} e h)
  with <ᴵ-dec (σ q) p | <ᴵ-dec (σ′ q′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢ~ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ u v → ψᴾ 0 p σ [] (f (intoˢ (<→◃ q) (tr⁻ˢ e₁ u))) ~ ψ p′ σ′ (g (into (<→◃ q′) (tr⁻ e₂ v))))
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-into (<→◃ r₂) y))
         (ψ~ ei (h _ _ (~→Rh (<→◃ q) (tr⁻ˢ-~ e₁ (~-tr⁻ e₂ (Rh→~ (<→◃ r₁) d))))))
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c  = ⊥-elim (clash₂ e ei r c)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c | injᵃ r  = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c)
... | injᵇ _ | injᵇ _  = l~ (λ n → ψ~ ei (h _ _ (~→Rh (<→◃ q) (chain n))))
  where chain = iter-R _~_ (λ d → ψ~ e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
... | injᵇ _ | injᶜ _  = l~ (λ n → ψ~ ei (h _ _ (~→Rh (<→◃ q) (chain n))))
  where chain = iter-R _~_ (λ d → ψ~ e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
... | injᶜ _ | injᵇ _  = l~ (λ n → ψ~ ei (h _ _ (~→Rh (<→◃ q) (chain n))))
  where chain = iter-R _~_ (λ d → ψ~ e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
... | injᶜ _ | injᶜ _  = l~ (λ n → ψ~ ei (h _ _ (~→Rh (<→◃ q) (chain n))))
  where chain = iter-R _~_ (λ d → ψ~ e (h _ _ (~→Rh (<→◃ q) d))) (Ω~ e)
```

```agda
force~ : ∀ {x : Ordˢ zero} {y : Ordᶜ zero} → x ~ y → (G : Goodᶻ (toZ x)) → force (toZ x) G ≅ y
force~ z~     gz        = z≅
force~ (s~ d) (gs G)    = s≅ (force~ d G)
force~ (l~ h) (gl G st) = l≅ (λ n → force~ (h n) (G n))
force~ (lᵢ~ {p = ()} e h) G
force~ (upˡ {r = ()} e) G
force~ (upʳ {r = ()} e) G

empty~ : ∀ {i ℓ a} (p : i <ᴵ ℓ) (σ : Simᴵ a ℓ) → ψᴾ 0 p σ [] (Ωˢ a) ~ ψ p σ (Ω a)
empty~ p σ = ψ~ (≅ᴵ-refl _) (Ω~ (≅ᴵ-refl _))

empty-agree : ∀ {ℓ a} (p : zero <ᴵ ℓ) (σ : Simᴵ a ℓ) (G : Goodᶻ (toZ (ψᴾ 0 p σ [] (Ωˢ a)))) →
              force (toZ (ψᴾ 0 p σ [] (Ωˢ a))) G ≅ ψ⁰ (Ω a)
empty-agree {a = a} p σ G = ≅-trans (force~ (empty~ p σ) G) (≅-sym (ψ⁰≅ψ {p = p} {σ = σ} (Ω-refl a)))
```

## §6 检验 1: $\psi^{[\hat\Omega]}(0)$ 的计值就是 `BTBOᴵ`

```agda
z2 : zero <ᴵ suc (suc zero)
z2 = suc zero
```

## §7 检验 2、3: 符号树的结构, 与界为什么必须紧

```agda
X₂ˢ : Ordˢ zero
X₂ˢ = ψᴾ 1 z2 (λ q → q) (fΩ̂ z2 ∷ []) (Ωˢ (suc (suc zero)))
```

## §10 结论与边界
