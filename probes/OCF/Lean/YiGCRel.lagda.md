# 精确 Level 参照在精简块上的沿帧关系
验收文件；关系与搬运、加法、逐层嵌入及第 0 层值出口。
来源：YiLSRel 的 Sim/TRJ/Add；上下文直接复用 YiFPFrames，槽位按统一形状改写。
不修改树、折叠或合法性；该关系尚不是 EboLean 的 M。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGCRel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiRWBlock renaming (L to LF)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiFPFrames using (Dc; Ctx; []; _∷_; fr; snocD; snocC; kid; asChild)
open import OCF.Lean.YiGCCorr using (Corr; cz; cs; cl; uniq)
open import OCF.Lean.YiLeanValRel using (TRC; module Back)
import OCF.Align.Level as L
open L using (_≅ᴵ_; _<ᴵ_; _≺ᴵ_)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
Corr-≅ : ∀ {a b x} → a ≅ᴵ b → Corr b x → Corr a x
Corr-≅ L.z≅ cz = cz
Corr-≅ (L.s≅ e) (cs c) = cs (Corr-≅ e c)
Corr-≅ (L.l≅ h) (cl c st) = cl (λ n → Corr-≅ (h n) (c n))
  (λ n → L.≺ᴵ-respˡ (h n) (L.≺ᴵ-respʳ (st n) (L.≅ᴵ-sym (h (suc n)))))

module Sim (ℓ : LF) (Sl : ∀ {j} → Dc ℓ j → (p : Pos j) → ∀ {i} → L.Ordᶜ i → Br j p → Set) where
  data J : ∀ {j} {d : Dc ℓ j} → Ctx ℓ d → ∀ {k} → L.Ordᶜ k → Tr j → Set where
    zr  : ∀ {k} {y : Tr ℓ} → J [] {k} L.zero y
    pop : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {t : Tr j} {c : CH j} {y : Tr (kid j c)}
        → J Γ X t → J (snocC Γ t c) X y
    ss  : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {y : Tr j} → J Γ X y → J Γ (L.suc X) (suc y)
    wk  : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {y y′ : Tr j} → J Γ X y → j ⊢ y ◃ y′ → J Γ X y′
    ll  : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {F : ℕ → L.Ordᶜ k} {y : Tr j} → (∀ n → J Γ (F n) y) → J Γ (L.lim F) y
    nodeR  : ∀ {j d} {Γ : Ctx ℓ {j} d} {i K′} {q : i <ᴵ K′} {f : L.U i (L.<→◃ q) → L.Ordᶜ K′}
            {p : Pos j} {g : Br j p → Tr j}
        → Corr i (at j p)
        → (∀ (y₀ : L.Ordᶜ i) (c : Br j p) → Sl d p y₀ c → J Γ (f (L.into (L.<→◃ q) y₀)) (g c))
        → J Γ (L.limᵢ q f) (Ω p g)
    ur  : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {y : Tr j} → J Γ X y → J Γ (L.up {k = k} L.zero X) y
    ul  : ∀ {j d} {Γ : Ctx ℓ {j} d} {f : ℕ → L.Ordᴵ} {s : ∀ n → f n L.⊑ᴵ f (suc n)} (n : ℕ) {X : L.Ordᶜ (f n)} {y : Tr j}
        → J Γ X y → J Γ {L.lim f s} (L.up (L.self n) X) y
    psh : ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {t : Tr j} {c : CH j} {y : ChT j c} {e : RCh j c (chZ j c) y}
        → J (snocC Γ t c) X (asChild j c y) → J Γ X (up t c y e)

open Sim public using (zr; pop; ss; wk; ll; nodeR; ur; ul; psh)

Rel   : (ℓ : LF) → ∀ {k} → L.Ordᶜ k → Tr ℓ → Set
SlOf  : (ℓ : LF) → ∀ {j} → Dc ℓ j → (p : Pos j) → ∀ {i} → L.Ordᶜ i → Br j p → Set
RelP  : (ℓ : LF) (p : Pos ℓ) → ∀ {i} → L.Ordᶜ i → Br ℓ p → Set
RelP⁼ : (a : LF) (p : Pos⁼ a) → ∀ {i} → L.Ordᶜ i → Br⁼ a p → Set

Rel ℓ X y = Sim.J ℓ (SlOf ℓ) [] X y

SlOf ℓ [] p = RelP ℓ p
SlOf zero (() ∷ d) p
SlOf (nd s h) (c ∷ d) p = SlOf (h c) d p

RelP (nd s h) (inj₂ (c , t)) = RelP⁼ (h c) t
RelP (nd (sΩ k) h) (inj₁ t) = RelP⁼ k t

RelP⁼ a (inj₁ _) = Rel a
RelP⁼ a (inj₂ p) = RelP a p
module TRJ (ℓ : LF) (Sl : ∀ {j} → Dc ℓ j → (p : Pos j) → ∀ {i} → L.Ordᶜ i → Br j p → Set)
  (ST : ∀ {j} (d : Dc ℓ j) (p : Pos j) → TRC (λ {i} → Sl d p {i})) where
  open Sim ℓ Sl using (J)

  TR⁻ : ∀ {a b} (e : a ≅ᴵ b) {j d} {Γ : Ctx ℓ {j} d} {y : L.Ordᶜ b} {η} → J Γ y η → J Γ (L.tr⁻ e y) η
  TR⁻ e zr = zr
  TR⁻ e (pop r) = pop (TR⁻ e r)
  TR⁻ e (ss r) = ss (TR⁻ e r)
  TR⁻ e (wk r d) = wk (TR⁻ e r) d
  TR⁻ e (ll h) = ll (λ n → TR⁻ e (h n))
  TR⁻ e (nodeR {d = d} {q = q} {f = f} {p = p} {g = g} lv h) =
    nodeR (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) lv) (λ y a r →
      subst (λ w → J _ (L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w)))) (g a))
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a (Back.back⁻ᴿ (ST d p) q e r))))
  TR⁻ (L.s≅ e) (ur r) = ur (TR⁻ e r)
  TR⁻ (L.l≅ h) (ul n r) = ul n (TR⁻ (h n) r)
  TR⁻ e (psh r) = psh (TR⁻ e r)

  TR⁺ : ∀ {a b} (e : a ≅ᴵ b) {j d} {Γ : Ctx ℓ {j} d} {y : L.Ordᶜ a} {η} → J Γ y η → J Γ (L.tr e y) η
  TR⁺ e zr = zr
  TR⁺ e (pop r) = pop (TR⁺ e r)
  TR⁺ e (ss r) = ss (TR⁺ e r)
  TR⁺ e (wk r d) = wk (TR⁺ e r) d
  TR⁺ e (ll h) = ll (λ n → TR⁺ e (h n))
  TR⁺ e (nodeR {d = d} {q = q} {f = f} {p = p} {g = g} lv h) =
    nodeR (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) lv) (λ y a r →
      subst (λ w → J _ (L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w)))) (g a))
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a (Back.backᴿ (ST d p) q e r))))
  TR⁺ (L.s≅ e) (ur r) = ur (TR⁺ e r)
  TR⁺ (L.l≅ h) (ul n r) = ul n (TR⁺ (h n) r)
  TR⁺ e (psh r) = psh (TR⁺ e r)

trRel : ∀ ℓ → TRC (λ {k} → Rel ℓ {k})
trSl  : ∀ ℓ {j} (d : Dc ℓ j) (p : Pos j) → TRC (λ {i} → SlOf ℓ d p {i})
trP   : ∀ ℓ (p : Pos ℓ) → TRC (λ {i} → RelP ℓ p {i})
trP⁼  : ∀ a (p : Pos⁼ a) → TRC (λ {i} → RelP⁼ a p {i})

trRel ℓ = record { tr⁻ᴿ = λ e r → TRJ.TR⁻ ℓ (SlOf ℓ) (trSl ℓ) e r ; trᴿ = λ e r → TRJ.TR⁺ ℓ (SlOf ℓ) (trSl ℓ) e r }

trSl ℓ [] p = trP ℓ p
trSl zero (() ∷ d) p
trSl (nd s h) (c ∷ d) p = trSl (h c) d p
trP (nd s h) (inj₂ (c , t)) = trP⁼ (h c) t
trP (nd (sΩ k) h) (inj₁ t) = trP⁼ k t
trP⁼ a (inj₁ _) = trRel a
trP⁼ a (inj₂ p) = trP a p
emb : ∀ {s h} (t₀ : Tr (nd s h)) (c : Ch s) {j} {d : Dc (h c) j} {Δ : Ctx (h c) d} {k} {X : L.Ordᶜ k} {y : Tr j}
  → Sim.J (h c) (SlOf (h c)) Δ X y → Sim.J (nd s h) (SlOf (nd s h)) (fr t₀ c Δ) X y
emb t₀ c zr = pop {Γ = []} zr
emb t₀ c (pop r) = pop (emb t₀ c r)
emb t₀ c (ss r) = ss (emb t₀ c r)
emb t₀ c (wk r e) = wk (emb t₀ c r) e
emb t₀ c (ll h) = ll (λ n → emb t₀ c (h n))
emb t₀ c (nodeR lv h) = nodeR lv (λ y z sl → emb t₀ c (h y z sl))
emb t₀ c (ur r) = ur (emb t₀ c r)
emb t₀ c (ul n r) = ul n (emb t₀ c r)
emb t₀ c (psh r) = psh (emb t₀ c r)
module Add (ℓ : LF) (Sl : ∀ {j} → Dc ℓ j → (p : Pos j) → ∀ {i} → L.Ordᶜ i → Br j p → Set) where
  open Sim ℓ Sl using (J)

  pre : Tr ℓ → ∀ {j} {d : Dc ℓ j} → Ctx ℓ d → Ctx ℓ d
  pre b []         = []
  pre b (fr t c Γ) = fr (b + t) c Γ

  prey : Tr ℓ → ∀ {j} {d : Dc ℓ j} → Ctx ℓ d → Tr j → Tr j
  prey b []         y = b + y
  prey b (fr t c Γ) y = y

  rpad : ∀ {k} {X : L.Ordᶜ k} {b : Tr ℓ} → J [] X b → (y : Tr ℓ) → J [] X (b + y)
  rpad r zero       = r
  rpad r (suc y)    = wk (rpad r y) ◃s
  rpad r (lim f a)    = wk (rpad r (f zero)) (◃l zero)
  rpad r (Ω p g)      = wk (rpad r (g (fromBr ℓ p zero))) ◃w
  rpad r (up t c y e) = psh (pop {Γ = []} (rpad r t))

  addL : ∀ {ka} {Xa : L.Ordᶜ ka} {b : Tr ℓ} → J [] Xa b
    → ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {Xb : L.Ordᶜ k} {y : Tr j} → J Γ Xb y → (σ : L.Simᴵ k ka)
    → J (pre b Γ) (L.add Xa σ Xb) (prey b Γ y)
  addL sa zr σ = rpad sa _
  addL sa (pop {Γ = []} r) σ = pop {Γ = []} (addL sa r σ)
  addL sa (pop {Γ = fr t′ c′ Γ₁} r) σ = pop (addL sa r σ)
  addL sa {Γ = []} (ss r) σ = ss (addL sa r σ)
  addL sa {Γ = fr t c Γ} (ss r) σ = ss (addL sa r σ)
  addL {b = b} sa {Γ = []} (wk r e) σ = wk (addL sa r σ) (+-mono b e)
  addL sa {Γ = fr t c Γ} (wk r e) σ = wk (addL sa r σ) e
  addL sa {Γ = []} (ll h) σ = ll (λ n → addL sa (h n) σ)
  addL sa {Γ = fr t c Γ} (ll h) σ = ll (λ n → addL sa (h n) σ)
  addL {Xa = Xa} {b = b} sa {Γ = []} (nodeR {q = q} {f = f} {g = g} c h) σ =
    nodeR c (λ y₀ c₀ sl → subst (λ w → J [] (L.add Xa σ (f (L.into (L.<→◃ q) w))) (b + g c₀))
      (sym (L.out-into (L.<→◃ (σ q)) y₀)) (addL sa (h y₀ c₀ sl) σ))
  addL {Xa = Xa} {b = b} sa {Γ = fr t c′ Γ} (nodeR {q = q} {f = f} {g = g} c h) σ =
    nodeR c (λ y₀ c₀ sl → subst (λ w → J (fr (b + t) c′ Γ) (L.add Xa σ (f (L.into (L.<→◃ q) w))) (g c₀))
      (sym (L.out-into (L.<→◃ (σ q)) y₀)) (addL sa (h y₀ c₀ sl) σ))
  addL sa (ur r) σ = addL sa r (λ q → σ (L.suc q))
  addL sa (ul n r) σ = addL sa r (λ q → σ (L.lim n q))
  addL sa (psh {Γ = []} r) σ = psh (addL sa r σ)
  addL sa (psh {Γ = fr t′ c′ Γ₁} r) σ = psh (addL sa r σ)

  cumR : (a : Tr ℓ) → ∀ {j d} {Γ : Ctx ℓ {j} d} {k} {X : L.Ordᶜ k} {y : Tr j} → J Γ X y
    → J (pre a Γ) X (prey a Γ y)
  cumR a zr = zr
  cumR a (pop {Γ = []} r) = pop {Γ = []} (cumR a r)
  cumR a (pop {Γ = fr t′ c′ Γ₁} r) = pop (cumR a r)
  cumR a {Γ = []} (ss r) = ss (cumR a r)
  cumR a {Γ = fr t c Γ} (ss r) = ss (cumR a r)
  cumR a {Γ = []} (wk r e) = wk (cumR a r) (+-mono a e)
  cumR a {Γ = fr t c Γ} (wk r e) = wk (cumR a r) e
  cumR a {Γ = []} (ll h) = ll (λ n → cumR a (h n))
  cumR a {Γ = fr t c Γ} (ll h) = ll (λ n → cumR a (h n))
  cumR a {Γ = []} (nodeR c h) = nodeR c (λ y₀ c₀ sl → cumR a (h y₀ c₀ sl))
  cumR a {Γ = fr t c′ Γ} (nodeR c h) = nodeR c (λ y₀ c₀ sl → cumR a (h y₀ c₀ sl))
  cumR a {Γ = []} (ur r) = ur (cumR a r)
  cumR a {Γ = fr t c Γ} (ur r) = ur (cumR a r)
  cumR a {Γ = []} (ul n r) = ul n (cumR a r)
  cumR a {Γ = fr t c Γ} (ul n r) = ul n (cumR a r)
  cumR a (psh {Γ = []} r) = psh (cumR a r)
  cumR a (psh {Γ = fr t′ c′ Γ₁} r) = psh (cumR a r)

  nextL : ∀ {k} {X : L.Ordᶜ k} {b : Tr ℓ} (nz : ℓ ⊢ zero ◃ b) → J [] X b
    → J [] (L.lim (iterᴸ (X L.+_) L.zero)) (proj₁ (next⁺ (b , nz)))
  nextL {X = X} {b = b} nz sa = ll λ where
      zero    → zr
      (suc n) → wk (go n) (◃l n)
    where
    go : ∀ n → J [] (iterᴸ (X L.+_) L.zero (suc n)) (iter (b +_) b n)
    go zero    = sa
    go (suc n) = addL sa (go n) (λ q → q)

  inCum : (F : ℕ → Tr ℓ) (nz : (n : ℕ) → ℓ ⊢ zero ◃ F n) (n : ℕ) → ∀ {k} {X : L.Ordᶜ k}
    → J [] X (F n) → J [] X (proj₁ (limc⁺ (λ n → F n , nz n)))
  inCum F nz n r = wk (go n r) (◃l n)
    where
    go : ∀ n {k} {X : L.Ordᶜ k} → J [] X (F n) → J [] X (cum F n)
    go zero    r = r
    go (suc n) r = cumR (cum F n) r

import OCF.Lean.YiKVRel as K
import OCF.Align.Value as V
read0 : ∀ {j} → Dc zero j → Tr j → L.Ordᶜ L.zero
read0 [] y = K.readRW y
read0 (() ∷ d) y
r0 : ∀ {j} {d : Dc zero j} {Γ : Ctx zero d} {k} {X : L.Ordᶜ k} {y : Tr j}
  → Sim.J zero (SlOf zero) Γ X y → X V.≼ read0 d y
r0 zr = V.z≼
r0 (pop {d = []} {c = ()} r)
r0 (pop {d = () ∷ _} r)
r0 {d = []} (ss r) = V.s≼s (r0 r)
r0 {d = []} (wk r e) = V.≼-trans (r0 r) (K.◃→≼ e)
r0 {d = []} (ll h) = V.l≼ (λ n → r0 (h n))
r0 {d = []} (nodeR {p = ()} c h)
r0 {d = []} (ur r) = V.u≼ (r0 r)
r0 {d = []} (ul n r) = V.u≼ (r0 r)
r0 {d = []} (psh {c = ()} r)
r0 {d = () ∷ _} r
r→≼ : ∀ {k} {X : L.Ordᶜ k} {y : Tr zero} → Rel zero X y → X V.≼ K.readRW y
r→≼ r = r0 r
```
