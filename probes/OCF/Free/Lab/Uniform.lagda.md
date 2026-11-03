# Uniform (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform](../../Align/Uniform.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Lab.Level
```

```agda
open Ord-Ord using (iter)
open Restr
```

## §0 记号与几条 $\cong$ 的小引理

```agda
≅-reflˡ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ≅ a
≅-reflˡ e = ≅-trans e (≅-sym e)

≅-reflʳ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → b ≅ b
≅-reflʳ e = ≅-trans (≅-sym e) e

self-tr : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → x ≅ x → tr e x ≅ tr e x
self-tr e d = ≅-reflˡ (tr-≅ e d)

self-tr⁻ : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → x ≅ x → tr⁻ e x ≅ tr⁻ e x
self-tr⁻ e d = ≅-reflˡ (tr⁻-≅ e d)

s-inv : ∀ {k k′} {a : Ordᶜ k} {b : Ordᶜ k′} → suc a ≅ suc b → a ≅ b
s-inv (s≅ e) = e

l-inv : ∀ {k k′} {f : ℕ → Ordᶜ k} {g : ℕ → Ordᶜ k′} → lim f ≅ lim g → ∀ n → f n ≅ g n
l-inv (l≅ h) = h

i-resp : ∀ {k k′ j} {p : j <ᴵ k} {f : U j (<→◃ p) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ p f ≅ b →
         ∀ {z z′ : Ordᶜ j} → z ≅ z′ → f (into (<→◃ p) z) ≅ f (into (<→◃ p) z′)
i-resp {p = p} (lᵢ≅ e h) {z} {z′} d =
  ≅-trans (h z (tr e z′) (≅→R (<→◃ p) (≅-tr e d)))
          (≅-sym (h z′ (tr e z′) (≅→R (<→◃ p) (≅-tr e (≅-reflʳ d)))))
i-resp (upʳ {r = zero} e)   = i-resp e
i-resp (upʳ {r = self n} e) = i-resp e

u-inv : ∀ {k ℓ ℓ′} (r : k ◃₁ ℓ) {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → up r x ≅ b → out (◃₁→◃ r) x ≅ b
u-inv zero     (upˡ e)              = e
u-inv zero     (upʳ {r = zero} e)   = upʳ (u-inv zero e)
u-inv zero     (upʳ {r = self n} e) = upʳ (u-inv zero e)
u-inv (self m) (upˡ e)              = e
u-inv (self m) (upʳ {r = zero} e)   = upʳ (u-inv (self m) e)
u-inv (self m) (upʳ {r = self n} e) = upʳ (u-inv (self m) e)

u-refl : ∀ {k ℓ} (r : k ◃₁ ℓ) {x : U k (◃₁→◃ r)} → up r x ≅ up r x → out (◃₁→◃ r) x ≅ out (◃₁→◃ r) x
u-refl r e = ≅-reflˡ (u-inv r e)
```

## §1 观测与观测前序 (SafePath §4, 加上搬运)

```agda
data Obs : Ordᴵ → Set where
  idO  : Obs zero
  ψ⁰o  : ∀ {k} → Obs zero → Obs k
  ψo   : ∀ {i k ℓ} → Obs i → i <ᴵ ℓ → Simᴵ k ℓ → Obs k
  addo : ∀ {k ℓ} → Obs ℓ → Ordᶜ ℓ → Simᴵ k ℓ → Obs k
  tro  : ∀ {a b} → Obs b → a ≅ᴵ b → Obs a
  tr⁻o : ∀ {a b} → Obs a → a ≅ᴵ b → Obs b

run : ∀ {k} → Obs k → Ordᶜ k → Ordᶜ zero
run idO          x = x
run (ψ⁰o O)      x = run O (ψ⁰ x)
run (ψo O p σ)   x = run O (ψ p σ x)
run (addo O a σ) x = run O (add a σ x)
run (tro O e)    x = run O (tr e x)
run (tr⁻o O e)   x = run O (tr⁻ e x)

infix 4 _≈ᵒ_ _⊑ᵒ_
data _≈ᵒ_ : ∀ {k k′} → Obs k → Obs k′ → Set where
  idO  : idO ≈ᵒ idO
  ψ⁰o  : ∀ {k k′} {O O′ : Obs zero} → O ≈ᵒ O′ → ψ⁰o {k} O ≈ᵒ ψ⁰o {k′} O′
  ψo   : ∀ {i k k′ ℓ ℓ′} {O O′ : Obs i} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → ψo O p σ ≈ᵒ ψo O′ p′ σ′
  addo : ∀ {k k′ ℓ ℓ′} {O : Obs ℓ} {O′ : Obs ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} →
         O ≈ᵒ O′ → a ≅ a′ → addo O a σ ≈ᵒ addo O′ a′ σ′
  tro  : ∀ {a a′ b b′} {O : Obs b} {O′ : Obs b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} →
         O ≈ᵒ O′ → tro O e ≈ᵒ tro O′ e′
  tr⁻o : ∀ {a a′ b b′} {O : Obs a} {O′ : Obs a′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} →
         O ≈ᵒ O′ → tr⁻o O e ≈ᵒ tr⁻o O′ e′

≈ᵒ-reflʳ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → O′ ≈ᵒ O′
≈ᵒ-reflʳ idO        = idO
≈ᵒ-reflʳ (ψ⁰o o)    = ψ⁰o (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (ψo o)     = ψo (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (addo o e) = addo (≈ᵒ-reflʳ o) (≅-reflʳ e)
≈ᵒ-reflʳ (tro o)    = tro (≈ᵒ-reflʳ o)
≈ᵒ-reflʳ (tr⁻o o)   = tr⁻o (≈ᵒ-reflʳ o)

run-≅ : ∀ {k k′} {O : Obs k} {O′ : Obs k′} {x : Ordᶜ k} {x′ : Ordᶜ k′} → O ≈ᵒ O′ → x ≅ x′ → run O x ≅ run O′ x′
run-≅ idO        d = d
run-≅ (ψ⁰o o)    d = run-≅ o (ψ⁰-≅ d)
run-≅ (ψo o)     d = run-≅ o (ψ-≅ (≅ᴵ-refl _) d)
run-≅ (addo o a) d = run-≅ o (add-≅ a d)
run-≅ (tro {e = e} {e′ = e′} o)  d = run-≅ o (tr-≅ e (≅-tr e′ d))
run-≅ (tr⁻o {e = e} {e′ = e′} o) d = run-≅ o (tr⁻-≅ e (≅-tr⁻ e′ d))

_⊑ᵒ_ : ∀ {k k′} → Ordᶜ k → Ordᶜ k′ → Set
_⊑ᵒ_ {k} {k′} x y = ∀ {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → run O x ⊑ run O′ y

≅→⊑ᵒ : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ≅ y → x ⊑ᵒ y
≅→⊑ᵒ e o = ≅→⊑ (run-≅ o e)

⊑ᵒ-≅ʳ : ∀ {k k′} {x : Ordᶜ k} {y y′ : Ordᶜ k′} → x ⊑ᵒ y → y ≅ y′ → x ⊑ᵒ y′
⊑ᵒ-≅ʳ h e o = ⊑-trans (h o) (≅→⊑ (run-≅ (≈ᵒ-reflʳ o) e))
```

## §2 同余

```agda
ψ-cong : ∀ {i k k′ ℓ ℓ′} {p : i <ᴵ ℓ} {p′ : i <ᴵ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordᶜ k} {y : Ordᶜ k′} →
         x ⊑ᵒ y → ψ p σ x ⊑ᵒ ψ p′ σ′ y
ψ-cong h o = h (ψo o)

ψ⁰-cong : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → ψ⁰ x ⊑ᵒ ψ⁰ y
ψ⁰-cong h o = h (ψ⁰o o)

add-cong : ∀ {k k′ ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ} {σ′ : Simᴵ k′ ℓ′} {x : Ordᶜ k} {y : Ordᶜ k′} →
           a ≅ a′ → x ⊑ᵒ y → add a σ x ⊑ᵒ add a′ σ′ y
add-cong e h o = h (addo o e)

tr-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordᶜ a} {y : Ordᶜ a′} → x ⊑ᵒ y → tr e x ⊑ᵒ tr e′ y
tr-cong h o = h (tro o)

tr⁻-cong : ∀ {a a′ b b′} {e : a ≅ᴵ b} {e′ : a′ ≅ᴵ b′} {x : Ordᶜ b} {y : Ordᶜ b′} → x ⊑ᵒ y → tr⁻ e x ⊑ᵒ tr⁻ e′ y
tr⁻-cong h o = h (tr⁻o o)

up-l : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {y : Ordᶜ ℓ′} → out (◃₁→◃ r) x ⊑ᵒ y → up r x ⊑ᵒ y
up-l {r = zero}   h (ψ⁰o o)    = h (ψ⁰o o)
up-l {r = zero}   h (ψo o)     = h (ψo o)
up-l {r = zero}   h (addo o e) = h (addo o e)
up-l {r = zero}   h (tro {e = s≅ e} o)  = up-l {r = zero} (λ o′ → h (tro o′)) o
up-l {r = zero}   h (tr⁻o {e = s≅ e} o) = up-l {r = zero} (λ o′ → h (tr⁻o o′)) o
up-l {r = self n} h (ψ⁰o o)    = h (ψ⁰o o)
up-l {r = self n} h (ψo o)     = h (ψo o)
up-l {r = self n} h (addo o e) = h (addo o e)
up-l {r = self n} h (tro {e = l≅ f} o)  = up-l {r = self n} (λ o′ → h (tro o′)) o
up-l {r = self n} h (tr⁻o {e = l≅ f} o) = up-l {r = self n} (λ o′ → h (tr⁻o o′)) o

up-r : ∀ {k ℓ ℓ′} {r : k ◃₁ ℓ} {y : U k (◃₁→◃ r)} {x : Ordᶜ ℓ′} → x ⊑ᵒ out (◃₁→◃ r) y → x ⊑ᵒ up r y
up-r {r = zero}   h (ψ⁰o o)    = h (ψ⁰o o)
up-r {r = zero}   h (ψo o)     = h (ψo o)
up-r {r = zero}   h (addo o e) = h (addo o e)
up-r {r = zero}   h (tro {e′ = s≅ e} o)  = up-r {r = zero} (λ o′ → h (tro o′)) o
up-r {r = zero}   h (tr⁻o {e′ = s≅ e} o) = up-r {r = zero} (λ o′ → h (tr⁻o o′)) o
up-r {r = self n} h (ψ⁰o o)    = h (ψ⁰o o)
up-r {r = self n} h (ψo o)     = h (ψo o)
up-r {r = self n} h (addo o e) = h (addo o e)
up-r {r = self n} h (tro {e′ = l≅ f} o)  = up-r {r = self n} (λ o′ → h (tro o′)) o
up-r {r = self n} h (tr⁻o {e′ = l≅ f} o) = up-r {r = self n} (λ o′ → h (tr⁻o o′)) o
```

## §3 上界引理

```agda
lim-r : ∀ {k k′} {x : Ordᶜ k} {h : ℕ → Ordᶜ k′} n → x ⊑ᵒ h n → x ⊑ᵒ lim h
lim-r n p idO        = ⊑-lim n (p idO)
lim-r n p (ψ⁰o o)    = lim-r n (ψ⁰-cong p) o
lim-r n p (ψo o)     = lim-r n (ψ-cong p) o
lim-r n p (addo o a) = lim-r n (add-cong a p) o
lim-r n p (tro o)    = lim-r n (tr-cong p) o
lim-r n p (tr⁻o o)   = lim-r n (tr⁻-cong p) o

lim-l : ∀ {k k′} {h : ℕ → Ordᶜ k} {y : Ordᶜ k′} → (∀ n → h n ⊑ᵒ y) → lim h ⊑ᵒ y
lim-l K idO        = lim-⊑ (λ n → K n idO)
lim-l K (ψ⁰o o)    = lim-l (λ n o′ → K n (ψ⁰o o′)) o
lim-l K (ψo o)     = lim-l (λ n o′ → K n (ψo o′)) o
lim-l K (addo o a) = lim-l (λ n o′ → K n (addo o′ a)) o
lim-l K (tro o)    = lim-l (λ n o′ → K n (tro o′)) o
lim-l K (tr⁻o o)   = lim-l (λ n o′ → K n (tr⁻o o′)) o

suc-r : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → x ⊑ᵒ y → x ⊑ᵒ suc y
suc-r p idO        = λ h → ≺s (p idO h)
suc-r p (ψ⁰o o)    = lim-r 1 (ψ⁰-cong p) o
suc-r p (ψo o)     = lim-r 1 (ψ-cong p) o
suc-r p (addo o a) = suc-r (add-cong a p) o
suc-r p (tro o)    = suc-r (tr-cong p) o
suc-r p (tr⁻o o)   = suc-r (tr⁻-cong p) o
```

```agda
limᵢ-r : ∀ {k k′ j} {x : Ordᶜ k} {q : j <ᴵ k′} {g : U j (<→◃ q) → Ordᶜ k′} →
         (∀ z → z ≅ Ω j → x ⊑ᵒ g (into (<→◃ q) z)) → x ⊑ᵒ limᵢ q g
limᵢ-r {q = ()} H idO
limᵢ-r {j = j} H (ψ⁰o o) = lim-r 0 (ψ⁰-cong (H (Ω j) (Ω-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (ψo {p = p} {p′ = p′} {σ = σ} {σ′ = σ′} o) with <ᴵ-dec (σ′ q) p′
... | injᵃ (via e r) = limᵢ-r (λ z d →
        subst (λ u → ψ p σ x ⊑ᵒ ψ p′ σ′ (g (into (<→◃ q) (tr⁻ e u)))) (sym (out-into (<→◃ r) z))
              (ψ-cong (H (tr⁻ e z) (tr⁻-≅ e (≅-trans d (Ω-≅ (≅ᴵ-sym e))))))) o
... | injᵇ _ = lim-r 0 (ψ-cong (H (Ω j) (Ω-refl j))) o
... | injᶜ _ = lim-r 0 (ψ-cong (H (Ω j) (Ω-refl j))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (addo {a = a} {a′ = a′} {σ = σ} {σ′ = σ′} o ea) = limᵢ-r (λ z d →
  subst (λ u → add a σ x ⊑ᵒ add a′ σ′ (g (into (<→◃ q) u))) (sym (out-into (<→◃ (σ′ q)) z))
        (add-cong ea (H z d))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tro {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr e x ⊑ᵒ tr e′ (g (into (<→◃ q) (back (res q e′) u)))) (sym (out-into (<→◃ (lt (res q e′))) z))
        (tr-cong (H (back (res q e′) z) (≅-trans (back-≅ q e′ d) (Ω-≅ (≅ᴵ-sym (eq (res q e′)))))))) o
limᵢ-r {j = j} {x = x} {q = q} {g = g} H (tr⁻o {e = e} {e′ = e′} o) = limᵢ-r (λ z d →
  subst (λ u → tr⁻ e x ⊑ᵒ tr⁻ e′ (g (into (<→◃ q) (back (res⁻ q e′) u)))) (sym (out-into (<→◃ (lt (res⁻ q e′))) z))
        (tr⁻-cong (H (back (res⁻ q e′) z) (≅-trans (back⁻-≅ q e′ d) (Ω-≅ (≅ᴵ-sym (eq (res⁻ q e′)))))))) o
```

## §4 链的起点 $\Omega_j\sqsubseteq^\mathsf{o}\psi_q z$ (SafePath §7)

```agda
B1 : ∀ {j ℓ k} {q : j <ᴵ ℓ} {σ : Simᴵ k ℓ} (z : Ordᶜ k) → z ≅ z → Ω j ⊑ᵒ ψ q σ z
B1 zero e = ≅→⊑ᵒ (Ω-refl _)
B1 {q = q} {σ = σ} (suc a) e = lim-r 1 (B1 {q = q} {σ = σ} a (s-inv e))
B1 {q = q} {σ = σ} (lim h) e = lim-r 0 (B1 {q = q} {σ = σ} (h 0) (l-inv e 0))
B1 {j = j} {q = q} {σ = σ} (limᵢ {i = j′} q′ g) e with <ᴵ-dec (σ q′) q
... | injᵃ (via e₁ r) = limᵢ-r (λ z d →
        subst (λ u → Ω j ⊑ᵒ ψ q σ (g (into (<→◃ q′) (tr⁻ e₁ u)))) (sym (out-into (<→◃ r) z))
              (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (tr⁻ e₁ z))) (i-resp e (self-tr⁻ e₁ (≅-reflˡ d)))))
... | injᵇ _ = lim-r 0 (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
... | injᶜ _ = lim-r 0 (B1 {q = q} {σ = σ} (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
B1 (up zero x) e     = B1 x (u-refl zero e)
B1 (up (self n) x) e = B1 x (u-refl (self n) e)

B1⁰ : ∀ {k} (z : Ordᶜ k) → z ≅ z → Ω zero ⊑ᵒ ψ⁰ z
B1⁰ zero e    = ≅→⊑ᵒ (Ω-refl zero)
B1⁰ (suc a) e = lim-r 1 (B1⁰ a (s-inv e))
B1⁰ (lim h) e = lim-r 0 (B1⁰ (h 0) (l-inv e 0))
B1⁰ (limᵢ {i = j′} q′ g) e = lim-r 0 (B1⁰ (g (into (<→◃ q′) (Ω j′))) (i-resp e (Ω-refl j′)))
B1⁰ (up zero x) e     = B1⁰ x (u-refl zero e)
B1⁰ (up (self n) x) e = B1⁰ x (u-refl (self n) e)

add-r : ∀ {k ℓ ℓ′} {a : Ordᶜ ℓ} {a′ : Ordᶜ ℓ′} {σ : Simᴵ k ℓ′} (b : Ordᶜ k) → a ≅ a′ → b ≅ b → a ⊑ᵒ add a′ σ b
add-r zero ea eb = ≅→⊑ᵒ ea
add-r {σ = σ} (suc b) ea eb = suc-r (add-r {σ = σ} b ea (s-inv eb))
add-r {σ = σ} (lim h) ea eb = lim-r 0 (add-r {σ = σ} (h 0) ea (l-inv eb 0))
add-r {a = a} {a′ = a′} {σ = σ} (limᵢ q g) ea eb = limᵢ-r (λ z d →
  subst (λ u → a ⊑ᵒ add a′ σ (g (into (<→◃ q) u))) (sym (out-into (<→◃ (σ q)) z))
        (add-r {σ = σ} (g (into (<→◃ q) z)) ea (i-resp eb (≅-reflˡ d))))
add-r (up zero x)     ea eb = add-r x ea (u-refl zero eb)
add-r (up (self n) x) ea eb = add-r x ea (u-refl (self n) eb)

zero-l : ∀ {k k′} {y : Ordᶜ k′} → y ≅ y → 𝟎 {k} ⊑ᵒ y
zero-l ey idO         = λ ()
zero-l ey (ψ⁰o o)     = B1⁰ _ ey o
zero-l ey (ψo o)      = B1 _ ey o
zero-l ey (addo o ea) = add-r _ ea ey o
zero-l ey (tro {e′ = e′} o)  = zero-l (self-tr e′ ey) o
zero-l ey (tr⁻o {e′ = e′} o) = zero-l (self-tr⁻ e′ ey) o
```

## §5 $\Omega$ 的单调性 (观测版)

```agda
Ω0 : ∀ b → Ω zero ⊑ᵒ Ω b
Ω0 zero      = ≅→⊑ᵒ (Ω-refl zero)
Ω0 (suc b)   = limᵢ-r (λ z d → up-r (⊑ᵒ-≅ʳ (Ω0 b) (≅-sym d)))
Ω0 (lim g s) = lim-r 0 (up-r (Ω0 (g 0)))

Ω< : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → Ω (suc a) ⊑ᵒ Ω b
Ω< e zero      = ≅→⊑ᵒ (Ω-≅ (s≅ e))
Ω< e (suc q)   = limᵢ-r (λ z d → up-r (⊑ᵒ-≅ʳ (Ω< e q) (≅-sym d)))
Ω< e (lim n q) = lim-r n (up-r (Ω< e q))

Ω-monoᵒ : ∀ {a b} → a ⊑ᴵ b → Ω a ⊑ᵒ Ω b
Ω-monoᵒ {b = b} z⊑ = Ω0 b
Ω-monoᵒ (s⊑ e q)   = Ω< e q
Ω-monoᵒ (l⊑ k)     = lim-l (λ n → up-l (Ω-monoᵒ (k n)))
```

## §6 遗传好树 `Good` 与搬运

```agda
module _ (ℓ : Ordᴵ) (G< : (i : Ordᴵ) (r : i ◃ ℓ) → U i r → Set) where
  data Good₊ : Ordᶜ ℓ → Set where
    gz : Good₊ zero
    gs : ∀ {a} → Good₊ a → Good₊ (suc a)
    gl : ∀ {h : ℕ → Ordᶜ ℓ} → (∀ n → Good₊ (h n)) → (∀ n → h n ⊑ᵒ h (suc n)) → Good₊ (lim h)
    gi : ∀ {j} {p : j <ᴵ ℓ} {f : U j (<→◃ p) → Ordᶜ ℓ} →
         (∀ (z : Ordᶜ j) → z ≅ z → G< j (<→◃ p) (into (<→◃ p) z) → Good₊ (f (into (<→◃ p) z))) →
         (∀ {z z′ : Ordᶜ j} → z ⊑ᵒ z′ → f (into (<→◃ p) z) ⊑ᵒ f (into (<→◃ p) z′)) →
         Good₊ (limᵢ p f)
    gu : ∀ {k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → G< k (◃₁→◃ r) x → Good₊ (up r x)

Gd : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → U i r → Set
Gd i zero         x = Good₊ i Gd x
Gd i (suc r)      x = Gd i r x
Gd _ (self {f} n) x = Good₊ (f n) Gd x
Gd i (lim n r)    x = Gd i r x

Good : ∀ {ℓ} → Ordᶜ ℓ → Set
Good {ℓ} = Good₊ ℓ Gd

Gd→Good : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Gd i r (into r x) → Good x
Gd→Good zero      g = g
Gd→Good (suc r)   g = Gd→Good r g
Gd→Good (self n)  g = g
Gd→Good (lim n r) g = Gd→Good r g

Good→Gd : ∀ {i ℓ} (r : i ◃ ℓ) {x : Ordᶜ i} → Good x → Gd i r (into r x)
Good→Gd zero      g = g
Good→Gd (suc r)   g = Good→Gd r g
Good→Gd (self n)  g = g
Good→Gd (lim n r) g = Good→Gd r g

Gd-conv : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) (r′ : i ◃ ℓ′) {x : Ordᶜ i} → Gd i r (into r x) → Gd i r′ (into r′ x)
Gd-conv r r′ g = Good→Gd r′ (Gd→Good r g)
```

```agda
back-mono : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u u′ : Ordᶜ (rep (res q e))} → u ⊑ᵒ u′ → back (res q e) u ⊑ᵒ back (res q e) u′
back-mono zero      (s≅ e) h = tr⁻-cong h
back-mono (suc q)   (s≅ e) h = back-mono q e h
back-mono (lim n q) (l≅ f) h = back-mono q (f n) h

back⁻-mono : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u u′ : Ordᶜ (rep (res⁻ q e))} → u ⊑ᵒ u′ → back (res⁻ q e) u ⊑ᵒ back (res⁻ q e) u′
back⁻-mono zero      (s≅ e) h = tr-cong h
back⁻-mono (suc q)   (s≅ e) h = back⁻-mono q e h
back⁻-mono (lim n q) (l≅ f) h = back⁻-mono q (f n) h

self-back : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → u ≅ u → back (res q e) u ≅ back (res q e) u
self-back q e d = ≅-reflˡ (back-≅ q e d)

self-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → u ≅ u → back (res⁻ q e) u ≅ back (res⁻ q e) u
self-back⁻ q e d = ≅-reflˡ (back⁻-≅ q e d)

Good-tr    : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ a} → Good x → Good (tr e x)
Good-tr⁻   : ∀ {a b} (e : a ≅ᴵ b) {x : Ordᶜ b} → Good x → Good (tr⁻ e x)
Good-back  : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} → Good u → Good (back (res q e) u)
Good-back⁻ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} → Good u → Good (back (res⁻ q e) u)

Good-tr e gz         = gz
Good-tr e (gs g)     = gs (Good-tr e g)
Good-tr e (gl hg st) = gl (λ n → Good-tr e (hg n)) (λ n → tr-cong (st n))
Good-tr e (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ w → Good (tr e (f (into (<→◃ q) (back (res q e) w))))) (sym (out-into (<→◃ (lt (res q e))) z))
                    (Good-tr e (hb (back (res q e) z) (self-back q e ez)
                                   (Good→Gd (<→◃ q) (Good-back q e (Gd→Good (<→◃ (lt (res q e))) g))))))
  (λ {z} {z′} h → subst₂ (λ w w′ → tr e (f (into (<→◃ q) (back (res q e) w))) ⊑ᵒ tr e (f (into (<→◃ q) (back (res q e) w′))))
                         (sym (out-into (<→◃ (lt (res q e))) z)) (sym (out-into (<→◃ (lt (res q e))) z′))
                         (tr-cong (hm (back-mono q e h))))
Good-tr (s≅ e) (gu {r = zero} g)   = gu (Good-tr e g)
Good-tr (l≅ f) (gu {r = self n} g) = gu (Good-tr (f n) g)

Good-tr⁻ e gz         = gz
Good-tr⁻ e (gs g)     = gs (Good-tr⁻ e g)
Good-tr⁻ e (gl hg st) = gl (λ n → Good-tr⁻ e (hg n)) (λ n → tr⁻-cong (st n))
Good-tr⁻ e (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ w → Good (tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))))) (sym (out-into (<→◃ (lt (res⁻ q e))) z))
                    (Good-tr⁻ e (hb (back (res⁻ q e) z) (self-back⁻ q e ez)
                                    (Good→Gd (<→◃ q) (Good-back⁻ q e (Gd→Good (<→◃ (lt (res⁻ q e))) g))))))
  (λ {z} {z′} h → subst₂ (λ w w′ → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))) ⊑ᵒ tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w′))))
                         (sym (out-into (<→◃ (lt (res⁻ q e))) z)) (sym (out-into (<→◃ (lt (res⁻ q e))) z′))
                         (tr⁻-cong (hm (back⁻-mono q e h))))
Good-tr⁻ (s≅ e) (gu {r = zero} g)   = gu (Good-tr⁻ e g)
Good-tr⁻ (l≅ f) (gu {r = self n} g) = gu (Good-tr⁻ (f n) g)

Good-back zero      (s≅ e) g = Good-tr⁻ e g
Good-back (suc q)   (s≅ e) g = Good-back q e g
Good-back (lim n q) (l≅ f) g = Good-back q (f n) g

Good-back⁻ zero      (s≅ e) g = Good-tr e g
Good-back⁻ (suc q)   (s≅ e) g = Good-back⁻ q e g
Good-back⁻ (lim n q) (l≅ f) g = Good-back⁻ q (f n) g
```

## §7 封闭性

```agda
Good-Ω : ∀ a → Good (Ω a)
Good-Ω zero      = gs gz
Good-Ω (suc c)   = gi (λ z ez g → gu g) (λ h → up-l (up-r h))
Good-Ω (lim g s) = gl (λ n → gu (Good-Ω (g n))) (λ n → up-l (up-r (Ω-monoᵒ (s n))))

Good-add : ∀ {k ℓ} {a : Ordᶜ ℓ} {σ : Simᴵ k ℓ} {b : Ordᶜ k} → Good a → a ≅ a → Good b → Good (add a σ b)
Good-add ga ea gz          = ga
Good-add ga ea (gs g)      = gs (Good-add ga ea g)
Good-add ga ea (gl hg st)  = gl (λ n → Good-add ga ea (hg n)) (λ n → add-cong ea (st n))
Good-add {a = a} {σ = σ} ga ea (gi {p = q} {f = f} hb hm) = gi
  (λ z ez g → subst (λ u → Good (add a σ (f (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) z))
                    (Good-add ga ea (hb z ez (Gd-conv (<→◃ (σ q)) (<→◃ q) g))))
  (λ {z} {z′} h → subst₂ (λ u v → add a σ (f (into (<→◃ q) u)) ⊑ᵒ add a σ (f (into (<→◃ q) v)))
                         (sym (out-into (<→◃ (σ q)) z)) (sym (out-into (<→◃ (σ q)) z′)) (add-cong ea (hm h)))
Good-add ga ea (gu {r = zero} g)   = Good-add ga ea g
Good-add ga ea (gu {r = self n} g) = Good-add ga ea g

Good-iter : ∀ {ℓ} {c : Ordᶜ ℓ} → Good c → c ≅ c → ∀ n → Good (iter (c +_) zero n)
Good-iter gc ec zero    = gz
Good-iter gc ec (suc n) = Good-add gc ec (Good-iter gc ec n)

rule4ᵒ : ∀ {ℓ} {c : Ordᶜ ℓ} → c ≅ c → ∀ n → iter (c +_) zero n ⊑ᵒ iter (c +_) zero (suc n)
rule4ᵒ ec zero    = zero-l ec
rule4ᵒ ec (suc n) = add-cong ec (rule4ᵒ ec n)

chain : ∀ {j k} (q : j <ᴵ k) (f : U j (<→◃ q) → Ordᶜ k) → ℕ → Ordᶜ j
chain {j} q f = iter (λ x → ψ q (λ r → r) (f (into (<→◃ q) x))) (Ω j)

chain-≅ : ∀ {j k k′} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ q f ≅ b → ∀ n → chain q f n ≅ chain q f n
chain-≅ {j} e zero    = Ω-refl j
chain-≅ {j} {q = q} e (suc n) = ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (≅ᴵ-refl j) (i-resp e (chain-≅ e n))

chain-step : ∀ {j k k′} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} {b : Ordᶜ k′} → limᵢ q f ≅ b →
             (∀ {z z′ : Ordᶜ j} → z ⊑ᵒ z′ → f (into (<→◃ q) z) ⊑ᵒ f (into (<→◃ q) z′)) →
             ∀ n → chain q f n ⊑ᵒ chain q f (suc n)
chain-step {j} {q = q} {f = f} e hm zero = B1 {q = q} {σ = λ r → r} (f (into (<→◃ q) (Ω j))) (i-resp e (Ω-refl j))
chain-step e hm (suc n) = ψ-cong (hm (chain-step e hm n))

Good-ψ : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ p σ x)
chain-good : ∀ {j k} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} →
             (∀ (z : Ordᶜ j) → z ≅ z → Gd j (<→◃ q) (into (<→◃ q) z) → Good (f (into (<→◃ q) z))) →
             limᵢ q f ≅ limᵢ q f → ∀ n → Good (chain q f n)
chain-good {j} hb e zero = Good-Ω j
chain-good {q = q} {f = f} hb e (suc n) =
  Good-ψ (hb (chain q f n) (chain-≅ e n) (Good→Gd (<→◃ q) (chain-good hb e n))) (i-resp e (chain-≅ e n))

Good-ψ {i} gz ex = Good-Ω i
Good-ψ {i} {p = p} {σ = σ} (gs {a} g) ex = gl (Good-iter (Good-ψ g ea) eψ) (rule4ᵒ eψ)
  where ea = s-inv ex
        eψ = ψ-≅ {p = p} {σ = σ} {p′ = p} {σ′ = σ} (≅ᴵ-refl i) ea
Good-ψ (gl hg st) ex = gl (λ n → Good-ψ (hg n) (l-inv ex n)) (λ n → ψ-cong (st n))
Good-ψ {p = p} {σ = σ} (gi {j = j} {p = q} {f = f} hb hm) ex with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = gi
  (λ z ez g → subst (λ u → Good (ψ p σ (f (into (<→◃ q) (tr⁻ e u))))) (sym (out-into (<→◃ r) z))
                    (Good-ψ (hb (tr⁻ e z) (self-tr⁻ e ez) (Good→Gd (<→◃ q) (Good-tr⁻ e (Gd→Good (<→◃ r) g))))
                            (i-resp ex (self-tr⁻ e ez))))
  (λ {z} {z′} h → subst₂ (λ u v → ψ p σ (f (into (<→◃ q) (tr⁻ e u))) ⊑ᵒ ψ p σ (f (into (<→◃ q) (tr⁻ e v))))
                         (sym (out-into (<→◃ r) z)) (sym (out-into (<→◃ r) z′)) (ψ-cong (hm (tr⁻-cong h))))
... | injᵇ _ = gl (λ n → Good-ψ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n)))
                                (i-resp ex (chain-≅ ex n)))
                  (λ n → ψ-cong (hm (chain-step ex hm n)))
... | injᶜ _ = gl (λ n → Good-ψ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n)))
                                (i-resp ex (chain-≅ ex n)))
                  (λ n → ψ-cong (hm (chain-step ex hm n)))
Good-ψ (gu {r = zero} g) ex   = Good-ψ g (u-refl zero ex)
Good-ψ (gu {r = self n} g) ex = Good-ψ g (u-refl (self n) ex)

Good-ψ⁰ : ∀ {k} {x : Ordᶜ k} → Good x → x ≅ x → Good (ψ⁰ x)
Good-ψ⁰ gz ex = gs gz
Good-ψ⁰ (gs {a} g) ex = gl (Good-iter (Good-ψ⁰ g ea) (ψ⁰-≅ ea)) (rule4ᵒ (ψ⁰-≅ ea))
  where ea = s-inv ex
Good-ψ⁰ (gl hg st) ex = gl (λ n → Good-ψ⁰ (hg n) (l-inv ex n)) (λ n → ψ⁰-cong (st n))
Good-ψ⁰ (gi {p = q} {f = f} hb hm) ex =
  gl (λ n → Good-ψ⁰ (hb (chain q f n) (chain-≅ ex n) (Good→Gd (<→◃ q) (chain-good hb ex n))) (i-resp ex (chain-≅ ex n)))
     (λ n → ψ⁰-cong (hm (chain-step ex hm n)))
Good-ψ⁰ (gu {r = zero} g) ex   = Good-ψ⁰ g (u-refl zero ex)
Good-ψ⁰ (gu {r = self n} g) ex = Good-ψ⁰ g (u-refl (self n) ex)
```

## §8 第 0 层: 好树遗传步进

```agda
Good→HS : ∀ {x : Ordᶜ zero} → Good x → HS x
Good→HS gz         = hz
Good→HS (gs g)     = hs (Good→HS g)
Good→HS (gl hg st) = hl (λ n → Good→HS (hg n)) (λ n → st n idO)
Good→HS (gi {p = ()} hb hm)
Good→HS (gu {r = ()} g)
```

## §9 一致引理

```agda
Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))
Uniform a = Good→HS (Good-ψ⁰ (Good-Ω a) (Ω-refl a))
```

## §12 结论与边界
