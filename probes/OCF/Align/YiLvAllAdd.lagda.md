# YiLvAll 底座：一般层号上的加法、前缀与 ω 倍

**验收文件，档位：编译定理 (引理)。** 对一切 `M`：`Rel M` 对加法 (`ADDg`)、前缀 (`ABSORB`)、ω 倍 (`SUCC`) 封闭；
加数嵌在低层时值域是变量深度的 `shS`，引理对任意带关系的值域 `RA A` 陈述。槽位结点的引入 `ndA`, `bA` 对槽位递归。
入口 [YiLvAll](YiLvAll.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvAllAdd where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Pre; Low; GdL; Gd)
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiIrrIf using (R)
open import OCF.Align.YiLvFoldAdd using (Alg; shS; rawAlg; add; plus; copies; successor)
open import OCF.Align.YiLvFoldFin using (fin)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩; plus≽; read-copies)
open import OCF.Align.YiLvAllRel
open import OCF.Align.YiLvAllTree using (nodeA)
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open L using (_≅ᴵ_; _<ᴵ_)
open V using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
```

## 1 输出一侧的极限规则，对一切目标层

```agda
out-l : ∀ m {x : L.Ordᶜ ⟨ m ⟩} {F : ℕ → Raw (fin m)} n → Rel m x (F n) → Rel m x (G.lim F)
out-l zero n (r0 q) = r0 (≼l n q)
out-l (suc N) n r = lr n r

out-ll : ∀ m {F : ℕ → L.Ordᶜ ⟨ m ⟩} {η} → (∀ n → Rel m (F n) η) → Rel m (L.lim F) η
out-ll zero h = r0 (l≼ (λ n → un0 (h n)))
out-ll (suc N) h = llr h
```

## 2 槽位上的结点

```agda
ndA : ∀ Lv (s : Pre (fin Lv)) {A : Alg (fin Lv)} (P : RA A) (c : Raw (fin (levN Lv s))) t
  (g : (a : Raw (fin (levN Lv s))) → .(Gd (fin (levN Lv s)) c a) → Alg.T A)
  {j K} {q : j <ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} →
  j ≅ᴵ ⟨ levN Lv s ⟩ → Rel (levN Lv s) (L.Ω ⟨ levN Lv s ⟩) c →
  (∀ (y : L.Ordᶜ j) a .(e : Gd (fin (levN Lv s)) c a) → Rel (levN Lv s) y a →
    RA.ρ P (f (L.into (L.<→◃ q) y)) (g a e)) →
  RA.ρ P (L.limᵢ q f) (nodeA Lv s A c t g)
ndA zero ()
ndA (suc Lv) (inj₁ _) P c t g lv base h = RA.rnd P (inj₁ tt) c t g lv base h
ndA (suc Lv) (inj₂ r) P c t g lv base h = ndA Lv r (shRA P) c t g lv base h

bA : ∀ Lv (s : Pre (fin Lv)) {A : Alg (fin Lv)} (P : RA A) (c : Raw (fin (levN Lv s))) t
  (g : (a : Raw (fin (levN Lv s))) → .(Gd (fin (levN Lv s)) c a) → Alg.T A) {k} {x : L.Ordᶜ k} →
  (∀ .(e : Gd (fin (levN Lv s)) c c) → RA.ρ P x (g c e)) → RA.ρ P x (nodeA Lv s A c t g)
bA zero ()
bA (suc Lv) (inj₁ _) P c t g h = RA.rb P (inj₁ tt) c t g h
bA (suc Lv) (inj₂ r) P c t g h = bA Lv r (shRA P) c t g h
```

## 3 右加数任意、嵌入的前缀、加法

`PLUSR`：左边已有关系，右边加任何树仍有关系。`EMSHIFT`：低层的关系经前缀 `θ` 进入值域。`ADDg`：两边的关系给出和的关系。
`top` 加数在层号 `L+1` 上展开成槽位 `inj₁` 的结点，下界 `cO`，起点由 `START` 给出。

```agda
module _ where
  open RA

  PLUSR : ∀ Lv {A : Alg (fin Lv)} (P : RA A) {k} {x : L.Ordᶜ k} {θ} → ρ P x θ →
    ∀ a → ρ P x (add (fin Lv) A θ a)
  PLUSR Lv P px G.zero = px
  PLUSR Lv P px (G.suc a) = rs P (PLUSR Lv P px a)
  PLUSR Lv P px (G.lim f) = rl P 0 (PLUSR Lv P px (f 0))
  PLUSR Lv P px (G.lc r c t g) = rb P r c _ _ (λ e → PLUSR Lv P px (g c e))
  PLUSR zero P px (G.em () a)
  PLUSR zero P px G.top = rs P px
  PLUSR (suc Lv) P px (G.em _ a) = PLUSR Lv (shRA P) px a
  PLUSR (suc Lv) P px G.top =
    rb P (inj₁ tt) (cO (fin Lv)) _ _ (λ e → PLUSR Lv (shRA P) px (cO (fin Lv)))

  EM0 : ∀ {A : Alg (fin 0)} (P : RA A) θ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ read a →
    ρ P y (add (fin 0) A θ a)
  EM0 P θ z≼ a q = rz P
  EM0 P θ (s≼s p) (G.suc a) refl = rss P (EM0 P θ p a refl)
  EM0 P θ (s≼s p) G.top refl = rss P (EM0 P θ p G.zero refl)
  EM0 P θ (≼l n p) (G.lim f) refl = rl P n (EM0 P θ p (f n) refl)
  EM0 P θ (l≼ h) a q = rll P (λ n → EM0 P θ (h n) a q)
  EM0 P θ (≼i {p = ()} x ex p) a q
  EM0 P θ (i≼ {p = ()} h) a q
  EM0 P θ (≼u {r = ()} p) a q
  EM0 P θ (u≼ {r = ()} p) a q

  EMSHIFT : ∀ Lv {A : Alg (fin Lv)} (P : RA A) θ {k} {y : L.Ordᶜ k} {a} → Rel Lv y a →
    ρ P y (add (fin Lv) A θ a)
  EMSHIFT zero P θ {a = a} (r0 q) = EM0 P θ q a refl
  EMSHIFT (suc Lv) P θ zr = rz P
  EMSHIFT (suc Lv) P θ (ssr r) = rss P (EMSHIFT (suc Lv) P θ r)
  EMSHIFT (suc Lv) P θ (sr r) = rs P (EMSHIFT (suc Lv) P θ r)
  EMSHIFT (suc Lv) P θ (lr n r) = rl P n (EMSHIFT (suc Lv) P θ r)
  EMSHIFT (suc Lv) P θ (llr h) = rll P (λ n → EMSHIFT (suc Lv) P θ (h n))
  EMSHIFT (suc Lv) P θ (br {s = s} {c = c} h) =
    rb P s c _ _ (λ e → EMSHIFT (suc Lv) P θ (h e))
  EMSHIFT (suc Lv) P θ (ndr {s = s} {c = c} lv base h) =
    rnd P s c _ _ lv base (λ y a e r → EMSHIFT (suc Lv) P θ (h y a e r))
  EMSHIFT (suc Lv) P θ (ntr lv h) =
    rnd P (inj₁ tt) (cO (fin Lv)) _ _ lv (START Lv) (λ y a e r → EMSHIFT (suc Lv) P θ (h y a r))
  EMSHIFT (suc Lv) P θ (emr r) = EMSHIFT Lv (shRA P) θ r
  EMSHIFT (suc Lv) P θ (ur r) = ru P (EMSHIFT (suc Lv) P θ r)

  ADD0 : ∀ {A : Alg (fin 0)} (P : RA A) {ℓ} (σ : L.Simᴵ L.zero ℓ) {x : L.Ordᶜ ℓ} {θ} → ρ P x θ →
    ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ read a → ρ P (L.add x σ y) (add (fin 0) A θ a)
  ADD0 P σ px z≼ a q = PLUSR 0 P px a
  ADD0 P σ px (s≼s p) (G.suc a) refl = rss P (ADD0 P σ px p a refl)
  ADD0 P σ px (s≼s p) G.top refl = rss P (ADD0 P σ px p G.zero refl)
  ADD0 P σ px (≼l n p) (G.lim f) refl = rl P n (ADD0 P σ px p (f n) refl)
  ADD0 P σ px (l≼ h) a q = rll P (λ n → ADD0 P σ px (h n) a q)
  ADD0 P σ px (≼i {p = ()} x ex p) a q
  ADD0 P σ px (i≼ {p = ()} h) a q
  ADD0 P σ px (≼u {r = ()} p) a q
  ADD0 P σ px (u≼ {r = ()} p) a q

  ADDg : ∀ Lv {A : Alg (fin Lv)} (P : RA A) {ℓ k} (σ : L.Simᴵ k ℓ) {x : L.Ordᶜ ℓ} {θ} →
    ρ P x θ → ∀ {y : L.Ordᶜ k} {a} → Rel Lv y a → ρ P (L.add x σ y) (add (fin Lv) A θ a)
  ADDg zero P σ px {a = a} (r0 q) = ADD0 P σ px q a refl
  ADDg (suc Lv) P σ px {a = a} zr = PLUSR (suc Lv) P px a
  ADDg (suc Lv) P σ px (ssr r) = rss P (ADDg (suc Lv) P σ px r)
  ADDg (suc Lv) P σ px (sr r) = rs P (ADDg (suc Lv) P σ px r)
  ADDg (suc Lv) P σ px (lr n r) = rl P n (ADDg (suc Lv) P σ px r)
  ADDg (suc Lv) P σ px (llr h) = rll P (λ n → ADDg (suc Lv) P σ px (h n))
  ADDg (suc Lv) P σ px (br {s = s} {c = c} h) =
    rb P s c _ _ (λ e → ADDg (suc Lv) P σ px (h e))
  ADDg (suc Lv) {A} P σ {x} {θ} px (ndr {s = s} {c = c} {g = g} {q = q} {f = f} lv base h) =
    rnd P s c _ _ lv base (λ y a e r →
      subst (λ w → ρ P (L.add x σ (f (L.into (L.<→◃ q) w))) (add (fin (suc Lv)) A θ (g a e)))
        (sym (L.out-into (L.<→◃ (σ q)) y)) (ADDg (suc Lv) P σ px (h y a e r)))
  ADDg (suc Lv) {A} P σ {x} {θ} px (ntr {q = q} {f = f} lv h) =
    rnd P (inj₁ tt) (cO (fin Lv)) _ _ lv (START Lv) (λ y a e r →
      subst (λ w → ρ P (L.add x σ (f (L.into (L.<→◃ q) w))) (add (fin (suc Lv)) A θ (G.em tt a)))
        (sym (L.out-into (L.<→◃ (σ q)) y)) (ADDg (suc Lv) P σ px (h y a r)))
  ADDg (suc Lv) P σ px (emr r) = ADDg Lv (shRA P) σ px r
  ADDg (suc Lv) P σ px (ur r) = ADDg (suc Lv) P (λ q → σ (L.suc q)) px r
```

## 4 前缀与 ω 倍

```agda
ABSORB : ∀ M θ {k} {x : L.Ordᶜ k} {η} → Rel M x η → Rel M x (plus (fin M) θ η)
ABSORB zero θ {η = η} (r0 q) = r0 (plus≽ θ η q)
ABSORB (suc N) θ zr = zr
ABSORB (suc N) θ (ssr r) = ssr (ABSORB (suc N) θ r)
ABSORB (suc N) θ (sr r) = sr (ABSORB (suc N) θ r)
ABSORB (suc N) θ (lr n r) = lr n (ABSORB (suc N) θ r)
ABSORB (suc N) θ (llr h) = llr (λ n → ABSORB (suc N) θ (h n))
ABSORB (suc N) θ (br h) = br (λ e → ABSORB (suc N) θ (h e))
ABSORB (suc N) θ (ndr lv base h) = ndr lv base (λ y a e r → ABSORB (suc N) θ (h y a e r))
ABSORB (suc N) θ (ntr lv h) =
  ndr {s = inj₁ tt} lv (START N) (λ y a e r → ABSORB (suc N) θ (h y a r))
ABSORB (suc N) θ (emr r) = EMSHIFT N (shRA (rawRA N)) θ r
ABSORB (suc N) θ (ur r) = ur (ABSORB (suc N) θ r)

COPIES : ∀ N {A : L.Ordᶜ ⟨ suc N ⟩} {Y} → Rel (suc N) A Y → ∀ n →
  Rel (suc N) (iter (A L.+_) L.zero (suc n)) (copies (fin (suc N)) Y n)
COPIES N px zero = px
COPIES N px (suc n) = ADDg (suc N) (rawRA N) (λ q → q) px (COPIES N px n)

SUCC : ∀ m {A : L.Ordᶜ ⟨ m ⟩} {Y} → Rel m A Y →
  Rel m (L.lim (iter (A L.+_) L.zero)) (successor (fin m) Y)
SUCC zero {Y = Y} (r0 low) = r0 (l≼ λ where
  zero → z≼
  (suc n) → ≼l n (read-copies Y low n))
SUCC (suc N) px = llr λ where
  zero → zr
  (suc n) → lr n (COPIES N px n)
```
