# YiBtVal 底座：一般层号上的输出规则、槽位结点、加法、前缀、ω 倍、部分和

**验收文件，档位：编译定理 (引理)。** 对一切 `LF` 层号：`RelF` 对加法 (`ADDg`)、前缀 (`ABSORB`)、ω 倍 (`SUCC`)、部分和 (`PSUM`) 封闭；
槽位上的结点 (`bAt`, `ndAt`) 对 (层号, 槽位) 递归，下界直接在 `Raw (lev m s)` 里。与 [YiLvAllAdd](YiLvAllAdd.lagda.md) 同形，多出极限层号上 `top` 的累加 (`cum`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiBtValAdd where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Pre; Low; GdL; Gd)
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiLvIf using (Plain; lev)
open import OCF.Align.YiLvFoldAdd using (Alg; shS; shL; rawAlg; add; plus; copies; successor; cum)
open import OCF.Align.YiLvFoldBase using (nodeAt)
open import OCF.Align.YiRawFoldBase using (psum)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (plus≽; read-copies)
open import OCF.Align.YiLvAllRel using (R0; r0; un0)
open import OCF.Align.YiBtValRel
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open L using (_≅ᴵ_; _<ᴵ_)
open V using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
```

## 1 输出一侧的极限规则

```agda
out-l : ∀ m {j} {x : L.Ordᶜ j} {F : ℕ → Raw m} n → RelF m x (F n) → RelF m x (G.lim F)
out-l B.zero n (r0 q) = r0 (≼l n q)
out-l (B.suc k) n r = lr n r
out-l (B.lim f) n r = lrˡ n r
out-l (B.lc k c w b t g) n ()

ll0 : ∀ {j} {F : ℕ → L.Ordᶜ j} {η} → R0 (F 0) η → (∀ n → R0 (F n) η) → R0 (L.lim F) η
ll0 (r0 q) h = r0 (l≼ (λ n → un0 (h n)))

out-ll : ∀ m {j} {F : ℕ → L.Ordᶜ j} {η} → (∀ n → RelF m (F n) η) → RelF m (L.lim F) η
out-ll B.zero h = ll0 (h 0) h
out-ll (B.suc k) h = llr h
out-ll (B.lim f) h = llrˡ h
out-ll (B.lc k c w b t g) h = h 0
```

## 2 槽位上的结点

```agda
bAt : ∀ m → Plain m → ∀ (s : Pre m) {A : Alg m} (P : RA A) (c : Raw (lev m s)) t
  (g : (a : Raw (lev m s)) → .(Gd (lev m s) c a) → Alg.T A) {j} {x : L.Ordᶜ j} →
  (∀ .(e : Gd (lev m s) c c) → RA.ρ P x (g c e)) → RA.ρ P x (nodeAt m s A c t g)
bAt B.zero pm () P c t g h
bAt (B.suc k) pm (inj₁ _) P c t g h = RA.rb P (inj₁ tt) c t g h
bAt (B.suc k) pm (inj₂ r) P c t g h = bAt k pm r (shRA P) c t g h
bAt (B.lim f) pm (n , r) P c t g h = bAt (f n) (pm n) r (shLA P n) c t g h
bAt (B.lc k₀ c₀ w₀ b₀ t₀ g₀) () s P c t g h

ndAt : ∀ m → Plain m → ∀ (s : Pre m) {A : Alg m} (P : RA A) (c : Raw (lev m s)) t
  (g : (a : Raw (lev m s)) → .(Gd (lev m s) c a) → Alg.T A)
  {j K} {q : j <ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} →
  Corr j (lev m s) → (∀ {j′} → Corr j′ (lev m s) → RelF (lev m s) (L.Ω j′) c) →
  (∀ (y : L.Ordᶜ j) a .(e : Gd (lev m s) c a) → RelF (lev m s) y a →
    RA.ρ P (f (L.into (L.<→◃ q) y)) (g a e)) →
  RA.ρ P (L.limᵢ q f) (nodeAt m s A c t g)
ndAt B.zero pm () P c t g lv base h
ndAt (B.suc k) pm (inj₁ _) P c t g lv base h = RA.rnd P (inj₁ tt) c t g lv base h
ndAt (B.suc k) pm (inj₂ r) P c t g lv base h = ndAt k pm r (shRA P) c t g lv base h
ndAt (B.lim f) pm (n , r) P c t g lv base h = ndAt (f n) (pm n) r (shLA P n) c t g lv base h
ndAt (B.lc k₀ c₀ w₀ b₀ t₀ g₀) () s P c t g lv base h

-- 目标就是 rawAlg m 时，按层号的形状取 RA.
bRaw : ∀ m → Plain m → ∀ (s : Pre m) (c : Raw (lev m s)) t
  (g : (a : Raw (lev m s)) → .(Gd (lev m s) c a) → Raw m) {j} {x : L.Ordᶜ j} →
  (∀ .(e : Gd (lev m s) c c) → RelF m x (g c e)) → RelF m x (nodeAt m s (rawAlg m) c t g)
bRaw B.zero pm () c t g h
bRaw (B.suc k) pm s c t g h = bAt (B.suc k) pm s (rawRAS k) c t g h
bRaw (B.lim f) pm s c t g h = bAt (B.lim f) pm s (rawRAL f) c t g h
bRaw (B.lc k₀ c₀ w₀ b₀ t₀ g₀) () s c t g h

ndRaw : ∀ m → Plain m → ∀ (s : Pre m) (c : Raw (lev m s)) t
  (g : (a : Raw (lev m s)) → .(Gd (lev m s) c a) → Raw m)
  {j K} {q : j <ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} →
  Corr j (lev m s) → (∀ {j′} → Corr j′ (lev m s) → RelF (lev m s) (L.Ω j′) c) →
  (∀ (y : L.Ordᶜ j) a .(e : Gd (lev m s) c a) → RelF (lev m s) y a →
    RelF m (f (L.into (L.<→◃ q) y)) (g a e)) →
  RelF m (L.limᵢ q f) (nodeAt m s (rawAlg m) c t g)
ndRaw B.zero pm () c t g lv base h
ndRaw (B.suc k) pm s c t g lv base h = ndAt (B.suc k) pm s (rawRAS k) c t g lv base h
ndRaw (B.lim f) pm s c t g lv base h = ndAt (B.lim f) pm s (rawRAL f) c t g lv base h
ndRaw (B.lc k₀ c₀ w₀ b₀ t₀ g₀) () s c t g lv base h
```

## 3 右加数任意、嵌入的前缀、加法

极限层号上 `x + top` 是 `x` 加各支 `top` 的累加 (`cum`)，第 `n` 项的左加数是前 `n` 项的累加 (`cumρ`)。

```agda
module _ where
  open RA

  PLUSR : ∀ K {A : Alg K} (P : RA A) {j} {x : L.Ordᶜ j} {θ} → ρ P x θ →
    ∀ a → ρ P x (add K A θ a)
  PLUSR K P px G.zero = px
  PLUSR K P px (G.suc a) = rs P (PLUSR K P px a)
  PLUSR K P px (G.lim f) = rl P 0 (PLUSR K P px (f 0))
  PLUSR K P px (G.lc r c t g) = rb P r c _ _ (λ e → PLUSR K P px (g c e))
  PLUSR B.zero P px (G.em () a)
  PLUSR B.zero P px G.top = rs P px
  PLUSR (B.suc k) P px (G.em _ a) = PLUSR k (shRA P) px a
  PLUSR (B.suc k) P px G.top =
    rb P (inj₁ tt) (cO k) _ _ (λ e → PLUSR k (shRA P) px (cO k))
  PLUSR (B.lim f) P px (G.em n a) = PLUSR (f n) (shLA P n) px a
  PLUSR (B.lim f) P px G.top = rl P 0 (PLUSR (f 0) (shLA P 0) px G.top)
  PLUSR (B.lc k c w b t g) P px (G.em i a) = px
  PLUSR (B.lc k c w b t g) P px G.top = rs P px

  cumρ : ∀ f {A : Alg (B.lim f)} (P : RA A) {j} {x : L.Ordᶜ j} {θ} → ρ P x θ →
    ∀ n → ρ P x (cum (λ n y → add (f n) (shL A n) y G.top) θ n)
  cumρ f P px zero = PLUSR (f 0) (shLA P 0) px G.top
  cumρ f P px (suc n) = PLUSR (f (suc n)) (shLA P (suc n)) (cumρ f P px n) G.top

  EM0 : ∀ {A : Alg B.zero} (P : RA A) θ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ read a →
    ρ P y (add B.zero A θ a)
  EM0 P θ z≼ a q = rz P
  EM0 P θ (s≼s p) (G.suc a) refl = rss P (EM0 P θ p a refl)
  EM0 P θ (s≼s p) G.top refl = rss P (EM0 P θ p G.zero refl)
  EM0 P θ (≼l n p) (G.lim f) refl = rl P n (EM0 P θ p (f n) refl)
  EM0 P θ (l≼ h) a q = rll P (λ n → EM0 P θ (h n) a q)
  EM0 P θ (≼i {p = ()} x ex p) a q
  EM0 P θ (i≼ {p = ()} h) a q
  EM0 P θ (≼u {r = ()} p) a q
  EM0 P θ (u≼ {r = ()} p) a q

  EMSHIFT : ∀ K {A : Alg K} (P : RA A) θ {j} {y : L.Ordᶜ j} {a} → RelF K y a →
    ρ P y (add K A θ a)
  EMSHIFT B.zero P θ {a = a} (r0 q) = EM0 P θ q a refl
  EMSHIFT (B.suc k) P θ zr = rz P
  EMSHIFT (B.suc k) P θ (ssr r) = rss P (EMSHIFT (B.suc k) P θ r)
  EMSHIFT (B.suc k) P θ (sr r) = rs P (EMSHIFT (B.suc k) P θ r)
  EMSHIFT (B.suc k) P θ (lr n r) = rl P n (EMSHIFT (B.suc k) P θ r)
  EMSHIFT (B.suc k) P θ (llr h) = rll P (λ n → EMSHIFT (B.suc k) P θ (h n))
  EMSHIFT (B.suc k) P θ (br {s = s} {c = c} h) =
    rb P s c _ _ (λ e → EMSHIFT (B.suc k) P θ (h e))
  EMSHIFT (B.suc k) P θ (ndr {s = s} {c = c} lv base h) =
    rnd P s c _ _ lv base (λ y a e r → EMSHIFT (B.suc k) P θ (h y a e r))
  EMSHIFT (B.suc k) P θ (ntr lv base h) =
    rnd P (inj₁ tt) (cO k) _ _ lv base (λ y a e r → EMSHIFT (B.suc k) P θ (h y a r))
  EMSHIFT (B.suc k) P θ (emr r) = EMSHIFT k (shRA P) θ r
  EMSHIFT (B.suc k) P θ (ur r) = ru P (EMSHIFT (B.suc k) P θ r)
  EMSHIFT (B.suc k) P θ (us r) = rus P (EMSHIFT (B.suc k) P θ r)
  EMSHIFT (B.lim f) P θ zrˡ = rz P
  EMSHIFT (B.lim f) P θ (ssrˡ r) = rss P (EMSHIFT (B.lim f) P θ r)
  EMSHIFT (B.lim f) P θ (srˡ r) = rs P (EMSHIFT (B.lim f) P θ r)
  EMSHIFT (B.lim f) P θ (lrˡ n r) = rl P n (EMSHIFT (B.lim f) P θ r)
  EMSHIFT (B.lim f) P θ (llrˡ h) = rll P (λ n → EMSHIFT (B.lim f) P θ (h n))
  EMSHIFT (B.lim f) P θ (brˡ {s = s} {c = c} h) =
    rb P s c _ _ (λ e → EMSHIFT (B.lim f) P θ (h e))
  EMSHIFT (B.lim f) P θ (ndrˡ {s = s} {c = c} lv base h) =
    rnd P s c _ _ lv base (λ y a e r → EMSHIFT (B.lim f) P θ (h y a e r))
  EMSHIFT (B.lim f) P θ (emrˡ {n = n} r) = EMSHIFT (f n) (shLA P n) θ r
  EMSHIFT (B.lim f) P θ (tlrˡ zero r) = rl P 0 (EMSHIFT (f 0) (shLA P 0) θ r)
  EMSHIFT (B.lim f) {A} P θ (tlrˡ (suc n) r) =
    rl P (suc n) (EMSHIFT (f (suc n)) (shLA P (suc n))
      (cum (λ n y → add (f n) (shL A n) y G.top) θ n) r)
  EMSHIFT (B.lim f) P θ (urˡ r) = ru P (EMSHIFT (B.lim f) P θ r)
  EMSHIFT (B.lim f) P θ (usˡ r) = rus P (EMSHIFT (B.lim f) P θ r)
  EMSHIFT (B.lc k c w b t g) P θ ()

  ADD0 : ∀ {A : Alg B.zero} (P : RA A) {ℓ} (σ : L.Simᴵ L.zero ℓ) {x : L.Ordᶜ ℓ} {θ} → ρ P x θ →
    ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ read a → ρ P (L.add x σ y) (add B.zero A θ a)
  ADD0 P σ px z≼ a q = PLUSR B.zero P px a
  ADD0 P σ px (s≼s p) (G.suc a) refl = rss P (ADD0 P σ px p a refl)
  ADD0 P σ px (s≼s p) G.top refl = rss P (ADD0 P σ px p G.zero refl)
  ADD0 P σ px (≼l n p) (G.lim f) refl = rl P n (ADD0 P σ px p (f n) refl)
  ADD0 P σ px (l≼ h) a q = rll P (λ n → ADD0 P σ px (h n) a q)
  ADD0 P σ px (≼i {p = ()} x ex p) a q
  ADD0 P σ px (i≼ {p = ()} h) a q
  ADD0 P σ px (≼u {r = ()} p) a q
  ADD0 P σ px (u≼ {r = ()} p) a q

  ADDg : ∀ K {A : Alg K} (P : RA A) {ℓ j} (σ : L.Simᴵ j ℓ) {x : L.Ordᶜ ℓ} {θ} →
    ρ P x θ → ∀ {y : L.Ordᶜ j} {a} → RelF K y a → ρ P (L.add x σ y) (add K A θ a)
  ADDg B.zero P σ px {a = a} (r0 q) = ADD0 P σ px q a refl
  ADDg (B.suc k) P σ px {a = a} zr = PLUSR (B.suc k) P px a
  ADDg (B.suc k) P σ px (ssr r) = rss P (ADDg (B.suc k) P σ px r)
  ADDg (B.suc k) P σ px (sr r) = rs P (ADDg (B.suc k) P σ px r)
  ADDg (B.suc k) P σ px (lr n r) = rl P n (ADDg (B.suc k) P σ px r)
  ADDg (B.suc k) P σ px (llr h) = rll P (λ n → ADDg (B.suc k) P σ px (h n))
  ADDg (B.suc k) P σ px (br {s = s} {c = c} h) =
    rb P s c _ _ (λ e → ADDg (B.suc k) P σ px (h e))
  ADDg (B.suc k) {A} P σ {x} {θ} px (ndr {s = s} {c = c} {g = g} {q = q} {f = f} lv base h) =
    rnd P s c _ _ lv base (λ y a e r →
      subst (λ w → ρ P (L.add x σ (f (L.into (L.<→◃ q) w))) (add (B.suc k) A θ (g a e)))
        (sym (L.out-into (L.<→◃ (σ q)) y)) (ADDg (B.suc k) P σ px (h y a e r)))
  ADDg (B.suc k) {A} P σ {x} {θ} px (ntr {q = q} {f = f} lv base h) =
    rnd P (inj₁ tt) (cO k) _ _ lv base (λ y a e r →
      subst (λ w → ρ P (L.add x σ (f (L.into (L.<→◃ q) w))) (add (B.suc k) A θ (G.em tt a)))
        (sym (L.out-into (L.<→◃ (σ q)) y)) (ADDg (B.suc k) P σ px (h y a r)))
  ADDg (B.suc k) P σ px (emr r) = ADDg k (shRA P) σ px r
  ADDg (B.suc k) P σ px (ur r) = ADDg (B.suc k) P (λ q → σ (L.suc q)) px r
  ADDg (B.suc k) P σ px (us {n = n} r) = ADDg (B.suc k) P (λ q → σ (L.lim n q)) px r
  ADDg (B.lim f) P σ px {a = a} zrˡ = PLUSR (B.lim f) P px a
  ADDg (B.lim f) P σ px (ssrˡ r) = rss P (ADDg (B.lim f) P σ px r)
  ADDg (B.lim f) P σ px (srˡ r) = rs P (ADDg (B.lim f) P σ px r)
  ADDg (B.lim f) P σ px (lrˡ n r) = rl P n (ADDg (B.lim f) P σ px r)
  ADDg (B.lim f) P σ px (llrˡ h) = rll P (λ n → ADDg (B.lim f) P σ px (h n))
  ADDg (B.lim f) P σ px (brˡ {s = s} {c = c} h) =
    rb P s c _ _ (λ e → ADDg (B.lim f) P σ px (h e))
  ADDg (B.lim f) {A} P σ {x} {θ} px (ndrˡ {s = s} {c = c} {g = g} {q = q} {h = h₀} lv base h) =
    rnd P s c _ _ lv base (λ y a e r →
      subst (λ w → ρ P (L.add x σ (h₀ (L.into (L.<→◃ q) w))) (add (B.lim f) A θ (g a e)))
        (sym (L.out-into (L.<→◃ (σ q)) y)) (ADDg (B.lim f) P σ px (h y a e r)))
  ADDg (B.lim f) P σ px (emrˡ {n = n} r) = ADDg (f n) (shLA P n) σ px r
  ADDg (B.lim f) P σ px (tlrˡ zero r) = rl P 0 (ADDg (f 0) (shLA P 0) σ px r)
  ADDg (B.lim f) P σ px (tlrˡ (suc n) r) =
    rl P (suc n) (ADDg (f (suc n)) (shLA P (suc n)) σ (cumρ f P px n) r)
  ADDg (B.lim f) P σ px (urˡ r) = ADDg (B.lim f) P (λ q → σ (L.suc q)) px r
  ADDg (B.lim f) P σ px (usˡ {n = n} r) = ADDg (B.lim f) P (λ q → σ (L.lim n q)) px r
  ADDg (B.lc k c w b t g) P σ px ()
```

## 4 前缀、ω 倍、部分和

```agda
ABSORB : ∀ K θ {j} {x : L.Ordᶜ j} {η} → RelF K x η → RelF K x (plus K θ η)
ABSORB B.zero θ {η = η} (r0 q) = r0 (plus≽ θ η q)
ABSORB (B.suc k) θ zr = zr
ABSORB (B.suc k) θ (ssr r) = ssr (ABSORB (B.suc k) θ r)
ABSORB (B.suc k) θ (sr r) = sr (ABSORB (B.suc k) θ r)
ABSORB (B.suc k) θ (lr n r) = lr n (ABSORB (B.suc k) θ r)
ABSORB (B.suc k) θ (llr h) = llr (λ n → ABSORB (B.suc k) θ (h n))
ABSORB (B.suc k) θ (br h) = br (λ e → ABSORB (B.suc k) θ (h e))
ABSORB (B.suc k) θ (ndr lv base h) = ndr lv base (λ y a e r → ABSORB (B.suc k) θ (h y a e r))
ABSORB (B.suc k) θ (ntr lv base h) =
  ndr {s = inj₁ tt} lv base (λ y a e r → ABSORB (B.suc k) θ (h y a r))
ABSORB (B.suc k) θ (emr r) = EMSHIFT k (shRA (rawRAS k)) θ r
ABSORB (B.suc k) θ (ur r) = ur (ABSORB (B.suc k) θ r)
ABSORB (B.suc k) θ (us r) = us (ABSORB (B.suc k) θ r)
ABSORB (B.lim f) θ zrˡ = zrˡ
ABSORB (B.lim f) θ (ssrˡ r) = ssrˡ (ABSORB (B.lim f) θ r)
ABSORB (B.lim f) θ (srˡ r) = srˡ (ABSORB (B.lim f) θ r)
ABSORB (B.lim f) θ (lrˡ n r) = lrˡ n (ABSORB (B.lim f) θ r)
ABSORB (B.lim f) θ (llrˡ h) = llrˡ (λ n → ABSORB (B.lim f) θ (h n))
ABSORB (B.lim f) θ (brˡ h) = brˡ (λ e → ABSORB (B.lim f) θ (h e))
ABSORB (B.lim f) θ (ndrˡ lv base h) = ndrˡ lv base (λ y a e r → ABSORB (B.lim f) θ (h y a e r))
ABSORB (B.lim f) θ (emrˡ {n = n} r) = EMSHIFT (f n) (shLA (rawRAL f) n) θ r
ABSORB (B.lim f) θ (tlrˡ zero r) = lrˡ 0 (EMSHIFT (f 0) (shLA (rawRAL f) 0) θ r)
ABSORB (B.lim f) θ (tlrˡ (suc n) r) =
  lrˡ (suc n) (EMSHIFT (f (suc n)) (shLA (rawRAL f) (suc n))
    (cum (λ n y → add (f n) (shL (rawAlg (B.lim f)) n) y G.top) θ n) r)
ABSORB (B.lim f) θ (urˡ r) = urˡ (ABSORB (B.lim f) θ r)
ABSORB (B.lim f) θ (usˡ r) = usˡ (ABSORB (B.lim f) θ r)
ABSORB (B.lc k c w b t g) θ ()

COPIESˢ : ∀ k {j} {A : L.Ordᶜ j} {Y} → RelF (B.suc k) A Y → ∀ n →
  RelF (B.suc k) (iter (A L.+_) L.zero (suc n)) (copies (B.suc k) Y n)
COPIESˢ k px zero = px
COPIESˢ k px (suc n) = ADDg (B.suc k) (rawRAS k) (λ q → q) px (COPIESˢ k px n)

COPIESˡ : ∀ f {j} {A : L.Ordᶜ j} {Y} → RelF (B.lim f) A Y → ∀ n →
  RelF (B.lim f) (iter (A L.+_) L.zero (suc n)) (copies (B.lim f) Y n)
COPIESˡ f px zero = px
COPIESˡ f px (suc n) = ADDg (B.lim f) (rawRAL f) (λ q → q) px (COPIESˡ f px n)

SUCC : ∀ m {j} {A : L.Ordᶜ j} {Y} → RelF m A Y →
  RelF m (L.lim (iter (A L.+_) L.zero)) (successor m Y)
SUCC B.zero {Y = Y} (r0 low) = r0 (l≼ λ where
  zero → z≼
  (suc n) → ≼l n (read-copies Y low n))
SUCC (B.suc k) px = llr λ where
  zero → zr
  (suc n) → lr n (COPIESˢ k px n)
SUCC (B.lim f) px = llrˡ λ where
  zero → zrˡ
  (suc n) → lrˡ n (COPIESˡ f px n)
SUCC (B.lc k c w b t g) ()

PSUM : ∀ m (g : ℕ → Raw m) {j} {z : L.Ordᶜ j} n → RelF m z (g n) → RelF m z (psum m g n)
PSUM m g zero r = r
PSUM m g (suc n) r = ABSORB m (psum m g n) r
```
