# 证书与阶段无关: 分支有证据的树与第 0 层的世界 (底座)

> 底座, 不含记号. 结论写在 [LevelK](LevelK.lagda.md). `Ordᴵ` 与 [Level](Level.lagda.md) 的同名定义逐字相同, 这里重述一次, 因为 `Level` 的导入链含 [Finite](Finite.lagda.md) 的镜像表记. 这里**不用** `<ᴵ-dec`: 比较来自 `<-decᴬ`. `W-ℓ`: 第 0 层的世界可以是任何 $\ell\ge\omega$, 这是 [InaccFloorBase](InaccFloorBase.lagda.md) 的 `Aℓ` 的地位. §3 是 [InaccThetaNeg](InaccThetaNeg.lagda.md) 的反例族, 逐字.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LevelKWorld where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; at; toLv; Tree)
open import OCF.Align.InaccFloorTree using (natL)
open import OCF.Align.LevelKBase using (NoO; module Leaf; Stage)
open import OCF.Align.LevelKFin using (IsK)
open import OCF.Align.LevelKTower using (St₀; isK₀; WorldK; World)
```

## §1 `Ordᴵ`

```agda
infix 4 _<ᴵ_ _≅ᴵ_ _⊑ᴵ_
data Ordᴵ : Set
data _<ᴵ_ : Ordᴵ → Ordᴵ → Set
data _≅ᴵ_ : Ordᴵ → Ordᴵ → Set
data _⊑ᴵ_ : Ordᴵ → Ordᴵ → Set

data Ordᴵ where
  zero : Ordᴵ
  suc  : Ordᴵ → Ordᴵ
  lim  : (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n)) → Ordᴵ

data _<ᴵ_ where
  zero : ∀ {a} → a <ᴵ suc a
  suc  : ∀ {a b} → a <ᴵ b → a <ᴵ suc b
  lim  : ∀ {a} {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → a <ᴵ f n → a <ᴵ lim f s

data _≅ᴵ_ where
  z≅ : zero ≅ᴵ zero
  s≅ : ∀ {a b} → a ≅ᴵ b → suc a ≅ᴵ suc b
  l≅ : ∀ {f g : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} {t : ∀ n → g n ⊑ᴵ g (suc n)} →
       (∀ n → f n ≅ᴵ g n) → lim f s ≅ᴵ lim g t

data _⊑ᴵ_ where
  z⊑ : ∀ {b} → zero ⊑ᴵ b
  s⊑ : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → suc a ⊑ᴵ b
  l⊑ : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} {b} → (∀ n → f n ⊑ᴵ b) → lim f s ⊑ᴵ b

≅ᴵ-refl : ∀ a → a ≅ᴵ a
≅ᴵ-refl zero      = z≅
≅ᴵ-refl (suc a)   = s≅ (≅ᴵ-refl a)
≅ᴵ-refl (lim f s) = l≅ (λ n → ≅ᴵ-refl (f n))

Sim→⊑ᴵ : ∀ a {b} → (∀ {x} → x <ᴵ a → x <ᴵ b) → a ⊑ᴵ b
Sim→⊑ᴵ zero      h = z⊑
Sim→⊑ᴵ (suc a)   h = s⊑ (≅ᴵ-refl a) (h zero)
Sim→⊑ᴵ (lim f s) h = l⊑ (λ n → Sim→⊑ᴵ (f n) (λ q → h (lim n q)))

natᴵ : ℕ → Ordᴵ
natᴵ zero    = zero
natᴵ (suc n) = suc (natᴵ n)

natᴵ-step : ∀ m → natᴵ m ⊑ᴵ natᴵ (suc m)
natᴵ-step m = Sim→⊑ᴵ (natᴵ m) suc

ωᴵ : Ordᴵ
ωᴵ = lim natᴵ natᴵ-step

em : Ordᴵ → Ordᴸ zero
em zero      = Tree.zero
em (suc a)   = Tree.suc (em a)
em (lim f s) = Tree.lim (λ n → em (f n))

E : Ordᴵ → Lv
E a = toLv (em a)
```

## §2 第 0 层的世界

```agda
module W-ℓ₀ where
  open Stage St₀
  open Leaf fl

  nat-wf : ∀ n → WFᴬ (natL n)
  nat-wf zero    = tt
  nat-wf (suc n) = nat-wf n

  noo-E : ∀ a → NoO (E a)
  noo-E zero      = tt
  noo-E (suc a)   = noo-E a
  noo-E (lim f s) = λ n → noo-E (f n)

  ≅→≈ : ∀ {a b} → a ≅ᴵ b → E a ≈ᴮ E b
  ≅→≈ z≅     = z≈
  ≅→≈ (s≅ e) = s≈ (≅→≈ e)
  ≅→≈ (l≅ h) = l≈ (λ n → ≅→≈ (h n))

  <→≺ : ∀ {a b} → a <ᴵ b → E a ≺ᴬ E b
  <→≺ zero = viaᴬ (inj₁ tt) tt (≈ᴮ-refl _)
  <→≺ (suc q) with <→≺ q
  ... | viaᴬ r d e = viaᴬ (inj₂ r) d e
  <→≺ (lim n q) with <→≺ q
  ... | viaᴬ r d e = viaᴬ (n , r) d e

  ⊑→⊑ : ∀ {a b} → a ⊑ᴵ b → E a ⊑ᴬ E b
  ⊑→⊑ z⊑ = λ ()
  ⊑→⊑ (s⊑ e q) (inj₁ _) _ = ≺ᴬ-respˡ (≅→≈ e) (<→≺ q)
  ⊑→⊑ (s⊑ e q) (inj₂ r) d = ≺→⊑ (≺ᴬ-respˡ (≅→≈ e) (<→≺ q)) r d
  ⊑→⊑ (l⊑ k) (n , r) d = ⊑→⊑ (k n) r d

  wf-E : ∀ a → WFᴬ (E a)
  wf-E zero      = tt
  wf-E (suc a)   = wf-E a
  wf-E (lim f s) = (λ n → ⊑→⊑ (s n)) , (λ n → wf-E (f n))

  E-nat : ∀ n → E (natᴵ n) ≡ natL n
  E-nat zero    = refl
  E-nat (suc n) = cong Lv.suc (E-nat n)

  W-ℓ : (ℓ : Ordᴵ) → (∀ n → natᴵ n <ᴵ ℓ) → WorldK 0 St₀
  W-ℓ ℓ h = record
    { w = record
        { L = E ℓ
        ; loL = noo→lo (E ℓ) (noo-E ℓ)
        ; cxL = wf-E ℓ , noo→rp (E ℓ) (noo-E ℓ) , noo→mn (E ℓ) (noo-E ℓ)
        ; hΩ = <→≺ (h 1)
        }
    ; b0 = λ _ n → subst (_≺ᴬ E ℓ) (E-nat n) (<→≺ (h n))
    }
open W-ℓ₀ using (W-ℓ) public
```

## §3 反例族

```agda
flag : (ℕ → Bool) → ℕ → Bool
flag s zero    = s zero
flag s (suc n) = flag s n ∨ s (suc n)

ω₂ : Ordᴵ
ω₂ = suc (suc ωᴵ)

sel : Bool → ℕ → Ordᴵ
sel true  n = ω₂
sel false n = natᴵ n

nat⊑ω₂ : ∀ n → natᴵ n ⊑ᴵ ω₂
nat⊑ω₂ zero    = z⊑
nat⊑ω₂ (suc n) = s⊑ (≅ᴵ-refl _) (suc (suc (lim (suc n) zero)))

⊑-refl : ∀ a → a ⊑ᴵ a
⊑-refl a = Sim→⊑ᴵ a (λ q → q)

sel-step : ∀ b c n → sel b n ⊑ᴵ sel (b ∨ c) (suc n)
sel-step true  c     n = ⊑-refl ω₂
sel-step false true  n = nat⊑ω₂ n
sel-step false false n = natᴵ-step n

g : (ℕ → Bool) → ℕ → Ordᴵ
g s n = sel (flag s n) n

i : (ℕ → Bool) → Ordᴵ
i s = lim (g s) (λ n → sel-step (flag s n) (s (suc n)) n)

G : (ℕ → Bool) → ℕ → Ordᴵ
G s zero    = ω₂
G s (suc n) = suc (suc (i s))

flag-false : ∀ s → (∀ n → s n ≡ false) → ∀ n → flag s n ≡ false
flag-false s h zero = h zero
flag-false s h (suc n) rewrite flag-false s h n | h (suc n) = refl

flag-true : ∀ s n → s n ≡ true → flag s n ≡ true
flag-true s zero p = p
flag-true s (suc n) p rewrite p = ∨-true (flag s n) where
  ∨-true : ∀ b → (b ∨ true) ≡ true
  ∨-true true  = refl
  ∨-true false = refl

ω≅i : ∀ s → (∀ n → s n ≡ false) → ωᴵ ≅ᴵ i s
ω≅i s h = l≅ λ n → subst (λ b → natᴵ n ≅ᴵ sel b n) (sym (flag-false s h n)) (≅ᴵ-refl _)

tail⊑ : ∀ s n → G s (suc n) ⊑ᴵ G s (suc (suc n))
tail⊑ s n = ⊑-refl _

tF : ∀ s → (∀ n → s n ≡ false) → ∀ n → G s n ⊑ᴵ G s (suc n)
tF s h zero    = s⊑ (s≅ (ω≅i s h)) zero
tF s h (suc n) = tail⊑ s n

ω₁<sel : ∀ b n → b ≡ true → suc ωᴵ <ᴵ sel b n
ω₁<sel _ n refl = zero

tT : ∀ s n → s n ≡ true → ∀ m → G s m ⊑ᴵ G s (suc m)
tT s n p zero    = s⊑ (≅ᴵ-refl _) (suc (suc (lim n (ω₁<sel (flag s n) n (flag-true s n p)))))
tT s n p (suc m) = tail⊑ s m

κ : (ℕ → Bool) → Lv
κ s = lim (λ n → E (G s n))

_ : ∀ s h → E (lim (G s) (tF s h)) ≡ κ s
_ = λ s h → refl

_ : ∀ s n p → E (lim (G s) (tT s n p)) ≡ κ s
_ = λ s n p → refl

at-natE : ∀ n (r : Pre (E (natᴵ n))) → Σ ℕ λ m → at (E (natᴵ n)) r ≡ natL m
at-natE (suc n) (inj₁ _) = n , lem n where
  lem : ∀ n → E (natᴵ n) ≡ natL n
  lem zero    = refl
  lem (suc n) = cong Lv.suc (lem n)
at-natE (suc n) (inj₂ r) = at-natE n r
```
