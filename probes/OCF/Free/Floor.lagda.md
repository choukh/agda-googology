# 无记号主线 (四): 地板, 上界, 外层闭包的算子

> **`Flr`, `Ev`, `Run`, `bound`, `cloA`.** 原文件其余部分是带标签的闭包, 这里全部去掉.
> 脚本从 [Uniform3Base](../Align/Uniform3Base.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Floor where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix
open import OCF.Free.Aux
```

```agda
open Ord-Ord using (iter)

```

## §2 字面证据与前缀塔

```agda
infixl 5 _⊔_
data Flr : Set where
  fz  : Flr
  fk  : Ordᴵ → Flr
  fb  : Ordᴵ → Flr
  _⊔_ : Flr → Flr → Flr

Ev : Ordᴵ → Flr → Set
Ev ℓ fz      = ⊤
Ev ℓ (fk K)  = Simᴵ (suc K) ℓ
Ev ℓ (fb K)  = Simᴵ K ℓ
Ev ℓ (a ⊔ b) = Ev ℓ a × Ev ℓ b

data InF (K : Ordᴵ) : Flr → Set where
  ink : InF K (fk K)
  inb : InF K (fb K)
  inl : ∀ {a b} → InF K a → InF K (a ⊔ b)
  inr : ∀ {a b} → InF K b → InF K (a ⊔ b)

liftEv : ∀ {ℓ ℓ′} (φ : Flr) → Simᴵ ℓ ℓ′ → Ev ℓ φ → Ev ℓ′ φ
liftEv fz      τ _       = tt
liftEv (fk K)  τ e       = λ q → τ (e q)
liftEv (fb K)  τ e       = λ q → τ (e q)
liftEv (a ⊔ b) τ (x , y) = liftEv a τ x , liftEv b τ y
Run : Flr → Set
Run φ = ∀ {i ℓ} → Ev ℓ φ → i <ᴵ ℓ → Ordˢ i

A : ℕ → Flr → Set
A zero    φ = Run φ
A (suc d) φ = ∀ {fl} → A d fl → A d (fl ⊔ φ)

wk : ∀ d {φ ψ} → (∀ {ℓ} → Ev ℓ ψ → Ev ℓ φ) → A d φ → A d ψ
wk zero    le x ev p = x (le ev) p
wk (suc d) le x P    = wk d (λ { (u , v) → u , le v }) (x P)

limA : ∀ d {φ} → (ℕ → A d φ) → A d φ
limA zero    F ev p = Ord₊ˢ.lim (λ m → F m ev p)
limA (suc d) F P    = limA d (λ m → F m P)

limᵢA : ∀ d {φ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → A d φ) → A d φ
limᵢA zero {j = j} ac h ev p with <ᴵ-dec (ac ev) p
... | injᵃ (via e r) = Ord₊ˢ.limᵢ r (λ y → h (tr⁻ˢ e (outˢ (<→◃ r) y)) ev p)
... | injᵇ _ = Ord₊ˢ.lim (λ m → h (iter (λ x → h x ev (ac ev)) (Ωˢ j) m) ev p)
... | injᶜ _ = Ord₊ˢ.lim (λ m → h (iter (λ x → h x ev (ac ev)) (Ωˢ j) m) ev p)
limᵢA (suc d) ac h P = limᵢA d (λ ev → ac (proj₂ ev)) (λ x → h x P)

ŝA : ∀ d {φ} (c : Ordᴵ) → A d φ → ((η : Ordᴵ) → c ⊑ᴵ η → A d φ) → A d φ
ŝA zero    c t g ev p = Ord₊ˢ.ŝ c (t ev p) (λ η e → g η e ev p)
ŝA (suc d) c t g P    = ŝA d c (t P) (λ η e → g η e P)

ĉA : ∀ d {φ} (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → A d φ → ((η : Ordᴵ) → c ⊑ᴵ η → A d φ) → A d φ
ĉA zero    c t₀ g o₀ o ev p = Ord₊ˢ.ĉᴸ c t₀ g (o₀ ev p) (λ η e → o η e ev p)
ĉA (suc d) c t₀ g o₀ o P    = ĉA d c t₀ g (o₀ P) (λ η e → o η e P)
```

## §3 界: 逐点上确界

```agda
⊑-suc : ∀ a → a ⊑ᴵ suc a
⊑-suc a = Sim→⊑ᴵ suc

⊑L : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → f n ⊑ᴵ lim f s
⊑L n = Sim→⊑ᴵ (λ q → lim n q)

FsUB : ∀ {a b c} → a ⊑ᴵ c → b ⊑ᴵ c → ∀ n → Fs a b n ⊑ᴵ c
FsUB ac bc zero    = ac
FsUB ac bc (suc n) = bc

≺0 : ∀ {a b} → a ≺ᴵ b → b ≅ᴵ zero → ⊥
≺0 (via e ()) z≅

Max3 : ∀ y K → Set
Max3 y K = K ≺ᴵ y ⊎ y ≺ᴵ K ⊎ K ≅ᴵ y

maxS : ∀ {y K} → Max3 y K → Ordᴵ
maxS {y} (injᵃ _)    = suc y
maxS {K = K} (injᵇ _) = suc K
maxS {y} (injᶜ _)    = suc y

mutual
  sup₁ : ∀ {ℓ} (a K : Ordᴵ) → Simᴵ a ℓ → Simᴵ (suc K) ℓ → Ordᴵ
  sup₁ zero      K σ ek = suc K
  sup₁ (suc y)   K σ ek = maxS (<ᴵ-dec (ek zero) (σ zero))
  sup₁ (lim g s) K σ ek =
    lim (λ n → sup₁ (g n) K (λ q → σ (lim n q)) ek)
        (λ n → sup₁-lub (g n) K _ ek (⊑ᴵ-trans (s n) (sup₁-up (g (suc n)) K _ ek)) (sup₁-K (g (suc n)) K _ ek))

  sup₁-up : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → a ⊑ᴵ sup₁ a K σ ek
  sup₁-up zero      K σ ek = z⊑
  sup₁-up (suc y)   K σ ek with <ᴵ-dec (ek zero) (σ zero)
  ... | injᵃ _ = ⊑ᴵ-refl
  ... | injᵇ (via e r) = s⊑ e (suc r)
  ... | injᶜ _ = ⊑ᴵ-refl
  sup₁-up (lim g s) K σ ek = l⊑ (λ n → ⊑ᴵ-trans (sup₁-up (g n) K (λ q → σ (lim n q)) ek) (⊑L n))

  sup₁-K : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → suc K ⊑ᴵ sup₁ a K σ ek
  sup₁-K zero      K σ ek = ⊑ᴵ-refl
  sup₁-K (suc y)   K σ ek with <ᴵ-dec (ek zero) (σ zero)
  ... | injᵃ (via e r) = s⊑ e (suc r)
  ... | injᵇ _ = ⊑ᴵ-refl
  ... | injᶜ e = s⊑ e zero
  sup₁-K (lim g s) K σ ek = ⊑ᴵ-trans (sup₁-K (g 0) K (λ q → σ (lim 0 q)) ek) (⊑L 0)

  sup₁-lub : ∀ {ℓ η} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → a ⊑ᴵ η → suc K ⊑ᴵ η → sup₁ a K σ ek ⊑ᴵ η
  sup₁-lub zero      K σ ek h k = k
  sup₁-lub (suc y)   K σ ek h k with <ᴵ-dec (ek zero) (σ zero)
  ... | injᵃ _ = h
  ... | injᵇ _ = k
  ... | injᶜ _ = h
  sup₁-lub (lim g s) K σ ek (l⊑ h) k = l⊑ (λ n → sup₁-lub (g n) K (λ q → σ (lim n q)) ek (h n) k)

mutual
  sup : ∀ {ℓ} (a K : Ordᴵ) → Simᴵ a ℓ → Simᴵ K ℓ → Ordᴵ
  sup a zero      σ σK = a
  sup a (suc K)   σ σK = sup₁ a K σ σK
  sup a (lim h t) σ σK =
    lim (λ n → sup a (h n) σ (λ q → σK (lim n q)))
        (λ n → sup-lub a (h n) σ _ (sup-up a (h (suc n)) σ _) (⊑ᴵ-trans (t n) (sup-K a (h (suc n)) σ _)))

  sup-up : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → a ⊑ᴵ sup a K σ σK
  sup-up a zero      σ σK = ⊑ᴵ-refl
  sup-up a (suc K)   σ σK = sup₁-up a K σ σK
  sup-up a (lim h t) σ σK = ⊑ᴵ-trans (sup-up a (h 0) σ (λ q → σK (lim 0 q))) (⊑L 0)

  sup-K : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → K ⊑ᴵ sup a K σ σK
  sup-K a zero      σ σK = z⊑
  sup-K a (suc K)   σ σK = sup₁-K a K σ σK
  sup-K a (lim h t) σ σK = l⊑ (λ n → ⊑ᴵ-trans (sup-K a (h n) σ (λ q → σK (lim n q))) (⊑L n))

  sup-lub : ∀ {ℓ η} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → a ⊑ᴵ η → K ⊑ᴵ η → sup a K σ σK ⊑ᴵ η
  sup-lub a zero      σ σK h k = h
  sup-lub a (suc K)   σ σK h k = sup₁-lub a K σ σK h k
  sup-lub a (lim f t) σ σK h (l⊑ k) = l⊑ (λ n → sup-lub a (f n) σ (λ q → σK (lim n q)) h (k n))

sup₁-sim : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → Simᴵ (sup₁ a K σ ek) ℓ
sup₁-sim zero      K σ ek q = ek q
sup₁-sim (suc y)   K σ ek q with <ᴵ-dec (ek zero) (σ zero)
... | injᵃ _ = σ q
... | injᵇ _ = ek q
... | injᶜ _ = σ q
sup₁-sim (lim g s) K σ ek (lim n q) = sup₁-sim (g n) K (λ r → σ (lim n r)) ek q

sup-sim : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → Simᴵ (sup a K σ σK) ℓ
sup-sim a zero      σ σK q = σ q
sup-sim a (suc K)   σ σK q = sup₁-sim a K σ σK q
sup-sim a (lim h t) σ σK (lim n q) = sup-sim a (h n) σ (λ r → σK (lim n r)) q
```

```agda
NZ : Ordᴵ → Set
NZ zero      = ⊥
NZ (suc _)   = ⊤
NZ (lim f s) = ∀ n → NZ (f n)

sup₁-NZ : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → NZ (sup₁ a K σ ek)
sup₁-NZ zero      K σ ek = tt
sup₁-NZ (suc y)   K σ ek with <ᴵ-dec (ek zero) (σ zero)
... | injᵃ _ = tt
... | injᵇ _ = tt
... | injᶜ _ = tt
sup₁-NZ (lim g s) K σ ek n = sup₁-NZ (g n) K (λ q → σ (lim n q)) ek

sup-NZ : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (σK : Simᴵ K ℓ) → NZ a → NZ (sup a K σ σK)
sup-NZ a zero      σ σK nz = nz
sup-NZ a (suc K)   σ σK nz = sup₁-NZ a K σ σK
sup-NZ a (lim h t) σ σK nz n = sup-NZ a (h n) σ (λ q → σK (lim n q)) nz

sup₁-lub₀ : ∀ {ℓ η} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → NZ a → K ≅ᴵ zero → a ⊑ᴵ η → sup₁ a K σ ek ⊑ᴵ η
sup₁-lub₀ (suc y)   K σ ek nz k0 h with <ᴵ-dec (ek zero) (σ zero)
... | injᵃ _ = h
... | injᵇ s = ⊥-elim (≺0 s k0)
... | injᶜ _ = h
sup₁-lub₀ (lim g s) K σ ek nz k0 (l⊑ h) = l⊑ (λ n → sup₁-lub₀ (g n) K (λ q → σ (lim n q)) ek (nz n) k0 (h n))

sup₁-triv : ∀ {ℓ} (a K : Ordᴵ) (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) → NZ a → K ≅ᴵ zero → sup₁ a K σ ek ≅ᴵ a
sup₁-triv (suc y)   K σ ek nz k0 with <ᴵ-dec (ek zero) (σ zero)
... | injᵃ _ = ≅ᴵ-refl _
... | injᵇ s = ⊥-elim (≺0 s k0)
... | injᶜ _ = ≅ᴵ-refl _
sup₁-triv (lim g s) K σ ek nz k0 = l≅ (λ n → sup₁-triv (g n) K (λ q → σ (lim n q)) ek (nz n) k0)
```

```agda
isB : ∀ {K φ} → InF K φ → Bool
isB ink     = false
isB inb     = true
isB (inl k) = isB k
isB (inr k) = isB k

DemB : Bool → Ordᴵ → Ordᴵ → Set
DemB false η K = (K ≺ᴵ η) ⊎ (K ≅ᴵ zero)
DemB true  η K = K ⊑ᴵ η

Dem : ∀ {K φ} → Ordᴵ → InF K φ → Set
Dem {K} η k = DemB (isB k) η K

record Top (i ℓ : Ordᴵ) (φ : Flr) : Set where
  constructor top
  field
    Bd  : Ordᴵ
    sb  : Simᴵ Bd ℓ
    nz  : NZ Bd
    ubd : ∀ {η} → i ≺ᴵ η → (∀ {K} (k : InF K φ) → Dem η k) → Bd ⊑ᴵ η
    Fc  : Ordᴵ
    evF : Ev Fc φ
    iF  : i <ᴵ Fc
    FM  : Fc ⊑ᴵ Bd
    MF  : Bd ⊑ᴵ Fc
open Top public

top₀ : ∀ {i ℓ} → i <ᴵ ℓ → Top i ℓ fz
top₀ {i} p = top (suc i) (λ { zero → p ; (suc q) → <ᴵ-trans q p }) tt
                 (λ { (via e q) _ → s⊑ e q }) (suc i) tt zero ⊑ᴵ-refl ⊑ᴵ-refl

module _ {i ℓ φ} (t : Top i ℓ φ) {D B′ : Ordᴵ} (bb : Bd t ⊑ᴵ B′) (dd : D ⊑ᴵ B′) where
  F₁ : Ordᴵ
  F₁ = Mlev (Fc t) B′ (⊑ᴵ-trans (FM t) bb)
  Fₙ : Ordᴵ
  Fₙ = Mlev D F₁ (⊑ᴵ-trans dd (⊑L 1))
  Fₙ-M : Fₙ ⊑ᴵ B′
  Fₙ-M = l⊑ (FsUB dd (l⊑ (FsUB (⊑ᴵ-trans (FM t) bb) ⊑ᴵ-refl)))
  Fₙ-B : B′ ⊑ᴵ Fₙ
  Fₙ-B = Sim→⊑ᴵ (λ q → lim 1 (lim 1 q))

ins : ∀ {i ℓ φ K} → Top i ℓ φ → Simᴵ (suc K) ℓ → Top i ℓ (φ ⊔ fk K)
ins {i} {φ = φ} {K} t ek =
  top B′ (sup₁-sim (Bd t) K (sb t) ek) (sup₁-NZ (Bd t) K (sb t) ek)
      (λ {η} iη h → ub iη (h (inr ink)) (λ k → h (inl k)))
      (Fₙ t bb dd) (liftEv φ (λ q → lim 1 (lim 0 q)) (evF t) , (λ q → lim 0 q)) (lim 1 (lim 0 (iF t))) (Fₙ-M t bb dd) (Fₙ-B t bb dd)
  where
  B′ = sup₁ (Bd t) K (sb t) ek
  bb = sup₁-up (Bd t) K (sb t) ek
  dd = sup₁-K (Bd t) K (sb t) ek
  ub : ∀ {η} → i ≺ᴵ η → (K ≺ᴵ η) ⊎ (K ≅ᴵ zero) → (∀ {K′} (k : InF K′ φ) → Dem η k) → B′ ⊑ᴵ η
  ub iη (inj₁ (via e q)) h = sup₁-lub (Bd t) K (sb t) ek (ubd t iη h) (s⊑ e q)
  ub iη (inj₂ k0) h = sup₁-lub₀ (Bd t) K (sb t) ek (nz t) k0 (ubd t iη h)

insB : ∀ {i ℓ φ K} → Top i ℓ φ → Simᴵ K ℓ → Top i ℓ (φ ⊔ fb K)
insB {i} {φ = φ} {K} t ek =
  top B′ (sup-sim (Bd t) K (sb t) ek) (sup-NZ (Bd t) K (sb t) ek (nz t))
      (λ {η} iη h → ub iη (h (inr inb)) (λ k → h (inl k)))
      (Fₙ t bb dd) (liftEv φ (λ q → lim 1 (lim 0 q)) (evF t) , (λ q → lim 0 q)) (lim 1 (lim 0 (iF t))) (Fₙ-M t bb dd) (Fₙ-B t bb dd)
  where
  B′ = sup (Bd t) K (sb t) ek
  bb = sup-up (Bd t) K (sb t) ek
  dd = sup-K (Bd t) K (sb t) ek
  ub : ∀ {η} → i ≺ᴵ η → K ⊑ᴵ η → (∀ {K′} (k : InF K′ φ) → Dem η k) → B′ ⊑ᴵ η
  ub iη le h = sup-lub (Bd t) K (sb t) ek (ubd t iη h) le
```

```agda
mapTop : ∀ {i ℓ φ ψ} → (∀ {L} → Ev L φ → Ev L ψ) → (g : ∀ {K} → InF K φ → InF K ψ) → (∀ {K} (k : InF K φ) → isB (g k) ≡ isB k) → Top i ℓ φ → Top i ℓ ψ
mapTop f g gb t = top (Bd t) (sb t) (nz t)
  (λ {η} iη h → ubd t iη (λ {K} k → subst (λ b → DemB b η K) (gb k) (h (g k)))) (Fc t) (f (evF t)) (iF t) (FM t) (MF t)

accT : ∀ {i ℓ φ₁} → Top i ℓ φ₁ → (φ₂ : Flr) → Ev ℓ φ₂ → Top i ℓ (φ₁ ⊔ φ₂)
accT t fz      _       = mapTop (λ x → x , tt) inl (λ _ → refl) t
accT t (fk K)  ek      = ins t ek
accT t (fb K)  ek      = insB t ek
accT t (a ⊔ b) (x , y) =
  mapTop (λ { ((u , v) , w) → u , (v , w) })
         (λ { (inl (inl k)) → inl k ; (inl (inr k)) → inr (inl k) ; (inr k) → inr (inr k) })
         (λ { (inl (inl k)) → refl ; (inl (inr k)) → refl ; (inr k) → refl })
         (accT (accT t a x) b y)

strip : ∀ {K φ} → InF K (fz ⊔ φ) → InF K φ
strip (inl ())
strip (inr k) = k

bound : ∀ {i ℓ} (φ : Flr) → Ev ℓ φ → i <ᴵ ℓ → Top i ℓ φ
bound φ ev p = mapTop proj₂ strip (λ { (inl ()) ; (inr k) → refl }) (accT (top₀ p) φ ev)

FB : ∀ {i ℓ φ} (B : Top i ℓ φ) {η} → Bd B ⊑ᴵ η → Fc B ⊑ᴵ suc η
FB B {η} e = ⊑ᴵ-trans (FM B) (⊑ᴵ-trans e (⊑-suc η))
```

```agda
cloA : ∀ d {φ} → A d (φ ⊔ fk zero) → ((η : Ordᴵ) → A d (φ ⊔ fk η)) → A d (φ ⊔ fk zero)
cloA zero {φ} t g {i} ev p =
  Ord₊ˢ.ŝ (Bd B) (t ev p)
          (λ η e → g η {ℓ = Mlev (Fc B) (suc η) (FB B e)} (liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q))
                         (lim 0 (iF B)))
  where B = bound (φ ⊔ fk zero) ev p
cloA (suc d) {φ} t g {fl} P =
  wk d (λ { (u , (v , w)) → (u , v) , w })
       (cloA d {fl ⊔ φ} (wk d (λ { ((u , v) , w) → u , (v , w) }) (t P))
                        (λ η → wk d (λ { ((u , v) , w) → u , (v , w) }) (g η P)))
```

## §4 统一折叠

```agda
flo : Ordᴵ → Flr
flo zero      = fz
flo (suc k)   = fk k
flo (lim f s) = fb (lim f s)

cvFlo : ∀ k {ℓ} → Ev ℓ (flo k) → Simᴵ k ℓ
cvFlo zero      _ = σ⊥
cvFlo (suc k)   e = e
cvFlo (lim f s) e = e

toFlo : ∀ k {ℓ} → Simᴵ k ℓ → Ev ℓ (flo k)
toFlo zero      σ = tt
toFlo (suc k)   σ = σ
toFlo (lim f s) σ = σ
```

## §5 符号项

```agda

∅ᴿ : Run fz
∅ᴿ {i} _ p = Ωˢ i
```

## §7 深度 0 的行引理

```agda
sucRun : ∀ {φ} → Run φ → Run φ
sucRun R ev p = Ord₊ˢ.lim (iter (R ev p +ˢ_) Ord₊ˢ.zero)
```

```agda
infix 4 _∼ᶠ_
data _∼ᶠ_ : Flr → Flr → Set where
  fz∼ : fz ∼ᶠ fz
  fk∼ : ∀ {K K′} → K ≅ᴵ K′ → fk K ∼ᶠ fk K′
  fb∼ : ∀ {K K′} → K ≅ᴵ K′ → fb K ∼ᶠ fb K′
  zk∼ : ∀ {K′} → K′ ≅ᴵ zero → fz ∼ᶠ fk K′
  kz∼ : ∀ {K} → K ≅ᴵ zero → fk K ∼ᶠ fz
  ⊔∼  : ∀ {a a′ b b′} → a ∼ᶠ a′ → b ∼ᶠ b′ → a ⊔ b ∼ᶠ a′ ⊔ b′

∼ᶠ-refl : ∀ φ → φ ∼ᶠ φ
∼ᶠ-refl fz      = fz∼
∼ᶠ-refl (fk K)  = fk∼ (≅ᴵ-refl K)
∼ᶠ-refl (fb K)  = fb∼ (≅ᴵ-refl K)
∼ᶠ-refl (a ⊔ b) = ⊔∼ (∼ᶠ-refl a) (∼ᶠ-refl b)

sup₁-≅ : ∀ {ℓ ℓ′ a a′ K K′} (σ : Simᴵ a ℓ) (ek : Simᴵ (suc K) ℓ) (σ′ : Simᴵ a′ ℓ′) (ek′ : Simᴵ (suc K′) ℓ′) →
         a ≅ᴵ a′ → K ≅ᴵ K′ → sup₁ a K σ ek ≅ᴵ sup₁ a′ K′ σ′ ek′
sup₁-≅ σ ek σ′ ek′ z≅ eK = s≅ eK
sup₁-≅ σ ek σ′ ek′ (s≅ eM) eK with <ᴵ-dec (ek zero) (σ zero) | <ᴵ-dec (ek′ zero) (σ′ zero)
... | injᵃ (via _ _) | injᵃ (via _ _) = s≅ eM
... | injᵃ (via _ _) | injᶜ _ = s≅ eM
... | injᶜ _ | injᵃ (via _ _) = s≅ eM
... | injᶜ _ | injᶜ _ = s≅ eM
... | injᵇ (via _ _) | injᵇ (via _ _) = s≅ eK
... | injᵃ r | injᵇ s = ⊥-elim (clash₁ eK eM r s)
... | injᶜ c | injᵇ s = ⊥-elim (clash₂ (≅ᴵ-sym eM) (≅ᴵ-sym eK) s (≅ᴵ-sym c))
... | injᵇ s | injᵃ r = ⊥-elim (clash₁ (≅ᴵ-sym eK) (≅ᴵ-sym eM) r s)
... | injᵇ s | injᶜ c = ⊥-elim (clash₂ eM eK s (≅ᴵ-sym c))
sup₁-≅ σ ek σ′ ek′ (l≅ h) eK = l≅ (λ n → sup₁-≅ (λ q → σ (lim n q)) ek (λ q → σ′ (lim n q)) ek′ (h n) eK)

sup-≅ : ∀ {ℓ ℓ′ a a′ K K′} (σ : Simᴵ a ℓ) (ek : Simᴵ K ℓ) (σ′ : Simᴵ a′ ℓ′) (ek′ : Simᴵ K′ ℓ′) →
        a ≅ᴵ a′ → K ≅ᴵ K′ → sup a K σ ek ≅ᴵ sup a′ K′ σ′ ek′
sup-≅ σ ek σ′ ek′ eA z≅ = eA
sup-≅ σ ek σ′ ek′ eA (s≅ eK) = sup₁-≅ σ ek σ′ ek′ eA eK
sup-≅ σ ek σ′ ek′ eA (l≅ h) = l≅ (λ n → sup-≅ σ (λ q → ek (lim n q)) σ′ (λ q → ek′ (lim n q)) eA (h n))

accM : ∀ {i i′ ℓ ℓ′ φ₁ φ₁′ φ₂ φ₂′} (t : Top i ℓ φ₁) (t′ : Top i′ ℓ′ φ₁′) → φ₂ ∼ᶠ φ₂′ →
       (ev : Ev ℓ φ₂) (ev′ : Ev ℓ′ φ₂′) → Bd t ≅ᴵ Bd t′ → Bd (accT t φ₂ ev) ≅ᴵ Bd (accT t′ φ₂′ ev′)
accM t t′ fz∼       ev ev′ eM = eM
accM t t′ (fk∼ eK)  ev ev′ eM = sup₁-≅ (sb t) ev (sb t′) ev′ eM eK
accM t t′ (fb∼ eK)  ev ev′ eM = sup-≅ (sb t) ev (sb t′) ev′ eM eK
accM t t′ (zk∼ k0)  ev ev′ eM = ≅ᴵ-trans eM (≅ᴵ-sym (sup₁-triv (Bd t′) _ (sb t′) ev′ (nz t′) k0))
accM t t′ (kz∼ k0)  ev ev′ eM = ≅ᴵ-trans (sup₁-triv (Bd t) _ (sb t) ev (nz t) k0) eM
accM t t′ (⊔∼ a b) (x , y) (x′ , y′) eM = accM (accT t _ x) (accT t′ _ x′) b y y′ (accM t t′ a x x′ eM)

bound-≅ : ∀ {i i′ ℓ ℓ′ φ φ′} → φ ∼ᶠ φ′ → (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ φ′) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ →
          Bd (bound φ ev p) ≅ᴵ Bd (bound φ′ ev′ p′)
bound-≅ s ev p ev′ p′ ei = accM (top₀ p) (top₀ p′) s ev ev′ (s≅ ei)
```

## §12 边界
