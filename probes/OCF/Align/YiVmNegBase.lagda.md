# YiVmNeg：探针与前驱嵌入的计数引理

**验收文件，档位：编译定理。** 为 `YiVmNegSeg`、`YiVmNegIrr` 备料：严格的遗传步进 `SHS` (极限处相邻两项严格上升)；由布尔序列 α 决定的探针 `Y α` (α 全假时值 ω，否则 ω·2，各项严格上升)；`PEmb` 的三条组合引理 (`reflect` 反射，`cnt` 计数，`no-nat-ω`)。
本文不否定任何东西。入口：`YiVmNegSeg`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmNegBase where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-irrefl; m≤n⇒m≤1+n; ≤-pred; <-≤-trans)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.Level
open import OCF.Align.BTBOFullEmb using (PEmb)
open PEmb
```

## 1 层号里的自然数与 ω

```agda
nat≅inj : ∀ {u v} → natᴵ u ≅ᴵ natᴵ v → u ≡ v
nat≅inj {u = zero} {v = zero} _ = refl
nat≅inj {u = zero} {v = suc v} ()
nat≅inj {u = suc u} {v = zero} ()
nat≅inj {u = suc u} {v = suc v} (s≅ e) = cong suc (nat≅inj e)

nat< : ∀ {c t} → c <ᴵ natᴵ t → Σ ℕ λ u → u < t × c ≡ natᴵ u
nat< {t = zero} ()
nat< {t = suc t} zero = t , ≤-refl , refl
nat< {t = suc t} (suc q) with nat< q
... | u , lt , e = u , m≤n⇒m≤1+n lt , e

nat≺ : ∀ {c t} → c ≺ᴵ natᴵ t → Σ ℕ λ u → u < t × c ≅ᴵ natᴵ u
nat≺ (via e q) with nat< q
... | u , lt , refl = u , lt , e

nat≺nat : ∀ {u v} → natᴵ u ≺ᴵ natᴵ v → u < v
nat≺nat p with nat≺ p
... | w , lt , e with nat≅inj e
... | refl = lt

≺ω : ∀ {c} → c ≺ᴵ ωᴵ → Σ ℕ λ u → c ≅ᴵ natᴵ u
≺ω (via e (lim n q)) with nat< q
... | u , _ , refl = u , e

nat≺ω : ∀ u → natᴵ u ≺ᴵ ωᴵ
nat≺ω u = via (≅ᴵ-refl _) (lim (suc u) zero)

nz : ∀ {c} → ¬ (c ≺ᴵ zero)
nz (via _ ())

toLevel-nat : ∀ n (h : HS (natᶜ n)) → toLevel (natᶜ n) h ≅ᴵ natᴵ n
toLevel-nat zero    h = z≅
toLevel-nat (suc n) h = s≅ (toLevel-nat n (hs⁻ h))

toLevel-ω : ∀ (h : HS ωᶜ) → toLevel ωᶜ h ≅ᴵ ωᴵ
toLevel-ω h = l≅ (λ n → toLevel-nat n (hl₁ h n))
```

## 2 严格的遗传步进与探针

`SHS` 在 `HS` 上加一条：极限处相邻两项严格上升 (`f n ≺ f (suc n)`)。这排除常值与最终常值的极限，即 AGENTS 说的退化结点。

```agda
data SHS : Ordᶜ zero → Set where
  sz : SHS zero
  ss : ∀ {a} → SHS a → SHS (suc a)
  sl : ∀ {f : ℕ → Ordᶜ zero} → (∀ n → SHS (f n)) → (∀ n → f n ⊑⁰ f (suc n)) → (∀ n → f n ≺ f (suc n)) → SHS (lim f)

SHS→HS : ∀ {a} → SHS a → HS a
SHS→HS sz = hz
SHS→HS (ss s) = hs (SHS→HS s)
SHS→HS (sl s st lt) = hl (λ n → SHS→HS (s n)) st

SHS-nat : ∀ n → SHS (natᶜ n)
SHS-nat zero    = sz
SHS-nat (suc n) = ss (SHS-nat n)

SHS-ω : SHS ωᶜ
SHS-ω = sl SHS-nat (λ n d → ≺s d) (λ n → ≺z (≅-refl⁰ (natᶜ n)))

sω : ℕ → Ordᶜ zero
sω zero    = ωᶜ
sω (suc n) = suc (sω n)

SHS-sω : ∀ n → SHS (sω n)
SHS-sω zero    = SHS-ω
SHS-sω (suc n) = ss (SHS-sω n)

hb : Bool → ℕ → Ordᶜ zero
hb false n = natᶜ n
hb true  n = sω n

SHS-hb : ∀ b n → SHS (hb b n)
SHS-hb false n = SHS-nat n
SHS-hb true  n = SHS-sω n

seen : (ℕ → Bool) → ℕ → Bool
seen α zero    = α zero
seen α (suc n) = seen α n ∨ α (suc n)

seen-mono : ∀ α n → seen α n ≡ true → seen α (suc n) ≡ true
seen-mono α n e rewrite e = refl

seen-of : ∀ α k → α k ≡ true → seen α k ≡ true
seen-of α zero e = e
seen-of α (suc k) e with seen α k
... | true  = refl
... | false = e

seen→Σ : ∀ α n → seen α n ≡ true → Σ ℕ λ k → α k ≡ true
seen→Σ α zero e = zero , e
seen→Σ α (suc n) e with seen α n in s
... | true  = seen→Σ α n s
... | false = suc n , e

seen-F : ∀ α → (∀ k → α k ≡ false) → ∀ n → seen α n ≡ false
seen-F α f zero = f zero
seen-F α f (suc n) rewrite seen-F α f n = f (suc n)
```

探针 `Y α = lim (hb (seen α n) n)`：α 到第 n 位都假时第 n 项是 n，否则是 ω+n。

```agda
≺ω-up : ∀ n {ℓ} {c : Ordᶜ ℓ} → c ≺ ωᶜ → c ≺ sω n
≺ω-up zero    d = d
≺ω-up (suc n) d = ≺s (≺ω-up n d)

nat⊑hb : ∀ b n → natᶜ n ⊑⁰ hb b n
nat⊑hb false n d = d
nat⊑hb true  n d = ≺ω-up n (≺l n d)

step : ∀ b b′ → (b ≡ true → b′ ≡ true) → ∀ n → hb b n ⊑⁰ hb b′ (suc n)
step false false m n d = ≺s d
step false true  m n d = ≺s (≺ω-up n (≺l n d))
step true  false m n d with m refl
... | ()
step true  true  m n d = ≺s d

sstep : ∀ b b′ → (b ≡ true → b′ ≡ true) → ∀ n → hb b n ≺ hb b′ (suc n)
sstep false false m n = ≺z (≅-refl⁰ (natᶜ n))
sstep false true  m n = ≺s (≺ω-up n (≺l (suc n) (≺z (≅-refl⁰ (natᶜ n)))))
sstep true  false m n with m refl
... | ()
sstep true  true  m n = ≺z (≅-refl⁰ (sω n))

Y : (ℕ → Bool) → Ordᶜ zero
Y α = lim (λ n → hb (seen α n) n)

SY : ∀ α → SHS (Y α)
SY α = sl (λ n → SHS-hb (seen α n) n) (λ n → step _ _ (seen-mono α n) n) (λ n → sstep _ _ (seen-mono α n) n)

hY : ∀ α → HS (Y α)
hY α = SHS→HS (SY α)

hω : HS ωᶜ
hω = SHS→HS SHS-ω

ω⊑Y : ∀ α → ωᶜ ⊑⁰ Y α
ω⊑Y α (≺l n d) = ≺l n (nat⊑hb (seen α n) n d)

A : Ordᴵ
A = toLevel ωᶜ hω

B : (ℕ → Bool) → Ordᴵ
B α = toLevel (Y α) (hY α)

nsA : ∀ i → natᴵ i ≺ᴵ A
nsA i = ≺ᴵ-respʳ (nat≺ω i) (≅ᴵ-sym (toLevel-ω hω))
```

`B α` 的字面前驱：第 n 项若 α 到 n 都假，前驱都是自然数 (`inB`)；α 到 n 有真时，ω 是它的前驱 (`ω≺hbT`)，而 `B α` 与 ω 不结构互模拟 (`ω≇B`)。

```agda
inB : ∀ b n (hh : HS (hb b n)) {m′} → m′ <ᴵ toLevel (hb b n) hh → b ≡ true ⊎ Σ ℕ λ t → m′ ≅ᴵ natᴵ t
inB true  n hh q = inj₁ refl
inB false n hh q with nat≺ (<-≅ q (toLevel-nat n hh))
... | t , _ , e = inj₂ (t , e)

ω≺sω : ∀ n (hh : HS (sω (suc n))) → ωᴵ ≺ᴵ toLevel (sω (suc n)) hh
ω≺sω zero    hh = via (≅ᴵ-sym (toLevel-ω (hs⁻ hh))) zero
ω≺sω (suc n) hh = ≺-suc (ω≺sω n (hs⁻ hh))

ω≺hbT : ∀ b n (hh : HS (hb b (suc n))) → b ≡ true → ωᴵ ≺ᴵ toLevel (hb b (suc n)) hh
ω≺hbT true n hh refl = ω≺sω n hh

nat≇sω : ∀ k (hh : HS (sω k)) → ¬ (natᴵ k ≅ᴵ toLevel (sω k) hh)
nat≇sω zero    hh ()
nat≇sω (suc k) hh (s≅ e) = nat≇sω k (hs⁻ hh) e

hbT≇ : ∀ b k (hh : HS (hb b k)) → b ≡ true → ¬ (natᴵ k ≅ᴵ toLevel (hb b k) hh)
hbT≇ true k hh refl = nat≇sω k hh

hbF≅ : ∀ b k (hh : HS (hb b k)) → b ≡ false → toLevel (hb b k) hh ≅ᴵ natᴵ k
hbF≅ false k hh refl = toLevel-nat k hh

ω≺B : ∀ α k → α k ≡ true → ωᴵ ≺ᴵ B α
ω≺B α k e = ≺-lim (suc k) (ω≺hbT (seen α (suc k)) k (hl₁ (hY α) (suc k)) (seen-mono α k (seen-of α k e)))

ω≇B : ∀ α k → α k ≡ true → ¬ (ωᴵ ≅ᴵ B α)
ω≇B α k e (l≅ h) = hbT≇ (seen α k) k (hl₁ (hY α) k) (seen-of α k e) (h k)
```

## 3 前驱嵌入的组合引理

`reflect`：嵌入反射严格序 (源层号内的有界三歧 `<ᴵ-dec` 加目标里的无自反)。`cnt`：一个前驱下面有一切自然数时，它的像不 `≅ᴵ` 任何自然数。`no-nat-ω`：像向下封闭 (只要双重否定) 时，自然数的像不 `≅ᴵ` ω。

```agda
reflect : ∀ {a b} (P : PEmb a b) {c d} (r : c ≺ᴵ a) (s : d ≺ᴵ a) → map P r ≺ᴵ map P s → c ≺ᴵ d
reflect P r@(via e q) s@(via e′ q′) lt with <ᴵ-dec q q′
... | inj₁ x = ≺ᴵ-respʳ (≺ᴵ-respˡ e x) (≅ᴵ-sym e′)
... | inj₂ (inj₁ x) = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans lt (mono P s r (≺ᴵ-respʳ (≺ᴵ-respˡ e′ x) (≅ᴵ-sym e)))))
... | inj₂ (inj₂ x) = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ lt (≅ᴵ-sym (coh P r s (≅ᴵ-trans e (≅ᴵ-trans x (≅ᴵ-sym e′)))))))

cnt : ∀ {a b} (P : PEmb a b) {c} (r : c ≺ᴵ a) (ns : ∀ i → natᴵ i ≺ᴵ c) {t} → map P r ≅ᴵ natᴵ t → ⊥
cnt P r ns {t} e = fin (go t)
  where
  rᵢ : ∀ i → natᴵ i ≺ᴵ _
  rᵢ i = ≺ᴵ-trans (ns i) r
  bel : ∀ i → Σ ℕ λ u → u < t × map P (rᵢ i) ≅ᴵ natᴵ u
  bel i = nat≺ (≺ᴵ-respʳ (mono P (rᵢ i) r (ns i)) e)
  go : ∀ i → Σ ℕ λ u → i ≤ u × u < t × map P (rᵢ i) ≅ᴵ natᴵ u
  go zero with bel zero
  ... | u , lt , eu = u , z≤n , lt , eu
  go (suc i) with go i | bel (suc i)
  ... | u , iu , _ , eu | u′ , lt′ , eu′ =
    u′ , ≤-trans (s≤s iu) (nat≺nat (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym eu)
           (mono P (rᵢ i) (rᵢ (suc i)) (via (≅ᴵ-refl _) zero))) eu′)) , lt′ , eu′
  fin : (Σ ℕ λ u → t ≤ u × u < t × map P (rᵢ t) ≅ᴵ natᴵ u) → ⊥
  fin (u , tu , ut , _) = <-irrefl refl (<-≤-trans ut tu)

Down : ∀ {a b} → PEmb a b → Set
Down {a} P = ∀ {c} (r : c ≺ᴵ a) {e} → e ≺ᴵ map P r → Σ Ordᴵ λ d → Σ (d ≺ᴵ a) λ s → map P s ≅ᴵ e

Down¬¬ : ∀ {a b} → PEmb a b → Set
Down¬¬ {a} P = ∀ {c} (r : c ≺ᴵ a) {e} → e ≺ᴵ map P r → ¬ ¬ (Σ Ordᴵ λ d → Σ (d ≺ᴵ a) λ s → map P s ≅ᴵ e)

no-nat-ω : ∀ {a b} (P : PEmb a b) → Down¬¬ P → ∀ {d} (s : d ≺ᴵ a) j → d ≅ᴵ natᴵ j → map P s ≅ᴵ ωᴵ → ⊥
no-nat-ω P dn s zero ed em = dn s z≺ λ { (d″ , s″ , e″) →
  nz (≺ᴵ-respʳ (reflect P s″ s (≺ᴵ-respˡ e″ z≺)) ed) }
  where z≺ = ≺ᴵ-respʳ (nat≺ω 0) (≅ᴵ-sym em)
no-nat-ω {a} P dn {d} s (suc w) ed em = go (≺ω (≺ᴵ-respʳ (mono P rc s cw) em))
  where
  cw : natᴵ w ≺ᴵ d
  cw = ≺ᴵ-respʳ (via (≅ᴵ-refl (natᴵ w)) zero) (≅ᴵ-sym ed)
  rc : natᴵ w ≺ᴵ a
  rc = ≺ᴵ-trans cw s
  go : (Σ ℕ λ u → map P rc ≅ᴵ natᴵ u) → ⊥
  go (u , eu) = dn s z1 λ { (d′ , s′ , e′) → fin d′ s′ e′ }
    where
    z1 : natᴵ (suc u) ≺ᴵ map P s
    z1 = ≺ᴵ-respʳ (nat≺ω (suc u)) (≅ᴵ-sym em)
    fin : ∀ d′ (s′ : d′ ≺ᴵ a) → map P s′ ≅ᴵ natᴵ (suc u) → ⊥
    fin d′ s′ e′ with nat≺ (≺ᴵ-respʳ (reflect P s′ s (≺ᴵ-respˡ e′ z1)) ed)
    ... | v , vw , ev =
      <-irrefl refl (<-≤-trans
        (nat≺nat (≺ᴵ-respʳ (reflect P rc s′ (≺ᴵ-respʳ (≺ᴵ-respˡ eu (via (≅ᴵ-refl (natᴵ u)) zero)) (≅ᴵ-sym e′))) ev))
        (≤-pred vw))
```
