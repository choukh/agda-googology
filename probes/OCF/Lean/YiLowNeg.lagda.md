# YiLow：严格树上的前驱嵌入推出 LPO

**验收文件，档位：编译定理 (否定)。** `embVˢ→LPO : EmbVˢ → LPO` (于是 `YiMonoVM.EmbV` 也推出 LPO，`embV→LPO`)，只用一个固定的 x = ω+ω² (`xP`) 与由 α 决定的严格树 `yP α`；两边都是 `SHS`，推导 `der α` 对一切 α 一致给出。
机制：嵌入必须给 ω 选像。α 全假时 `z₀ α` 是 ω，像只能在它之上 (`cnt`)；α 有真位时 `z₀ α` 之上只剩 ω·k 的空间，放不下 ω² (`room`)。读像落在 `z₀ α` 哪一边就判定了 α。
不否定 `VMˢ` 本身 (ψ⁰ 层的左极限不要一致性)，也不否定读推导的嵌入在更窄的定义域上成立。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLowNeg where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _≤?_)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n; ≰⇒>; ≤-pred; <⇒≤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Barrier using (LPO)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≼-suc; ≼lim⁻; ≅→≼; ≺→s≼; ≼-+ʳ; +-mono)
open import OCF.Align.BTBOFullEmb using (PEmb)
open PEmb
open import OCF.Align.YiVmNegBase using (SHS; sz; ss; sl; SHS→HS; SHS-nat; SHS-ω; seen; seen-mono; seen-of; seen→Σ;
  nat≺; nat≺ω; toLevel-nat; toLevel-ω; cnt)
open import OCF.Align.YiVmNegBound using (forget-≅ᴵ; forget-<; forget-≺; no-back)
open import OCF.Align.YiVmConExact using (irr)
open import OCF.Lean.YiLowBase using (EmbVˢ)
open import OCF.Align.YiMonoVM using (EmbV)
```

## 1 第 0 层的加法

```agda
≺→⊑ : ∀ {b b′ : Ordᶜ zero} → b ≺ b′ → b ⊑⁰ b′
≺→⊑ (≺z e) h = ≺s (≺-respʳ h e)
≺→⊑ (≺s d) h = ≺s (≺→⊑ d h)
≺→⊑ (≺l n d) h = ≺l n (≺→⊑ d h)
≺→⊑ (≺i {p = ()} x ex d) h
≺→⊑ (≺u {r = ()} d) h

add-≺ : ∀ (A : Ordᶜ zero) {b b′ : Ordᶜ zero} → b ≺ b′ → A + b ≺ A + b′
add-≺ A (≺z e) = ≺z (add-≅ (≅-refl⁰ A) e)
add-≺ A (≺s d) = ≺s (add-≺ A d)
add-≺ A (≺l n d) = ≺l n (add-≺ A d)
add-≺ A (≺i {p = ()} x ex d)
add-≺ A (≺u {r = ()} d)

A⊑A+ : ∀ (A b : Ordᶜ zero) → A ⊑⁰ A + b
A⊑A+ A zero h = h
A⊑A+ A (suc b) h = ≺s (A⊑A+ A b h)
A⊑A+ A (lim f) h = ≺l 0 (A⊑A+ A (f 0) h)
A⊑A+ A (limᵢ () f) h
A⊑A+ A (up () x) h

add-⊑ : ∀ (A : Ordᶜ zero) {b b′ : Ordᶜ zero} → b ⊑⁰ b′ → A + b ⊑⁰ A + b′
add-⊑ A {b = zero} {b′} k h = A⊑A+ A b′ h
add-⊑ A {b = suc b} k (≺z e) = ≺-respˡ (≅-sym e) (add-≺ A (k (≺z (≅-refl⁰ b))))
add-⊑ A {b = suc b} k (≺s h) = add-⊑ A {b} (λ d → k (≺s d)) h
add-⊑ A {b = lim f} k (≺l n h) = add-⊑ A {f n} (λ d → k (≺l n d)) h
add-⊑ A {b = limᵢ () f} k h
add-⊑ A {b = up () x} k h

SHS-+ : ∀ {A B : Ordᶜ zero} → SHS A → SHS B → SHS (A + B)
SHS-+ sA sz = sA
SHS-+ sA (ss sB) = ss (SHS-+ sA sB)
SHS-+ {A} sA (sl sf st lt) = sl (λ n → SHS-+ sA (sf n)) (λ n → add-⊑ A (st n)) (λ n → add-≺ A (lt n))

HS-+ : ∀ {A B : Ordᶜ zero} → HS A → HS B → HS (A + B)
HS-+ hA hz = hA
HS-+ hA (hs hB) = hs (HS-+ hA hB)
HS-+ {A} hA (hl hf st) = hl (λ n → HS-+ hA (hf n)) (λ n → add-⊑ A (st n))

forget-⊑ : ∀ {a b} → a ⊑ᴵ b → forget a ⊑⁰ forget b
forget-⊑ z⊑ ()
forget-⊑ (s⊑ e q) (≺z e′) = ≺-respˡ (≅-sym (≅-trans e′ (forget-≅ᴵ e))) (forget-< q)
forget-⊑ (s⊑ e q) (≺s h) = ≺→⊑ (≺-respˡ (≅-sym (forget-≅ᴵ e)) (forget-< q)) h
forget-⊑ (l⊑ k) (≺l n h) = forget-⊑ (k n) h

HS-forget : ∀ a → HS (forget a)
HS-forget zero = hz
HS-forget (suc a) = hs (HS-forget a)
HS-forget (lim f s) = hl (λ n → HS-forget (f n)) (λ n → forget-⊑ (s n))
```

## 2 值序：左消去与相对的秩

`rel-val`：层号 T 的前驱保序地映到 [v, w) 里，则 v + T ≼ w (值)。

```agda
l≼⁻ : ∀ {f : ℕ → Ordᶜ zero} {b : Ordᶜ zero} → lim f ≼ b → ∀ n → f n ≼ b
l≼⁻ (l≼ h) n = h n
l≼⁻ (≼l k d) n = ≼l k (l≼⁻ d n)
l≼⁻ (≼i {p = ()} x ex d) n
l≼⁻ (≼u {r = ()} d) n

lc : ∀ (A P Q : Ordᶜ zero) → A + P ≼ A + Q → P ≼ Q
lc A zero Q d = z≼
lc A (suc P) zero d = ⊥-elim (irr A (≼-trans (s≼s (≼-+ʳ A P)) d))
lc A (suc P) (suc Q) (s≼s d) = s≼s (lc A P Q d)
lc A (suc P) (lim q) (≼l n d) = ≼l n (lc A (suc P) (q n) d)
lc A (suc P) (limᵢ () f) d
lc A (suc P) (up () x) d
lc A (lim p) Q d = l≼ (λ n → lc A (p n) Q (l≼⁻ d n))
lc A (limᵢ () f) Q d
lc A (up () x) Q d

ω⋠nat : ∀ m → ¬ (ωᶜ ≼ natᶜ m)
ω⋠nat m d = irr (natᶜ m) (l≼⁻ d (suc m))

≺→≼f : ∀ {a b} → a ≺ᴵ b → forget a ≼ forget b
≺→≼f p = ≼-trans (≼-suc (≼-refl _)) (≺→s≼ (forget-≺ p))

≅→≼f : ∀ {a b} → a ≅ᴵ b → forget a ≼ forget b
≅→≼f e = ≅→≼ (forget-≅ᴵ e)

rel-val : ∀ (T v w : Ordᴵ) (g : ∀ {d} → d ≺ᴵ T → Ordᴵ) →
  (∀ {d d′} (r : d ≺ᴵ T) (s : d′ ≺ᴵ T) → d ≺ᴵ d′ → g r ≺ᴵ g s) →
  (∀ {d} (r : d ≺ᴵ T) → g r ≺ᴵ w) →
  (∀ {d} (r : d ≺ᴵ T) → forget v ≼ forget (g r)) →
  forget v ≼ forget w →
  forget v + forget T ≼ forget w
rel-val zero v w g mo bd lo vw = vw
rel-val (suc T) v w g mo bd lo vw =
  ≼-trans (s≼s (rel-val T v (g t) (λ r → g (≺-suc r)) (λ r s lt → mo (≺-suc r) (≺-suc s) lt)
                  (λ r → mo (≺-suc r) t r) (λ r → lo (≺-suc r)) (lo t)))
          (≺→s≼ (forget-≺ (bd t)))
  where
  t : T ≺ᴵ suc T
  t = via (≅ᴵ-refl T) zero
rel-val (lim f s) v w g mo bd lo vw =
  l≼ (λ n → rel-val (f n) v w (λ r → g (≺-lim n r)) (λ r s′ lt → mo (≺-lim n r) (≺-lim n s′) lt)
              (λ r → bd (≺-lim n r)) (λ r → lo (≺-lim n r)) vw)

tri : ∀ {a b c} → a ≺ᴵ c → b ≺ᴵ c → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
tri (via e p) (via e′ q) with <ᴵ-dec p q
... | inj₁ x = inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ e x) (≅ᴵ-sym e′))
... | inj₂ (inj₁ x) = inj₂ (inj₁ (≺ᴵ-respʳ (≺ᴵ-respˡ e′ x) (≅ᴵ-sym e)))
... | inj₂ (inj₂ x) = inj₂ (inj₂ (≅ᴵ-trans e (≅ᴵ-trans x (≅ᴵ-sym e′))))
```

## 3 探针

x = ω + ω² 固定。`z₀ α` 的第 j 项：α 到 j 都假时是 j，否则是 ω² + j。`cc α` 在 α 假时每步加 ω，有真位后每步加 1。`yP α = z₀ α + lim (cc α)`。

```agda
mulω : ℕ → Ordᶜ zero
mulω zero = zero
mulω (suc k) = mulω k + ωᶜ

+ω-step : ∀ (t : Ordᶜ zero) → t ≺ t + ωᶜ
+ω-step t = ≺l 1 (≺z (≅-refl⁰ t))

SHS-mulω : ∀ k → SHS (mulω k)
SHS-mulω zero = sz
SHS-mulω (suc k) = SHS-+ (SHS-mulω k) SHS-ω

Bω : Ordᶜ zero
Bω = lim (λ n → mulω (suc n))

SHS-B : SHS Bω
SHS-B = sl (λ n → SHS-mulω (suc n)) (λ n → ≺→⊑ (+ω-step _)) (λ n → +ω-step _)

xP : Ordᶜ zero
xP = ωᶜ + Bω

SHS-x : SHS xP
SHS-x = SHS-+ SHS-ω SHS-B

hbz : Bool → ℕ → Ordᶜ zero
hbz false j = natᶜ j
hbz true  j = Bω + natᶜ j

nat≅0+ : ∀ j → natᶜ j ≅ (zero + natᶜ j)
nat≅0+ zero = z≅
nat≅0+ (suc j) = s≅ (nat≅0+ j)

nat≺B : ∀ j → natᶜ j ≺ Bω
nat≺B j = ≺l 0 (≺l (suc j) (≺z (nat≅0+ j)))

hbz-step : ∀ b b′ → (b ≡ true → b′ ≡ true) → ∀ j → hbz b j ≺ hbz b′ (suc j)
hbz-step false false m j = ≺z (≅-refl⁰ (natᶜ j))
hbz-step false true  m j = ≺s (A⊑A+ Bω (natᶜ j) (nat≺B j))
hbz-step true  false m j with m refl
... | ()
hbz-step true  true  m j = ≺z (≅-refl⁰ (Bω + natᶜ j))

SHS-hbz : ∀ b j → SHS (hbz b j)
SHS-hbz false j = SHS-nat j
SHS-hbz true  j = SHS-+ SHS-B (SHS-nat j)

z₀ : (ℕ → Bool) → Ordᶜ zero
z₀ α = lim (λ j → hbz (seen α j) j)

SHS-z₀ : ∀ α → SHS (z₀ α)
SHS-z₀ α = sl (λ j → SHS-hbz (seen α j) j) (λ j → ≺→⊑ (hbz-step _ _ (seen-mono α j) j))
  (λ j → hbz-step _ _ (seen-mono α j) j)

cstep : Bool → Ordᶜ zero → Ordᶜ zero
cstep false t = t + ωᶜ
cstep true  t = suc t

cc : (ℕ → Bool) → ℕ → Ordᶜ zero
cc α zero = zero
cc α (suc m) = cstep (seen α (suc m)) (cc α m)

cstep-step : ∀ b t → t ≺ cstep b t
cstep-step false t = +ω-step t
cstep-step true  t = ≺z (≅-refl⁰ t)

SHS-cstep : ∀ b {t} → SHS t → SHS (cstep b t)
SHS-cstep false st = SHS-+ st SHS-ω
SHS-cstep true  st = ss st

SHS-cc : ∀ α m → SHS (cc α m)
SHS-cc α zero = sz
SHS-cc α (suc m) = SHS-cstep (seen α (suc m)) (SHS-cc α m)

Cα : (ℕ → Bool) → Ordᶜ zero
Cα α = lim (cc α)

SHS-C : ∀ α → SHS (Cα α)
SHS-C α = sl (SHS-cc α) (λ m → ≺→⊑ (cstep-step _ _)) (λ m → cstep-step _ _)

yP : (ℕ → Bool) → Ordᶜ zero
yP α = z₀ α + Cα α

SHS-y : ∀ α → SHS (yP α)
SHS-y α = SHS-+ (SHS-z₀ α) (SHS-C α)
```

## 4 一致的推导

α 到第 n+1 位都假时，第 n 项 ω + ω·(n+1) 放在 `z₀ α` 的 ω 之上加 ω·(n+1)；有真位时放进 `z₀ α` 的 ω² 部分。

```agda
nat≼+ : ∀ (A : Ordᶜ zero) j → natᶜ j ≼ A + natᶜ j
nat≼+ A zero = z≼
nat≼+ A (suc j) = s≼s (nat≼+ A j)

nat≼hbz : ∀ b j → natᶜ j ≼ hbz b j
nat≼hbz false j = ≼-refl (natᶜ j)
nat≼hbz true  j = nat≼+ Bω j

ω≼z₀ : ∀ α → ωᶜ ≼ z₀ α
ω≼z₀ α = l≼ (λ j → ≼l j (nat≼hbz (seen α j) j))

B≼hbz : ∀ b j → b ≡ true → Bω ≼ hbz b j
B≼hbz true j refl = ≼-+ʳ Bω (natᶜ j)

assoc-nat : ∀ (A B : Ordᶜ zero) n → (A + (B + natᶜ n)) ≅ ((A + B) + natᶜ n)
assoc-nat A B zero = ≅-refl⁰ (A + B)
assoc-nat A B (suc n) = s≅ (assoc-nat A B n)

ω+mulω : ∀ m → ωᶜ + mulω m ≼ mulω (suc m)
ω+mulω zero = l≼ (λ n → ≼l n (≅→≼ (nat≅0+ n)))
ω+mulω (suc m) = l≼ (λ n → ≼l n (≼-trans (≅→≼ (assoc-nat ωᶜ (mulω m) n)) (+-mono (ω+mulω m) (≼-refl (natᶜ n)))))

cstep-false : ∀ b t → b ≡ false → cstep b t ≡ t + ωᶜ
cstep-false false t refl = refl

cstep-true : ∀ b t → b ≡ true → cstep b t ≡ suc t
cstep-true true t refl = refl

∨-false : ∀ a b → a ∨ b ≡ false → a ≡ false
∨-false false b e = refl
∨-false true b ()

cc-false : ∀ α m → seen α m ≡ false → cc α m ≡ mulω m
cc-false α zero e = refl
cc-false α (suc m) e =
  trans (cstep-false (seen α (suc m)) (cc α m) e) (cong (_+ ωᶜ) (cc-false α m (∨-false (seen α m) (α (suc m)) e)))

der : ∀ α → xP ≼ yP α
der α = l≼ D
  where
  D : ∀ n → ωᶜ + mulω (suc n) ≼ yP α
  D n = Dc (seen α (suc n)) refl
    where
    Dc : ∀ b → seen α (suc n) ≡ b → ωᶜ + mulω (suc n) ≼ yP α
    Dc false e = ≼l (suc n) (subst (λ t → ωᶜ + mulω (suc n) ≼ z₀ α + t) (sym (cc-false α (suc n) e))
      (+-mono (ω≼z₀ α) (≼-refl (mulω (suc n)))))
    Dc true e = ≼-trans (ω+mulω (suc n)) (≼-trans (≼l (suc n) (≼-refl (mulω (suc (suc n)))))
      (≼-trans (≼l (suc n) (B≼hbz (seen α (suc n)) (suc n) e)) (≼-+ʳ (z₀ α) (Cα α))))
```

## 5 读出判定

```agda
EmbX : Set
EmbX = ∀ (y : Ordᶜ zero) (sy : SHS y) → xP ≼ y → PEmb (toLevel xP (SHS→HS SHS-x)) (toLevel y (SHS→HS sy))

embVˢ→embX : EmbVˢ → EmbX
embVˢ→embX ev y sy d = ev xP (SHS→HS SHS-x) y (SHS→HS sy) SHS-x sy d

inZ : ∀ b j (h : HS (hbz b j)) {m} → m <ᴵ toLevel (hbz b j) h → b ≡ true ⊎ Σ ℕ λ u → m ≅ᴵ natᴵ u
inZ true  j h q = inj₁ refl
inZ false j h q with nat≺ (<-≅ q (toLevel-nat j h))
... | u , _ , e = inj₂ (u , e)

t≢f : true ≡ false → ⊥
t≢f ()

mulω-mono : ∀ {a b} → a ≤ b → mulω a ≼ mulω b
mulω-mono {a} {b = zero} z≤n = ≼-refl zero
mulω-mono {a} {b = suc b} p with m≤n⇒m<n∨m≡n p
... | inj₁ q = ≼-trans (mulω-mono (≤-pred q)) (≼-+ʳ (mulω b) ωᶜ)
... | inj₂ refl = ≼-refl _

module Probe (ex : EmbX) (α : ℕ → Bool) where
  hx : HS xP
  hx = SHS→HS SHS-x
  hω : HS ωᶜ
  hω = SHS→HS SHS-ω
  hy : HS (yP α)
  hy = SHS→HS (SHS-y α)
  hz₀ : HS (z₀ α)
  hz₀ = SHS→HS (SHS-z₀ α)
  hB : HS Bω
  hB = SHS→HS SHS-B

  E : PEmb (toLevel xP hx) (toLevel (yP α) hy)
  E = ex (yP α) (SHS-y α) (der α)

  rω : toLevel ωᶜ hω ≺ᴵ toLevel xP hx
  rω = toLevel-≺ hω hx (≺l 0 (≺l 1 (≺z (≅-refl⁰ ωᶜ))))

  v : Ordᴵ
  v = map E rω

  z0≺Y : toLevel (z₀ α) hz₀ ≺ᴵ toLevel (yP α) hy
  z0≺Y = toLevel-≺ hz₀ hy (≺l 1 (add-≺ (z₀ α) (cstep-step (seen α 1) zero)))

  ns : ∀ i → natᴵ i ≺ᴵ toLevel ωᶜ hω
  ns i = ≺ᴵ-respʳ (nat≺ω i) (≅ᴵ-sym (toLevel-ω hω))

  low : v ≺ᴵ toLevel (z₀ α) hz₀ → Σ ℕ λ k → α k ≡ true
  low (via e (lim j q)) with inZ (seen α j) j (hl₁ hz₀ j) q
  ... | inj₁ t = seen→Σ α j t
  ... | inj₂ (u , e′) = ⊥-elim (cnt E rω ns (≅ᴵ-trans e e′))

  T : Ordᴵ
  T = toLevel Bω hB

  hfd : ∀ d → HS (ωᶜ + forget d)
  hfd d = HS-+ hω (HS-forget d)

  tp : ∀ {d} → d ≺ᴵ T → toLevel (ωᶜ + forget d) (hfd d) ≺ᴵ toLevel xP hx
  tp {d} r = toLevel-≺ (hfd d) hx (add-≺ ωᶜ (≺-respʳ (forget-≺ r) (forget-toLevel Bω hB)))

  g : ∀ {d} → d ≺ᴵ T → Ordᴵ
  g r = map E (tp r)

  g-mono : ∀ {d d′} (r : d ≺ᴵ T) (s : d′ ≺ᴵ T) → d ≺ᴵ d′ → g r ≺ᴵ g s
  g-mono {d} {d′} r s lt = mono E (tp r) (tp s) (toLevel-≺ (hfd d) (hfd d′) (add-≺ ωᶜ (forget-≺ lt)))

  g-lo : ∀ {d} (r : d ≺ᴵ T) → forget v ≼ forget (g r)
  g-lo {d} r with tri rω (tp r)
  ... | inj₁ lt = ≺→≼f (mono E rω (tp r) lt)
  ... | inj₂ (inj₁ gt) = ⊥-elim (no-back ωᶜ hω (ωᶜ + forget d) (hfd d) gt (≼-+ʳ ωᶜ (forget d)))
  ... | inj₂ (inj₂ eq) = ≅→≼f (coh E rω (tp r) eq)

  rv : forget v + forget T ≼ forget (toLevel (yP α) hy)
  rv = rel-val T v (toLevel (yP α) hy) g g-mono (λ r → bnd E (tp r)) g-lo (≺→≼f (bnd E rω))

  seen-≤ : ∀ {j n} → j ≤ n → seen α j ≡ true → seen α n ≡ true
  seen-≤ {j} {n = zero} z≤n e = e
  seen-≤ {j} {n = suc n} p e with m≤n⇒m<n∨m≡n p
  ... | inj₁ q = seen-mono α n (seen-≤ (≤-pred q) e)
  ... | inj₂ refl = e

  below-k : ∀ k → α k ≡ true → ∀ n → seen α n ≡ false → n < k
  below-k k ek n e with k ≤? n
  ... | yes p = ⊥-elim (t≢f (trans (sym (seen-≤ p (seen-of α k ek))) e))
  ... | no ¬p = ≰⇒> ¬p

  cc-bound : ∀ k → α k ≡ true → ∀ m → cc α m ≼ mulω k + natᶜ m
  cc-bound k ek zero = z≼
  cc-bound k ek (suc m) = cb (seen α (suc m)) refl
    where
    cb : ∀ b → seen α (suc m) ≡ b → cc α (suc m) ≼ mulω k + natᶜ (suc m)
    cb true e = subst (λ t → t ≼ mulω k + natᶜ (suc m)) (sym (cstep-true (seen α (suc m)) (cc α m) e))
      (s≼s (cc-bound k ek m))
    cb false e = subst (λ t → t ≼ mulω k + natᶜ (suc m)) (sym (cc-false α (suc m) e))
      (≼-trans (mulω-mono (<⇒≤ (below-k k ek (suc m) e))) (≼-+ʳ (mulω k) (natᶜ (suc m))))

  room : z₀ α ≼ forget v → ∀ k → α k ≡ true → ⊥
  room zle k ek with ≼lim⁻ (≼-trans (≼l (suc k) (≼l 1 (≼-refl (suc (mulω (suc k)))))) s1)
    where
    s1 : Bω ≼ Cα α
    s1 = lc (z₀ α) Bω (Cα α) (≼-trans (+-mono zle (≼-refl Bω))
           (≼-trans (+-mono (≼-refl (forget v)) (≅→≼ (≅-sym (forget-toLevel Bω hB))))
             (≼-trans rv (≅→≼ (forget-toLevel (yP α) hy)))))
  ... | m , d = ω⋠nat m (≼-trans (≼-suc (≼-refl ωᶜ))
                  (lc (mulω k) (suc ωᶜ) (natᶜ m) (≼-trans d (cc-bound k ek m))))

  allF : z₀ α ≼ forget v → ∀ k → α k ≡ false
  allF zle k = go (α k) refl
    where
    go : ∀ b → α k ≡ b → α k ≡ false
    go false e = e
    go true e = ⊥-elim (room zle k e)

  decide : (Σ ℕ λ k → α k ≡ true) ⊎ (∀ k → α k ≡ false)
  decide with tri (bnd E rω) z0≺Y
  ... | inj₁ lt = inj₁ (low lt)
  ... | inj₂ (inj₁ gt) = inj₂ (allF (≼-trans (≅→≼ (≅-sym (forget-toLevel (z₀ α) hz₀))) (≺→≼f gt)))
  ... | inj₂ (inj₂ eq) = inj₂ (allF (≼-trans (≅→≼ (≅-sym (forget-toLevel (z₀ α) hz₀))) (≅→≼f (≅ᴵ-sym eq))))

embX→LPO : EmbX → LPO
embX→LPO ex α = Probe.decide ex α

embVˢ→LPO : EmbVˢ → LPO
embVˢ→LPO ev = embX→LPO (embVˢ→embX ev)

embV→LPO : EmbV → LPO
embV→LPO ev = embX→LPO (λ y sy d → ev xP (SHS→HS SHS-x) y (SHS→HS sy) d)
```
