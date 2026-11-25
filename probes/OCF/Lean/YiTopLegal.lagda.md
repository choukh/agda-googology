# 顶槽位的块: 合法性

> 判决: 成品候选 (合法性). 空白页的合法性 (`YiFreshLegal`) 去掉槽位路径: 分支的合法性 `LegI` 只看下标层; 保留判定的归纳原理 (`Good`, `kp-ind`) 不再需要.
> 编译定理, 无前提: 折叠对第一位置序单调 (`mono⊥`, `monos`), 折叠保持合法 (`pres⊥`, `press`, 底合法且非零); `tw n`, `Λ` 合法, 它们的 Ω 树与读法 ψ₀(Λ) 的闭项 `EBOᶜ` 合法 (`EBOᶜ-leg`).
> 不否定什么. 层号的合法性同空白页, 不要求 `Ωₗ k h` 的下标层 k 本身合法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTopLegal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiTopBlock
open import OCF.Lean.YiTopFold
```

## 第一位置序与合法性

```agda
infix 4 _⊢_◃_
data _⊢_◃_ : (ℓ : L) → Tr ℓ → Tr ℓ → Set where
  ◃s : ∀ {ℓ x} → ℓ ⊢ x ◃ suc x
  ◃l : ∀ {ℓ f} (n : ℕ) → ℓ ⊢ f n ◃ lim f
  ◃w : ∀ {ℓ s g} → ℓ ⊢ g (z₀ ℓ s) ◃ Ω s g
  ◃u : ∀ {ℓ x c y} → chL ℓ c ⊢ zero ◃ chT ℓ c y → ℓ ⊢ x ◃ up x c y
  ◃c : ∀ {ℓ x c y′ y} → chL ℓ c ⊢ chT ℓ c y′ ◃ chT ℓ c y → ℓ ⊢ up x c y′ ◃ up x c y
  ◃t : ∀ {ℓ x y z} → ℓ ⊢ x ◃ y → ℓ ⊢ y ◃ z → ℓ ⊢ x ◃ z

mutual
  Leg : (ℓ : L) → Tr ℓ → Set
  Leg ℓ zero       = ⊤
  Leg ℓ (suc x)    = Leg ℓ x
  Leg ℓ (lim f)    = ((n : ℕ) → Leg ℓ (f n)) × ((n : ℕ) → ℓ ⊢ f n ◃ f (suc n))
  Leg ℓ (Ω s g)    = (z : Bt ℓ) → LegI ℓ z → Leg ℓ (g z)
  Leg ℓ (up x c y) = Leg ℓ x × LegCh ℓ c y × (chL ℓ c ⊢ zero ◃ chT ℓ c y)

  LegI : (ℓ : L) → Bt ℓ → Set
  LegI (suc a)  z = Leg a z
  LegI (Ωₗ k h) z = Leg k z
  LegI _        _ = ⊤

  LegCh : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Set
  LegCh (suc a)  _ y = Leg a y
  LegCh (lim g)  n y = Leg (g n) y
  LegCh (Ωₗ k h) c y = Leg (h c) y

z₀-leg : (ℓ : L) (s : Hd ℓ) → LegI ℓ (z₀ ℓ s)
z₀-leg (suc a)  _ = tt
z₀-leg (Ωₗ k h) _ = tt
```

## 运算的引理

```agda
+-mono : ∀ {ℓ a b} (c : Tr ℓ) → ℓ ⊢ a ◃ b → ℓ ⊢ c + a ◃ c + b
+-mono c ◃s       = ◃s
+-mono c (◃l n)   = ◃l n
+-mono c ◃w       = ◃w
+-mono c (◃u z)   = ◃u z
+-mono c (◃c d)   = ◃c d
+-mono c (◃t d e) = ◃t (+-mono c d) (+-mono c e)

+-leg : ∀ {ℓ} (a b : Tr ℓ) → Leg ℓ a → Leg ℓ b → Leg ℓ (a + b)
+-leg a zero       ha hb = ha
+-leg a (suc b)    ha hb = +-leg a b ha hb
+-leg a (lim f)    ha (hf , adj) = (λ n → +-leg a (f n) ha (hf n)) , (λ n → +-mono a (adj n))
+-leg a (Ω s g)    ha hb = λ z h → +-leg a (g z) ha (hb z h)
+-leg a (up y c w) ha (hy , hw , zw) = +-leg a y ha hy , hw , zw

ι-mono : ∀ {a b} (j : L) → zero ⊢ a ◃ b → j ⊢ ι j a ◃ ι j b
ι-mono j ◃s       = ◃s
ι-mono j (◃l n)   = ◃l n
ι-mono j (◃w {s = ()})
ι-mono j (◃u {c = ()} _)
ι-mono j (◃c {c = ()} _)
ι-mono j (◃t d e) = ◃t (ι-mono j d) (ι-mono j e)

ι-leg : (j : L) (a : Tr zero) → Leg zero a → Leg j (ι j a)
ι-leg j zero    h = tt
ι-leg j (suc a) h = ι-leg j a h
ι-leg j (lim f) (hf , adj) = (λ n → ι-leg j (f n) (hf n)) , (λ n → ι-mono j (adj n))
ι-leg j (Ω () _) h
ι-leg j (up _ () _) h

zl : ∀ {ℓ} (x : Tr ℓ) → Leg ℓ x → (zero ≡ x) ⊎ (ℓ ⊢ zero ◃ x)
zl zero h = inj₁ refl
zl (suc x) h with zl x h
... | inj₁ refl = inj₂ ◃s
... | inj₂ d    = inj₂ (◃t d ◃s)
zl (lim f) (hf , adj) with zl (f zero) (hf zero)
... | inj₁ e = inj₂ (subst (λ v → _ ⊢ v ◃ lim f) (sym e) (◃l zero))
... | inj₂ d = inj₂ (◃t d (◃l zero))
zl {ℓ} (Ω s g) h with zl (g (z₀ ℓ s)) (h _ (z₀-leg ℓ s))
... | inj₁ e = inj₂ (subst (λ v → ℓ ⊢ v ◃ Ω s g) (sym e) ◃w)
... | inj₂ d = inj₂ (◃t d ◃w)
zl (up x c y) (hx , hy , zy) with zl x hx
... | inj₁ refl = inj₂ (◃u zy)
... | inj₂ d    = inj₂ (◃t d (◃u zy))

z◃s : ∀ {ℓ} (x : Tr ℓ) → Leg ℓ x → ℓ ⊢ zero ◃ suc x
z◃s x h with zl x h
... | inj₁ refl = ◃s
... | inj₂ d    = ◃t d ◃s
```

## Ω 树合法且非零

```agda
seq : ∀ {S B C D} → T S B C D → ℕ → T S B C D
seq (lim f) = f
seq x       = λ _ → x

mutual
  Ωt-nz : (ℓ : L) → ℓ ⊢ zero ◃ Ωt ℓ
  Ωt-nz zero     = ◃s
  Ωt-nz (suc a)  = ◃t (◃u ◃s) ◃w
  Ωt-nz (lim g)  = ◃t (◃u (Ωt-nz (g zero))) (◃l zero)
  Ωt-nz (Ωₗ k h) = ◃t (◃u (Ωt-nz (h zero))) ◃w

  Ωt-leg : (ℓ : L) → Leg ℓ (Ωt ℓ)
  Ωt-leg zero     = tt
  Ωt-leg (suc a)  = λ z h → tt , h , z◃s z h
  Ωt-leg (lim g)  = cl , (λ n → ◃u (Ωt-nz (g (suc n))))
    where
    cl : (n : ℕ) → Leg (lim g) (seq (Ωt (lim g)) n)
    cl zero    = tt , Ωt-leg (g zero) , Ωt-nz (g zero)
    cl (suc n) = cl n , Ωt-leg (g (suc n)) , Ωt-nz (g (suc n))
  Ωt-leg (Ωₗ k h) = λ c _ → tt , Ωt-leg (h c) , Ωt-nz (h c)
```

## 折叠单调 (无前提)

```agda
dS : (a : L) → Base (suc a) → Tr (suc a) → Base a
dS a B x = base (ψ⊥ (suc a) B x) (λ j w → ψs (suc a) B j (ins w) x)

dL : (g : ℕ → L) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
dL g B n x = base (ψ⊥ (lim g) B x) (λ j w → ψs (lim g) B j (inl n w) x)

dW : (k : L) (h : Tr k → L) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
dW k h B c x = base (ψ⊥ (Ωₗ k h) B x) (λ j w → ψs (Ωₗ k h) B j (inb c w) x)

mutual
  fb : ∀ {j} (b : Tr j) (ℓ′ : L) {y : Tr ℓ′} → ℓ′ ⊢ zero ◃ y
     → j ⊢ b ◃ b + ι j (ψ⊥ ℓ′ (B₀ ℓ′) y)
  fb {j} b ℓ′ zy = +-mono b (ι-mono j (◃t ◃s (mono⊥ ℓ′ (B₀ ℓ′) zy)))

  mono⊥ : (ℓ : L) (B : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ B x ◃ ψ⊥ ℓ B y
  mono⊥ ℓ B ◃s     = ◃l zero
  mono⊥ ℓ B (◃l n) = ◃l n
  mono⊥ ℓ B ◃w     = ◃l zero
  mono⊥ (suc a)  B (◃u {x = x} zy)     = mono⊥ a (dS a B x) zy
  mono⊥ (lim g)  B (◃u {x = x} {c = n} zy) = mono⊥ (g n) (dL g B n x) zy
  mono⊥ (Ωₗ k h) B (◃u {x = x} {c = c} zy) = mono⊥ (h c) (dW k h B c x) zy
  mono⊥ (suc a)  B (◃c {x = x} d)     = mono⊥ a (dS a B x) d
  mono⊥ (lim g)  B (◃c {x = x} {c = n} d) = mono⊥ (g n) (dL g B n x) d
  mono⊥ (Ωₗ k h) B (◃c {x = x} {c = c} d) = mono⊥ (h c) (dW k h B c x) d
  mono⊥ ℓ B (◃t d e) = ◃t (mono⊥ ℓ B d) (mono⊥ ℓ B e)

  monos : (ℓ : L) (B : Base ℓ) (j : L) (v : j ≤ ℓ) {x y : Tr ℓ}
        → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ B j v x ◃ ψs ℓ B j v y
  monos ℓ B j v ◃s     = ◃l zero
  monos ℓ B j v (◃l n) = ◃l n
  monos ℓ        B _ self       ◃w = ◃w
  monos (suc a)  B j (ins v)    ◃w = ◃l zero
  monos (Ωₗ k h) B j (ink v)    ◃w = ◃l zero
  monos (Ωₗ k h) B j (inb c′ v) ◃w = ◃l zero
  monos (lim g)  B j (inl n v) (◃w {s = ()})
  monos ℓ        B _ self      (◃u zy) = ◃u zy
  monos (suc a)  B j (ins v)   (◃u {x = x} zy) = monos a (dS a B x) j v zy
  monos (lim g)  B j (inl n v) (◃u {x = x} {c = m} zy) with eqℕ m n
  ... | just refl = monos (g m) (dL g B m x) j v zy
  ... | nothing   = fb (ψs (lim g) B j (inl n v) x) (g m) zy
  monos (Ωₗ k h) B j (ink v)    (◃u {x = x} {c = c} zy) = fb (ψs (Ωₗ k h) B j (ink v) x) (h c) zy
  monos (Ωₗ k h) B j (inb c′ v) (◃u {x = x} {c = c} zy) = fb (ψs (Ωₗ k h) B j (inb c′ v) x) (h c) zy
  monos ℓ        B _ self      (◃c d) = ◃c d
  monos (suc a)  B j (ins v)   (◃c {x = x} d) = monos a (dS a B x) j v d
  monos (lim g)  B j (inl n v) (◃c {x = x} {c = m} d) with eqℕ m n
  ... | just refl = monos (g m) (dL g B m x) j v d
  ... | nothing   = +-mono (ψs (lim g) B j (inl n v) x) (ι-mono j (mono⊥ (g m) (B₀ (g m)) d))
  monos (Ωₗ k h) B j (ink v)    (◃c {x = x} {c = c} d) =
    +-mono (ψs (Ωₗ k h) B j (ink v) x) (ι-mono j (mono⊥ (h c) (B₀ (h c)) d))
  monos (Ωₗ k h) B j (inb c′ v) (◃c {x = x} {c = c} d) =
    +-mono (ψs (Ωₗ k h) B j (inb c′ v) x) (ι-mono j (mono⊥ (h c) (B₀ (h c)) d))
  monos ℓ B j v (◃t d e) = ◃t (monos ℓ B j v d) (monos ℓ B j v e)
```

## 折叠保持合法

```agda
LN : (j : L) → Tr j → Set
LN j x = Leg j x × (j ⊢ zero ◃ x)

LegB : (ℓ : L) → Base ℓ → Set
LegB ℓ B = LN zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → LN j (bs B j w))

LegB₀ : (ℓ : L) → LegB ℓ (B₀ ℓ)
LegB₀ ℓ = (Ωt-leg zero , Ωt-nz zero) , λ j _ → Ωt-leg j , Ωt-nz j

iterInv : {A : Set} (P : A → Set) (S : A → A) (a : A) → P a → ((z : A) → P z → P (S z))
        → (n : ℕ) → P (iter S a n)
iterInv P S a pa ps zero    = pa
iterInv P S a pa ps (suc n) = ps _ (iterInv P S a pa ps n)

nextLN : ∀ {j} (b : Tr j) → LN j b → LN j (next b)
nextLN {j} b (hb , zb) = (il , ia) , ◃t zb (◃l zero)
  where
  il : (n : ℕ) → Leg j (iter (b +_) b n)
  il zero    = hb
  il (suc n) = +-leg b _ hb (il n)
  ia : (n : ℕ) → j ⊢ iter (b +_) b n ◃ iter (b +_) b (suc n)
  ia zero    = +-mono b zb
  ia (suc n) = +-mono b (ia n)

cumLN : ∀ {j} (F : ℕ → Tr j) → ((n : ℕ) → LN j (F n)) → LN j (lim (cum F))
cumLN {j} F hF = (cl , λ n → +-mono (cum F n) (proj₂ (hF (suc n)))) , ◃t (proj₂ (hF zero)) (◃l zero)
  where
  cl : (n : ℕ) → Leg j (cum F n)
  cl zero    = proj₁ (hF zero)
  cl (suc n) = +-leg (cum F n) (F (suc n)) (cl n) (proj₁ (hF (suc n)))

mutual
  fbLN : ∀ {j} (b : Tr j) → LN j b → (ℓ′ : L) (y : Tr ℓ′) → Leg ℓ′ y → ℓ′ ⊢ zero ◃ y
       → LN j (b + ι j (ψ⊥ ℓ′ (B₀ ℓ′) y))
  fbLN {j} b (hb , zb) ℓ′ y hy zy =
    +-leg b _ hb (ι-leg j _ (proj₁ (pres⊥ ℓ′ (B₀ ℓ′) (LegB₀ ℓ′) y hy))) , ◃t zb (fb b ℓ′ zy)

  stp-leg : (ℓ : L) (B : Base ℓ) → LegB ℓ B → (s : Hd ℓ) (g : Bt ℓ → Tr ℓ)
          → ((z : Bt ℓ) → LegI ℓ z → Leg ℓ (g z)) → (z : Bt ℓ) → LegI ℓ z → LegI ℓ (stp ℓ B s g z)
  stp-leg (suc a)  B hB _ g h z hz = proj₁ (press (suc a) B hB a (ins self) (g z) (h z hz))
  stp-leg (Ωₗ k h′) B hB _ g h z hz = proj₁ (press (Ωₗ k h′) B hB k (ink self) (g z) (h z hz))

  pres⊥ : (ℓ : L) (B : Base ℓ) → LegB ℓ B → (x : Tr ℓ) → Leg ℓ x → LN zero (ψ⊥ ℓ B x)
  pres⊥ ℓ B hB zero    h = proj₁ hB
  pres⊥ ℓ B hB (suc x) h = nextLN _ (pres⊥ ℓ B hB x h)
  pres⊥ ℓ B hB (lim f) (hf , adj) =
    ((λ n → proj₁ (pres⊥ ℓ B hB (f n) (hf n))) , (λ n → mono⊥ ℓ B (adj n)))
    , ◃t (proj₂ (pres⊥ ℓ B hB (f zero) (hf zero))) (◃l zero)
  pres⊥ ℓ B hB (Ω s g) h =
    cumLN _ (λ n → pres⊥ ℓ B hB (g _) (h _ (iterInv (LegI ℓ) _ _ (z₀-leg ℓ s) (stp-leg ℓ B hB s g h) n)))
  pres⊥ (suc a)  B hB (up x _ y) (hx , hy , zy) =
    pres⊥ a (dS a B x) (pres⊥ (suc a) B hB x hx , λ j w → press (suc a) B hB j (ins w) x hx) y hy
  pres⊥ (lim g)  B hB (up x n y) (hx , hy , zy) =
    pres⊥ (g n) (dL g B n x) (pres⊥ (lim g) B hB x hx , λ j w → press (lim g) B hB j (inl n w) x hx) y hy
  pres⊥ (Ωₗ k h) B hB (up x c y) (hx , hy , zy) =
    pres⊥ (h c) (dW k h B c x) (pres⊥ (Ωₗ k h) B hB x hx , λ j w → press (Ωₗ k h) B hB j (inb c w) x hx) y hy

  press : (ℓ : L) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (x : Tr ℓ) → Leg ℓ x
        → LN j (ψs ℓ B j v x)
  press ℓ B hB j v zero    h = proj₂ hB j v
  press ℓ B hB j v (suc x) h = nextLN _ (press ℓ B hB j v x h)
  press ℓ B hB j v (lim f) (hf , adj) =
    ((λ n → proj₁ (press ℓ B hB j v (f n) (hf n))) , (λ n → monos ℓ B j v (adj n)))
    , ◃t (proj₂ (press ℓ B hB j v (f zero) (hf zero))) (◃l zero)
  press ℓ B hB _ self (Ω s g) h =
    (λ z hz → proj₁ (press ℓ B hB ℓ self (g z) (h z hz)))
    , ◃t (proj₂ (press ℓ B hB ℓ self (g (z₀ ℓ s)) (h _ (z₀-leg ℓ s)))) ◃w
  press (suc a)  B hB j (ins v)    (Ω s g) h = dfLN (suc a)  B hB j (ins v)    s g h
  press (Ωₗ k h′) B hB j (ink v)    (Ω s g) h = dfLN (Ωₗ k h′) B hB j (ink v)    s g h
  press (Ωₗ k h′) B hB j (inb c v) (Ω s g) h = dfLN (Ωₗ k h′) B hB j (inb c v) s g h
  press (lim g′) B hB j (inl n v) (Ω () g) h
  press ℓ B hB _ self (up x c y) (hx , hy , zy) =
    (proj₁ (press ℓ B hB ℓ self x hx) , hy , zy) , ◃t (proj₂ (press ℓ B hB ℓ self x hx)) (◃u zy)
  press (suc a) B hB j (ins v) (up x _ y) (hx , hy , zy) =
    press a (dS a B x) (pres⊥ (suc a) B hB x hx , λ j′ w′ → press (suc a) B hB j′ (ins w′) x hx) j v y hy
  press (lim g) B hB j (inl n v) (up x m y) (hx , hy , zy) with eqℕ m n
  ... | just refl =
    press (g m) (dL g B m x) (pres⊥ (lim g) B hB x hx , λ j′ w′ → press (lim g) B hB j′ (inl m w′) x hx) j v y hy
  ... | nothing = fbLN _ (press (lim g) B hB j (inl n v) x hx) (g m) y hy zy
  press (Ωₗ k h) B hB j (ink v)    (up x c y) (hx , hy , zy) =
    fbLN _ (press (Ωₗ k h) B hB j (ink v) x hx) (h c) y hy zy
  press (Ωₗ k h) B hB j (inb c′ v) (up x c y) (hx , hy , zy) =
    fbLN _ (press (Ωₗ k h) B hB j (inb c′ v) x hx) (h c) y hy zy

  dfLN : (ℓ : L) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (s : Hd ℓ) (g : Bt ℓ → Tr ℓ)
       → ((z : Bt ℓ) → LegI ℓ z → Leg ℓ (g z))
       → LN j (lim (cum (λ n → ψs ℓ B j v (g (iter (stp ℓ B s g) (z₀ ℓ s) n)))))
  dfLN ℓ B hB j v s g h =
    cumLN _ (λ n → press ℓ B hB j v (g _) (h _ (iterInv (LegI ℓ) _ _ (z₀-leg ℓ s) (stp-leg ℓ B hB s g h) n)))

ψ₀-leg : (ℓ : L) (x : Tr ℓ) → Leg ℓ x → Leg zero (ψ₀ ℓ x)
ψ₀-leg ℓ x h = proj₁ (pres⊥ ℓ (B₀ ℓ) (LegB₀ ℓ) x h)
```

## 层号的第一位置序与合法性

```agda
infix 4 _◃ₗ_
data _◃ₗ_ : L → L → Set where
  ◃ls : ∀ {a} → a ◃ₗ suc a
  ◃ll : ∀ {g} (n : ℕ) → g n ◃ₗ lim g
  ◃lw : ∀ {k h} → h zero ◃ₗ Ωₗ k h
  ◃lt : ∀ {a b c} → a ◃ₗ b → b ◃ₗ c → a ◃ₗ c

LegL : L → Set
LegL zero     = ⊤
LegL (suc a)  = LegL a
LegL (lim g)  = ((n : ℕ) → LegL (g n)) × ((n : ℕ) → g n ◃ₗ g (suc n))
LegL (Ωₗ k h) = (c : Tr k) → Leg k c → LegL (h c)

⊕-mono : ∀ {b b′} (a : L) → b ◃ₗ b′ → a ⊕ b ◃ₗ a ⊕ b′
⊕-mono a ◃ls       = ◃ls
⊕-mono a (◃ll n)   = ◃ll n
⊕-mono a ◃lw       = ◃lw
⊕-mono a (◃lt d e) = ◃lt (⊕-mono a d) (⊕-mono a e)

⊕-legL : (a b : L) → LegL a → LegL b → LegL (a ⊕ b)
⊕-legL a zero     ha hb = ha
⊕-legL a (suc b)  ha hb = ⊕-legL a b ha hb
⊕-legL a (lim g)  ha (hg , adj) = (λ n → ⊕-legL a (g n) ha (hg n)) , (λ n → ⊕-mono a (adj n))
⊕-legL a (Ωₗ k h) ha hb = λ c hc → ⊕-legL a (h c) ha (hb c hc)

mutual
  ↑-mono : (k : L) {x y : Tr k} → k ⊢ x ◃ y → ↑ k x ◃ₗ ↑ k y
  ↑-mono k        ◃s     = ◃ls
  ↑-mono k        (◃l n) = ◃ll n
  ↑-mono (suc a)  ◃w     = ◃lw
  ↑-mono (Ωₗ k h) ◃w     = ◃lw
  ↑-mono zero     (◃w {s = ()})
  ↑-mono (lim _)  (◃w {s = ()})
  ↑-mono (suc a)  (◃u {x = x} zy)         = ⊕-mono (↑ (suc a) x) (↑-mono a zy)
  ↑-mono (lim g)  (◃u {x = x} {c = n} zy) = ⊕-mono (↑ (lim g) x) (↑-mono (g n) zy)
  ↑-mono (Ωₗ k h) (◃u {x = x} {c = c} zy) = ⊕-mono (↑ (Ωₗ k h) x) (↑-mono (h c) zy)
  ↑-mono k        (◃c {x = x} {c = c} d)  = ⊕-mono (↑ k x) (↑ch-mono k c d)
  ↑-mono k        (◃t d e) = ◃lt (↑-mono k d) (↑-mono k e)

  ↑ch-mono : (k : L) (c : Ch k) {y′ y : ChT k c}
           → chL k c ⊢ chT k c y′ ◃ chT k c y → ↑ch k c y′ ◃ₗ ↑ch k c y
  ↑ch-mono (suc a)  _ d = ↑-mono a d
  ↑ch-mono (lim g)  n d = ↑-mono (g n) d
  ↑ch-mono (Ωₗ k h) c d = ↑-mono (h c) d

mutual
  ↑-legL : (k : L) (c : Tr k) → Leg k c → LegL (↑ k c)
  ↑-legL k zero       h = tt
  ↑-legL k (suc x)    h = ↑-legL k x h
  ↑-legL k (lim f)    (hf , adj) = (λ n → ↑-legL k (f n) (hf n)) , (λ n → ↑-mono k (adj n))
  ↑-legL (suc a)  (Ω _ g) h = λ c hc → ↑-legL (suc a) (g c) (h c hc)
  ↑-legL (Ωₗ k h′) (Ω _ g) h = λ c hc → ↑-legL (Ωₗ k h′) (g c) (h c hc)
  ↑-legL zero     (Ω () _) h
  ↑-legL (lim _)  (Ω () _) h
  ↑-legL k (up x c y) (hx , hy , zy) =
    ⊕-legL (↑ k x) (↑ch k c y) (↑-legL k x hx) (↑ch-legL k c y hy)

  ↑ch-legL : (k : L) (c : Ch k) (y : ChT k c) → LegCh k c y → LegL (↑ch k c y)
  ↑ch-legL (suc a)   _ y h = ↑-legL a y h
  ↑ch-legL (lim g)   n y h = ↑-legL (g n) y h
  ↑ch-legL (Ωₗ k h′) c y h = ↑-legL (h′ c) y h
```

## 塔与 Λ 的合法闭项 (无前提)

```agda
tw-leg : (n : ℕ) → LegL (tw n)
tw-leg zero    = tt
tw-leg (suc n) = λ c hc → ⊕-legL (tw n) (↑ (tw n) c) (tw-leg n) (↑-legL (tw n) c hc)

Λ-leg : LegL Λ
Λ-leg = tw-leg , λ n → ◃lw

twΩ-leg : (n : ℕ) → Leg (tw n) (Ωt (tw n))
twΩ-leg n = Ωt-leg (tw n)

ΛΩ-leg : Leg Λ (Ωt Λ)
ΛΩ-leg = Ωt-leg Λ

EBOᶜ : Tr zero
EBOᶜ = ψ₀ Λ (Ωt Λ)

EBOᶜ-leg : Leg zero EBOᶜ
EBOᶜ-leg = ψ₀-leg Λ (Ωt Λ) ΛΩ-leg
```
