# φ 并进折叠: 合法性

> 判决: 成品候选 (合法性). 编译定理: 新折叠对第一位置序单调 (`mono⊥`, `monos`, 无前提), 保持 "合法且非零" (`pres⊥`, `press`; 底合法且非零);
> 塔各项与 Λ 的 Ω 树折到第 0 层的闭项合法 (`twᶜ-leg`, `EBOᶜ-leg`, 无前提). 序, 合法性, 运算的引理取自 `YiFreshLegal` (块没有改).
> 不否定什么. 层号自身的合法性 (`tw-leg`, `Λ-leg`) 仍是 `YiFreshLegal` 的, 这里不重证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiLegal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ)
open import OCF.Lean.YiFreshLegal using
  ( _⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t; Leg; LegBr; LegBr⁼; legFrom; legFrom⁼
  ; +-mono; +-leg; ι-mono; ι-leg; Ωt-nz; Ωt-leg; Good; Good⁼
  ; LN; iterInv; nextLN; cumLN )
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold
```

## 槽位搬运与保留判定的归纳原理

`pshBr` 把第一分支送到第一分支, 并保持分支合法; 所以保留时交出的换型仍满足 `Good`.

```agda
pshFirst : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k)
  → pshBr v t (fromBr⁼ a (psh v t) zero) ≡ fromBr⁼ k t zero
pshFirst self      t = refl
pshFirst (ins v)   t = pshFirst v t
pshFirst (inl n v) t = pshFirst v t
pshFirst (inlu vs) t = pshFirst (vs zero) t
pshFirst (ink v)   t = pshFirst v t
pshFirst (inb c v) t = pshFirst v t
pshFirst (inu vs)  t = pshFirst (vs zero) t

pshLeg : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) (z : Br⁼ a (psh v t))
  → LegBr⁼ a (psh v t) z → LegBr⁼ k t (pshBr v t z)
pshLeg self      t z h = h
pshLeg (ins v)   t z h = pshLeg v t z h
pshLeg (inl n v) t z h = pshLeg v t z h
pshLeg (inlu vs) t z h = pshLeg (vs zero) t z h
pshLeg (ink v)   t z h = pshLeg v t z h
pshLeg (inb c v) t z h = pshLeg v t z h
pshLeg (inu vs)  t z h = pshLeg (vs zero) t z h

mutual
  kp-ind : (ℓ : L) (ε : Ev ℓ) (p : Pos ℓ) {j : L} (v : j ≤ ℓ) {X : Set} (R : X → Set)
    {K : (q : Pos j) → (Br j q → Br ℓ p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br ℓ p) → Good ℓ p j q cv → R (K q cv)) → R d
    → R (kp ℓ ε p v K d)
  kp-ind ℓ        ε p       self      R hk hd = hk p (λ z → z) (refl , λ z h → h)
  kp-ind (suc a)  ε p       (ins v)   R hk hd = kp⁼-ind a ε p v R hk hd
  kp-ind (lim g)  ε (m , p) (inl n v) R hk hd with eqℕ m n
  ... | just refl = kp⁼-ind (g m) (ε m) p v R hk hd
  ... | nothing   = hd
  kp-ind (lim g)  ε (m , p) (inlu vs) R hk hd = kp⁼-ind (g m) (ε m) p (vs m) R hk hd
  kp-ind (Ωₗ k h) (ek , e) (inj₁ t)       (ink v)    R hk hd = kp⁼-ind k ek t v R hk hd
  kp-ind (Ωₗ k h) (ek , e) (inj₁ t)       (inb c v)  R hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) (psh (proj₁ (e c)) t) v R
      (λ q cv gd → hk q (λ z → pshBr (proj₁ (e c)) t (cv z))
        ( trans (cong (pshBr (proj₁ (e c)) t) (proj₁ gd)) (pshFirst (proj₁ (e c)) t)
        , λ z hz → pshLeg (proj₁ (e c)) t (cv z) (proj₂ gd z hz))) hd
  kp-ind (Ωₗ k h) (ek , e) (inj₁ t)       (inu vs)   R hk hd =
    kp⁼-ind (h zero) (proj₂ (e zero)) (psh (proj₁ (e zero)) t) (vs zero) R
      (λ q cv gd → hk q (λ z → pshBr (proj₁ (e zero)) t (cv z))
        ( trans (cong (pshBr (proj₁ (e zero)) t) (proj₁ gd)) (pshFirst (proj₁ (e zero)) t)
        , λ z hz → pshLeg (proj₁ (e zero)) t (cv z) (proj₂ gd z hz))) hd
  kp-ind (Ωₗ k h) (ek , e) (inj₂ (c , t)) (ink v)    R hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) t (v ∙ proj₁ (e c)) R hk hd
  kp-ind (Ωₗ k h) (ek , e) (inj₂ (c , t)) (inu vs)   R hk hd = kp⁼-ind (h c) (proj₂ (e c)) t (vs c) R hk hd
  kp-ind (Ωₗ k h) (ek , e) (inj₂ (c , t)) (inb c′ v) R hk hd = hd

  kp⁼-ind : (a : L) (ε : Ev a) (p : Pos⁼ a) {j : L} (v : j ≤ a) {X : Set} (R : X → Set)
    {K : (q : Pos j) → (Br j q → Br⁼ a p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br⁼ a p) → Good⁼ a p j q cv → R (K q cv)) → R d
    → R (kp⁼ a ε p v K d)
  kp⁼-ind a ε (inj₁ _) v R hk hd = hd
  kp⁼-ind a ε (inj₂ p) v R hk hd = kp-ind a ε p v R hk hd
```

## 折叠单调 (无前提)

孩子的底与 `YiPhiFold` 里逐字相同.

```agda
dS : (a : L) → Ev (suc a) → Base (suc a) → Tr (suc a) → Base a
dS a ε B x = base (ψ⊥ (suc a) ε B x) (λ j w → ψs (suc a) ε B j (ins w) (bs B j (ins w)) x)

dL : (g : ℕ → L) → Ev (lim g) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
dL g ε B n x = base (ψ⊥ (lim g) ε B x) (λ j w → ψs (lim g) ε B j (inl n w) (bs B j (inl n w)) x)

dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
dW k h ε B c x = base (ψ⊥ (Ωₗ k h) ε B x) (λ j w → ψs (Ωₗ k h) ε B j (inb c w) (bs B j (inb c w)) x)

mutual
  fb : ∀ {j} (b : Tr j) (ℓ′ : L) (ε′ : Ev ℓ′) {y : Tr ℓ′} → ℓ′ ⊢ zero ◃ y
     → j ⊢ b ◃ b + ι j (ψ⊥ ℓ′ ε′ (B₀ ℓ′) y)
  fb {j} b ℓ′ ε′ zy = +-mono b (ι-mono j (◃t ◃s (mono⊥ ℓ′ ε′ (B₀ ℓ′) zy)))

  mono⊥ : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε B x ◃ ψ⊥ ℓ ε B y
  mono⊥ ℓ ε B ◃s     = ◃l zero
  mono⊥ ℓ ε B (◃l n) = ◃l n
  mono⊥ ℓ ε B ◃w     = ◃l zero
  mono⊥ (suc a)  ε B (◃u {x = x} zy)         = mono⊥ a ε (dS a ε B x) zy
  mono⊥ (lim g)  ε B (◃u {x = x} {c = n} zy) = mono⊥ (g n) (ε n) (dL g ε B n x) zy
  mono⊥ (Ωₗ k h) ε B (◃u {x = x} {c = c} zy) = mono⊥ (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) zy
  mono⊥ (suc a)  ε B (◃c {x = x} d)          = mono⊥ a ε (dS a ε B x) d
  mono⊥ (lim g)  ε B (◃c {x = x} {c = n} d)  = mono⊥ (g n) (ε n) (dL g ε B n x) d
  mono⊥ (Ωₗ k h) ε B (◃c {x = x} {c = c} d)  = mono⊥ (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) d
  mono⊥ ℓ ε B (◃t d e) = ◃t (mono⊥ ℓ ε B d) (mono⊥ ℓ ε B e)

  monos : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ}
        → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε B j v β x ◃ ψs ℓ ε B j v β y
  monos ℓ ε B j v β ◃s     = ◃l zero
  monos ℓ ε B j v β (◃l n) = ◃l n
  monos ℓ ε B j v β (◃w {p = p} {g = g}) =
    kp-ind ℓ ε p v (λ X → j ⊢ ψs ℓ ε B j v β (g (fromBr ℓ p zero)) ◃ X)
      (λ q cv gd → subst (λ t → j ⊢ ψs ℓ ε B j v β (g t) ◃ Ω q (λ z → ψs ℓ ε B j v β (g (cv z))))
                     (proj₁ gd) ◃w)
      (◃l zero)
  monos ℓ        ε B _ self      β (◃u zy) = ◃u zy
  monos (suc a)  ε B j (ins v)   β (◃u {x = x} zy) =
    monos a ε (dS a ε B x) j v (ψs (suc a) ε B j (ins v) β x) zy
  monos (lim g)  ε B j (inl n v) β (◃u {x = x} {c = m} zy) with eqℕ m n
  ... | just refl = monos (g m) (ε m) (dL g ε B m x) j v (ψs (lim g) ε B j (inl m v) β x) zy
  ... | nothing   = fb (ψs (lim g) ε B j (inl n v) β x) (g m) (ε m) zy
  monos (lim g)  ε B j (inlu vs) β (◃u {x = x} {c = m} zy) =
    monos (g m) (ε m) (dL g ε B m x) j (vs m) (ψs (lim g) ε B j (inlu vs) β x) zy
  monos (Ωₗ k h) ε B j (ink v)    β (◃u {x = x} {c = c} zy) =
    monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (v ∙ proj₁ (proj₂ ε c))
      (ψs (Ωₗ k h) ε B j (ink v) β x) zy
  monos (Ωₗ k h) ε B j (inu vs)   β (◃u {x = x} {c = c} zy) =
    monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (vs c) (ψs (Ωₗ k h) ε B j (inu vs) β x) zy
  monos (Ωₗ k h) ε B j (inb c′ v) β (◃u {x = x} {c = c} zy) =
    fb (ψs (Ωₗ k h) ε B j (inb c′ v) β x) (h c) (proj₂ (proj₂ ε c)) zy
  monos ℓ        ε B _ self      β (◃c d) = ◃c d
  monos (suc a)  ε B j (ins v)   β (◃c {x = x} d) =
    monos a ε (dS a ε B x) j v (ψs (suc a) ε B j (ins v) β x) d
  monos (lim g)  ε B j (inl n v) β (◃c {x = x} {c = m} d) with eqℕ m n
  ... | just refl = monos (g m) (ε m) (dL g ε B m x) j v (ψs (lim g) ε B j (inl m v) β x) d
  ... | nothing   = +-mono (ψs (lim g) ε B j (inl n v) β x) (ι-mono j (mono⊥ (g m) (ε m) (B₀ (g m)) d))
  monos (lim g)  ε B j (inlu vs) β (◃c {x = x} {c = m} d) =
    monos (g m) (ε m) (dL g ε B m x) j (vs m) (ψs (lim g) ε B j (inlu vs) β x) d
  monos (Ωₗ k h) ε B j (ink v)    β (◃c {x = x} {c = c} d) =
    monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (v ∙ proj₁ (proj₂ ε c))
      (ψs (Ωₗ k h) ε B j (ink v) β x) d
  monos (Ωₗ k h) ε B j (inu vs)   β (◃c {x = x} {c = c} d) =
    monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (vs c) (ψs (Ωₗ k h) ε B j (inu vs) β x) d
  monos (Ωₗ k h) ε B j (inb c′ v) β (◃c {x = x} {c = c} d) =
    +-mono (ψs (Ωₗ k h) ε B j (inb c′ v) β x)
      (ι-mono j (mono⊥ (h c) (proj₂ (proj₂ ε c)) (B₀ (h c)) d))
  monos ℓ ε B j v β (◃t d e) = ◃t (monos ℓ ε B j v β d) (monos ℓ ε B j v β e)
```

## 折叠保持合法

底的每个分量合法且非零 (`LegB`); 当前目标的底 β 也合法且非零.

```agda
LegB : (ℓ : L) → Base ℓ → Set
LegB ℓ B = LN zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → LN j (bs B j w))

LegB₀ : (ℓ : L) → LegB ℓ (B₀ ℓ)
LegB₀ ℓ = (Ωt-leg zero , Ωt-nz zero) , λ j _ → Ωt-leg j , Ωt-nz j

mutual
  fbLN : ∀ {j} (b : Tr j) → LN j b → (ℓ′ : L) (ε′ : Ev ℓ′) (y : Tr ℓ′) → Leg ℓ′ y → ℓ′ ⊢ zero ◃ y
       → LN j (b + ι j (ψ⊥ ℓ′ ε′ (B₀ ℓ′) y))
  fbLN {j} b (hb , zb) ℓ′ ε′ y hy zy =
    +-leg b _ hb (ι-leg j _ (proj₁ (pres⊥ ℓ′ ε′ (B₀ ℓ′) (LegB₀ ℓ′) y hy))) , ◃t zb (fb b ℓ′ ε′ zy)

  legS : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) → LegB (suc a) B → (x : Tr (suc a)) → Leg (suc a) x
       → LegB a (dS a ε B x)
  legS a ε B hB x hx = pres⊥ (suc a) ε B hB x hx
    , λ j w → press (suc a) ε B hB j (ins w) (bs B j (ins w)) (proj₂ hB j (ins w)) x hx

  legL : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) → LegB (lim g) B → (n : ℕ) (x : Tr (lim g))
       → Leg (lim g) x → LegB (g n) (dL g ε B n x)
  legL g ε B hB n x hx = pres⊥ (lim g) ε B hB x hx
    , λ j w → press (lim g) ε B hB j (inl n w) (bs B j (inl n w)) (proj₂ hB j (inl n w)) x hx

  legW : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) → LegB (Ωₗ k h) B → (c : Tr k)
       (x : Tr (Ωₗ k h)) → Leg (Ωₗ k h) x → LegB (h c) (dW k h ε B c x)
  legW k h ε B hB c x hx = pres⊥ (Ωₗ k h) ε B hB x hx
    , λ j w → press (Ωₗ k h) ε B hB j (inb c w) (bs B j (inb c w)) (proj₂ hB j (inb c w)) x hx

  pres⊥ : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (x : Tr ℓ) → Leg ℓ x → LN zero (ψ⊥ ℓ ε B x)
  pres⊥ ℓ ε B hB zero    h = proj₁ hB
  pres⊥ ℓ ε B hB (suc x) h = nextLN _ (pres⊥ ℓ ε B hB x h)
  pres⊥ ℓ ε B hB (lim f) (hf , adj) =
    ((λ n → proj₁ (pres⊥ ℓ ε B hB (f n) (hf n))) , (λ n → mono⊥ ℓ ε B (adj n)))
    , ◃t (proj₂ (pres⊥ ℓ ε B hB (f zero) (hf zero))) (◃l zero)
  pres⊥ ℓ ε B hB (Ω p g) h =
    cumLN _ (λ n → pres⊥ ℓ ε B hB (g _) (h _ (iterInv (LegBr ℓ p) _ _ (legFrom ℓ p zero tt)
      (λ z hz → legFrom ℓ p _ (proj₁ (press ℓ ε B hB (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p))
        (proj₂ hB (at ℓ p) (posW ℓ p)) (g z) (h z hz)))) n)))
  pres⊥ (suc a)  ε B hB (up x _ y) (hx , hy , zy) = pres⊥ a ε (dS a ε B x) (legS a ε B hB x hx) y hy
  pres⊥ (lim g)  ε B hB (up x n y) (hx , hy , zy) =
    pres⊥ (g n) (ε n) (dL g ε B n x) (legL g ε B hB n x hx) y hy
  pres⊥ (Ωₗ k h) ε B hB (up x c y) (hx , hy , zy) =
    pres⊥ (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (legW k h ε B hB c x hx) y hy

  press : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → LN j β
        → (x : Tr ℓ) → Leg ℓ x → LN j (ψs ℓ ε B j v β x)
  press ℓ ε B hB j v β hβ zero    h = hβ
  press ℓ ε B hB j v β hβ (suc x) h = nextLN _ (press ℓ ε B hB j v β hβ x h)
  press ℓ ε B hB j v β hβ (lim f) (hf , adj) =
    ((λ n → proj₁ (press ℓ ε B hB j v β hβ (f n) (hf n))) , (λ n → monos ℓ ε B j v β (adj n)))
    , ◃t (proj₂ (press ℓ ε B hB j v β hβ (f zero) (hf zero))) (◃l zero)
  press ℓ ε B hB j v β hβ (Ω p g) h =
    kp-ind ℓ ε p v (LN j)
      (λ q cv gd →
        (λ z hz → proj₁ (press ℓ ε B hB j v β hβ (g (cv z)) (h (cv z) (proj₂ gd z hz))))
        , ◃t (proj₂ (press ℓ ε B hB j v β hβ (g (cv (fromBr j q zero)))
                      (h _ (proj₂ gd _ (legFrom j q zero tt))))) ◃w)
      (cumLN _ (λ n → press ℓ ε B hB j v β hβ (g _) (h _ (iterInv (LegBr ℓ p) _ _ (legFrom ℓ p zero tt)
        (λ z hz → legFrom ℓ p _ (proj₁ (press ℓ ε B hB (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p))
          (proj₂ hB (at ℓ p) (posW ℓ p)) (g z) (h z hz)))) n))))
  press ℓ ε B hB _ self β hβ (up x c y) (hx , hy , zy) =
    (proj₁ (press ℓ ε B hB ℓ self β hβ x hx) , hy , zy)
    , ◃t (proj₂ (press ℓ ε B hB ℓ self β hβ x hx)) (◃u zy)
  press (suc a) ε B hB j (ins v) β hβ (up x _ y) (hx , hy , zy) =
    press a ε (dS a ε B x) (legS a ε B hB x hx) j v _ (press (suc a) ε B hB j (ins v) β hβ x hx) y hy
  press (lim g) ε B hB j (inl n v) β hβ (up x m y) (hx , hy , zy) with eqℕ m n
  ... | just refl =
    press (g m) (ε m) (dL g ε B m x) (legL g ε B hB m x hx) j v _
      (press (lim g) ε B hB j (inl m v) β hβ x hx) y hy
  ... | nothing = fbLN _ (press (lim g) ε B hB j (inl n v) β hβ x hx) (g m) (ε m) y hy zy
  press (lim g) ε B hB j (inlu vs) β hβ (up x m y) (hx , hy , zy) =
    press (g m) (ε m) (dL g ε B m x) (legL g ε B hB m x hx) j (vs m) _
      (press (lim g) ε B hB j (inlu vs) β hβ x hx) y hy
  press (Ωₗ k h) ε B hB j (ink v) β hβ (up x c y) (hx , hy , zy) =
    press (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (legW k h ε B hB c x hx) j (v ∙ proj₁ (proj₂ ε c)) _
      (press (Ωₗ k h) ε B hB j (ink v) β hβ x hx) y hy
  press (Ωₗ k h) ε B hB j (inu vs) β hβ (up x c y) (hx , hy , zy) =
    press (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (legW k h ε B hB c x hx) j (vs c) _
      (press (Ωₗ k h) ε B hB j (inu vs) β hβ x hx) y hy
  press (Ωₗ k h) ε B hB j (inb c′ v) β hβ (up x c y) (hx , hy , zy) =
    fbLN _ (press (Ωₗ k h) ε B hB j (inb c′ v) β hβ x hx) (h c) (proj₂ (proj₂ ε c)) y hy zy
```

## 闭项合法 (无前提)

```agda
ψ₀-leg : (ℓ : L) (ε : Ev ℓ) (x : Tr ℓ) → Leg ℓ x → Leg zero (ψ₀ ℓ ε x)
ψ₀-leg ℓ ε x h = proj₁ (pres⊥ ℓ ε (B₀ ℓ) (LegB₀ ℓ) x h)

twᶜ : ℕ → Tr zero
twᶜ n = ψ₀ (tw n) (Ev-tw n) (Ωt (tw n))

twᶜ-leg : (n : ℕ) → Leg zero (twᶜ n)
twᶜ-leg n = ψ₀-leg (tw n) (Ev-tw n) (Ωt (tw n)) (Ωt-leg (tw n))

EBOᶜ : Tr zero
EBOᶜ = ψ₀ Λ Ev-Λ (Ωt Λ)

EBOᶜ-leg : Leg zero EBOᶜ
EBOᶜ-leg = ψ₀-leg Λ Ev-Λ (Ωt Λ) (Ωt-leg Λ)
```
