# 上折: 合法性

> 判决: 成品候选 (合法性). 编译定理: 上折对第一位置序单调 (`Up-mono`, 无前提), 保持 "合法且非零" (`Up-LN`, 底合法且非零); 由此 `YiUpFold` 的折叠单调 (`mono⊥`, `monos`, 无前提), 保持合法 (`pres⊥`, `press`);
> 塔各项与 Λ 的 Ω 树折到第 0 层的闭项合法 (`twᶜ-leg`, `EBOᶜ-leg`, 无前提). 保留判定的归纳原理取自 `YiPhiLegal`, 序与运算的引理取自 `YiFreshLegal`.
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpLegal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ)
open import OCF.Lean.YiFreshLegal using
  ( _⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t; Leg; LegBr; LegBr⁼; LegCh; legFrom; legFrom⁼
  ; +-mono; +-leg; ι-mono; ι-leg; Ωt-nz; Ωt-leg; Good; Good⁼
  ; LN; iterInv; nextLN; cumLN )
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold using (kp; kp⁼)
open import OCF.Lean.YiPhiLegal using (kp-ind; kp⁼-ind)
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiUpFold
```

## 上折的引理

槽位搬运把第一分支送到第一分支, 并保持分支合法.

```agda
chFirst : (j : L) (c : Ch j) (p : Pos (chL j c))
  → chBr j c p (fromBr j (chP j c p) zero) ≡ fromBr (chL j c) p zero
chFirst (suc a)  _ p = refl
chFirst (lim g)  n p = refl
chFirst (Ωₗ k h) c p = refl

mvFirst : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) → mvBr d p (fromBr ℓ (mv d p) zero) ≡ fromBr j p zero
mvFirst stop           p = refl
mvFirst (down {j} d c) p = trans (cong (chBr j c p) (mvFirst d (chP j c p))) (chFirst j c p)

chLeg : (j : L) (c : Ch j) (p : Pos (chL j c)) (z : Br j (chP j c p))
  → LegBr j (chP j c p) z → LegBr (chL j c) p (chBr j c p z)
chLeg (suc a)  _ p z h = h
chLeg (lim g)  n p z h = h
chLeg (Ωₗ k h) c p z e = e

mvLeg : ∀ {ℓ j} (d : Dn ℓ j) (p : Pos j) (z : Br ℓ (mv d p)) → LegBr ℓ (mv d p) z → LegBr j p (mvBr d p z)
mvLeg stop           p z h = h
mvLeg (down {j} d c) p z h = chLeg j c p _ (mvLeg d (chP j c p) z h)

legCh : (ℓ : L) (c : Ch ℓ) (y : ChT ℓ c) → LegCh ℓ c y → Leg (chL ℓ c) (chT ℓ c y)
legCh (suc a)  _ y h = h
legCh (lim g)  n y h = h
legCh (Ωₗ k h) c y e = e
```

上折单调 (任意底), 保持 "合法且非零" (底合法且非零).

```agda
Up-mono : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) {x y : Tr j} → j ⊢ x ◃ y → ℓ ⊢ Up j d b x ◃ Up j d b y
Up-mono j d b ◃s     = ◃l zero
Up-mono j d b (◃l n) = ◃l n
Up-mono {ℓ} j d b (◃w {p = p} {g = g}) =
  subst (λ t → ℓ ⊢ Up j d b (g t) ◃ Ω (mv d p) (λ z → Up j d b (g (mvBr d p z)))) (mvFirst d p) ◃w
Up-mono (suc a)  d b (◃u {x = x} zy)         = Up-mono a (down d tt) (Up (suc a) d b x) zy
Up-mono (lim g)  d b (◃u {x = x} {c = n} zy) = Up-mono (g n) (down d n) (Up (lim g) d b x) zy
Up-mono (Ωₗ k h) d b (◃u {x = x} {c = c} zy) = Up-mono (h c) (down d c) (Up (Ωₗ k h) d b x) zy
Up-mono (suc a)  d b (◃c {x = x} e)          = Up-mono a (down d tt) (Up (suc a) d b x) e
Up-mono (lim g)  d b (◃c {x = x} {c = n} e)  = Up-mono (g n) (down d n) (Up (lim g) d b x) e
Up-mono (Ωₗ k h) d b (◃c {x = x} {c = c} e)  = Up-mono (h c) (down d c) (Up (Ωₗ k h) d b x) e
Up-mono j d b (◃t e f) = ◃t (Up-mono j d b e) (Up-mono j d b f)

Up-LN : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b : Tr ℓ) → LN ℓ b → (y : Tr j) → Leg j y → LN ℓ (Up j d b y)
Up-LN j d b hb zero    h = hb
Up-LN j d b hb (suc y) h = nextLN _ (Up-LN j d b hb y h)
Up-LN j d b hb (lim f) (hf , adj) =
  ((λ n → proj₁ (Up-LN j d b hb (f n) (hf n))) , (λ n → Up-mono j d b (adj n)))
  , ◃t (proj₂ (Up-LN j d b hb (f zero) (hf zero))) (◃l zero)
Up-LN {ℓ} j d b hb (Ω p g) h =
  (λ z hz → proj₁ (Up-LN j d b hb (g (mvBr d p z)) (h _ (mvLeg d p z hz))))
  , ◃t (proj₂ (Up-LN j d b hb (g (mvBr d p (fromBr ℓ (mv d p) zero)))
                (h _ (mvLeg d p _ (legFrom ℓ (mv d p) zero tt))))) ◃w
Up-LN (suc a)  d b hb (up y _ y′) (hy , hy′ , zy) =
  Up-LN a (down d tt) _ (Up-LN (suc a) d b hb y hy) y′ hy′
Up-LN (lim g)  d b hb (up y n y′) (hy , hy′ , zy) =
  Up-LN (g n) (down d n) _ (Up-LN (lim g) d b hb y hy) y′ hy′
Up-LN (Ωₗ k h) d b hb (up y c y′) (hy , hy′ , zy) =
  Up-LN (h c) (down d c) _ (Up-LN (Ωₗ k h) d b hb y hy) y′ hy′
Up-LN zero     d b hb (up y () _)
```

## 折叠单调 (无前提)

孩子的底与 `YiUpFold` 里逐字相同. 与 `YiPhiLegal` 不同的只有自身行的三处 (`◃u`, `◃c`, `up`), 都交给上折的引理.

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
  monos ℓ        ε B _ self      β (◃u {x = x} {c = c} zy) =
    Up-mono (chL ℓ c) (down stop c) (ψs ℓ ε B ℓ self β x) zy
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
  monos ℓ        ε B _ self      β (◃c {x = x} {c = c} d) =
    Up-mono (chL ℓ c) (down stop c) (ψs ℓ ε B ℓ self β x) d
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
    Up-LN (chL ℓ c) (down stop c) (ψs ℓ ε B ℓ self β x) (press ℓ ε B hB ℓ self β hβ x hx)
      (chT ℓ c y) (legCh ℓ c y hy)
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
