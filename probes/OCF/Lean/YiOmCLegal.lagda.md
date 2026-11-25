# 留在孩子里, 底依赖左边: 合法性

> 判决: 成品候选 (合法性). 编译定理: 折到第 0 层单调, 无前提 (`mono⊥`); 折到目标 j 单调, 前提是底的每个分量非零 (`monos`, 前提 `NZB`); 底合法且非零时保持合法且非零 (`pres⊥`, `press`); 塔各项与 Λ 的闭项合法 (`twᶜ-leg`, `EBOᶜ-leg`).
> 前提 `NZB` 在规范底上成立 (`nzB₀`), 由孩子的底继承 (`nzS`, `nzL`, `nzW`), 由底合法推出 (`nzLeg`). 它出在 Ω 结点层号的自身行: `◃u` 要孩子部分非零, 孩子部分的底取自 B.
> 不否定什么. 没有证明 "无此前提则不单调"; 写法照设计探针 `OmProbe-OmCLegal` 改.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOmCLegal where

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
open import OCF.Lean.YiUpBlock using (chP; chBr; Dn; stop; down; mv; mvBr)
open import OCF.Lean.YiUpLegal using (mvFirst; mvLeg; legCh)
open import OCF.Lean.YiOmCFold
```

## 重新嵌入的引理

```agda
u-inc : (j : L) (c : Ch j) (x : Tr j) {t : Tr (chL j c)} → chL j c ⊢ zero ◃ t → j ⊢ x ◃ up x c (unT j c t)
u-inc (suc a)  _ x zt = ◃u zt
u-inc (lim g)  n x zt = ◃u zt
u-inc (Ωₗ k h) c x zt = ◃u zt

u-mono : (j : L) (c : Ch j) (x : Tr j) {s t : Tr (chL j c)} → chL j c ⊢ s ◃ t
  → j ⊢ up x c (unT j c s) ◃ up x c (unT j c t)
u-mono (suc a)  _ x e = ◃c e
u-mono (lim g)  n x e = ◃c e
u-mono (Ωₗ k h) c x e = ◃c e

u-leg : (j : L) (c : Ch j) (x : Tr j) (t : Tr (chL j c)) → Leg j x → Leg (chL j c) t → chL j c ⊢ zero ◃ t
  → Leg j (up x c (unT j c t))
u-leg (suc a)  _ x t hx ht zt = hx , ht , zt
u-leg (lim g)  n x t hx ht zt = hx , ht , zt
u-leg (Ωₗ k h) c x t hx ht zt = hx , ht , zt

embD-inc : ∀ {ℓ j} (d : Dn ℓ j) (x : Tr ℓ) {t : Tr j} → j ⊢ zero ◃ t → ℓ ⊢ x ◃ embD d x t
embD-inc stop           x zt = +-mono x zt
embD-inc (down {j} d c) x zt = embD-inc d x (u-inc j c zero zt)

embD-mono : ∀ {ℓ j} (d : Dn ℓ j) (x : Tr ℓ) {s t : Tr j} → j ⊢ s ◃ t → ℓ ⊢ embD d x s ◃ embD d x t
embD-mono stop           x e = +-mono x e
embD-mono (down {j} d c) x e = embD-mono d x (u-mono j c zero e)

embD-leg : ∀ {ℓ j} (d : Dn ℓ j) (x : Tr ℓ) (t : Tr j) → Leg ℓ x → Leg j t → j ⊢ zero ◃ t → Leg ℓ (embD d x t)
embD-leg stop           x t hx ht zt = +-leg x t hx ht
embD-leg (down {j} d c) x t hx ht zt = embD-leg d x _ hx (u-leg j c zero t tt ht zt) (u-inc j c zero zt)
```

## 孩子的底

```agda
dS : (a : L) → Ev (suc a) → Base (suc a) → Tr (suc a) → Base a
dS a ε B x = base (ψ⊥ (suc a) ε B x) (λ j w → ψs (suc a) ε B j (ins w) (bs B j (ins w)) x)

dL : (g : ℕ → L) → Ev (lim g) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
dL g ε B n x = base (ψ⊥ (lim g) ε B x) (λ j w → ψs (lim g) ε B j (inl n w) (bs B j (inl n w)) x)

dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
dW k h ε B c x = base (ψ⊥ (Ωₗ k h) ε B x) (λ j w → ψs (Ωₗ k h) ε B j (inb c w) (bs B j (inb c w)) x)
```

## 非零 (不要合法性)

底的每个分量非零 (`NZB`) 时, 折叠值非零; 对树递归, 不用单调.

```agda
NZB : (ℓ : L) → Base ℓ → Set
NZB ℓ B = (j : L) (w : j ≤ ℓ) → j ⊢ zero ◃ bs B j w

nzB₀ : (ℓ : L) → NZB ℓ (B₀ ℓ)
nzB₀ ℓ j _ = Ωt-nz j

+ι-nz : ∀ {j} (b : Tr j) → j ⊢ zero ◃ b → (t : Tr zero) → j ⊢ zero ◃ b + ι j t
+ι-nz b zb zero    = zb
+ι-nz b zb (suc t) = ◃t (+ι-nz b zb t) ◃s
+ι-nz b zb (lim f) = ◃t (+ι-nz b zb (f zero)) (◃l zero)
+ι-nz b zb (Ω () _)
+ι-nz b zb (up _ () _)

mutual
  nzU : ∀ {ℓ} (j : L) (ε : Ev j) (d : Dn ℓ j) (b : Tr ℓ) → ℓ ⊢ zero ◃ b → (y : Tr j) → ℓ ⊢ zero ◃ Up′ j ε d b y
  nzU j ε d b zb zero    = zb
  nzU j ε d b zb (suc y) = ◃t (nzU j ε d b zb y) (◃l zero)
  nzU j ε d b zb (lim f) = ◃t (nzU j ε d b zb (f zero)) (◃l zero)
  nzU {ℓ} j ε d b zb (Ω p g) = ◃t (nzU j ε d b zb (g (mvBr d p (fromBr ℓ (mv d p) zero)))) ◃w
  nzU (suc a)  ε d b zb (up y _ y′) = nzU a ε (down d tt) _ (nzU (suc a) ε d b zb y) y′
  nzU (lim g)  ε d b zb (up y n y′) = nzU (g n) (ε n) (down d n) _ (nzU (lim g) ε d b zb y) y′
  nzU (Ωₗ k h) ε d b zb (up y c y′) =
    ◃t (nzU (Ωₗ k h) ε d b zb y) (embD-inc d _ (◃u (kid-nz k h ε (B₀ (Ωₗ k h)) (nzB₀ (Ωₗ k h)) c y y′)))
  nzU zero     ε d b zb (up y () _)

  kid-nz : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) → NZB (Ωₗ k h) B → (c : Tr k)
    (x : Tr (Ωₗ k h)) (y : Tr (h c)) → h c ⊢ zero ◃ kid k h ε B c x y
  kid-nz k h ε B nb c x y =
    nzs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (nzW k h ε B nb c x) (h c) self _
      (nzs (Ωₗ k h) ε B nb (h c) (inb c self) _ (nb (h c) (inb c self)) x) y

  nzS : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) → NZB (suc a) B → (x : Tr (suc a)) → NZB a (dS a ε B x)
  nzS a ε B nb x j w = nzs (suc a) ε B nb j (ins w) _ (nb j (ins w)) x

  nzL : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) → NZB (lim g) B → (n : ℕ) (x : Tr (lim g))
    → NZB (g n) (dL g ε B n x)
  nzL g ε B nb n x j w = nzs (lim g) ε B nb j (inl n w) _ (nb j (inl n w)) x

  nzW : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) → NZB (Ωₗ k h) B → (c : Tr k)
    (x : Tr (Ωₗ k h)) → NZB (h c) (dW k h ε B c x)
  nzW k h ε B nb c x j w = nzs (Ωₗ k h) ε B nb j (inb c w) _ (nb j (inb c w)) x

  nzs : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → NZB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → j ⊢ zero ◃ β
      → (x : Tr ℓ) → j ⊢ zero ◃ ψs ℓ ε B j v β x
  nzs ℓ ε B nb j v β zβ zero    = zβ
  nzs ℓ ε B nb j v β zβ (suc x) = ◃t (nzs ℓ ε B nb j v β zβ x) (◃l zero)
  nzs ℓ ε B nb j v β zβ (lim f) = ◃t (nzs ℓ ε B nb j v β zβ (f zero)) (◃l zero)
  nzs ℓ ε B nb j v β zβ (Ω p g) =
    kp-ind ℓ ε p v (λ X → j ⊢ zero ◃ X)
      (λ q cv gd → ◃t (nzs ℓ ε B nb j v β zβ (g (cv (fromBr j q zero)))) ◃w)
      (◃t (nzs ℓ ε B nb j v β zβ (g (fromBr ℓ p zero))) (◃l zero))
  nzs (suc a)  ε B nb _ self β zβ (up x _ y) =
    nzU a ε (down stop tt) _ (nzs (suc a) ε B nb (suc a) self β zβ x) y
  nzs (lim g)  ε B nb _ self β zβ (up x n y) =
    nzU (g n) (ε n) (down stop n) _ (nzs (lim g) ε B nb (lim g) self β zβ x) y
  nzs (Ωₗ k h) ε B nb _ self β zβ (up x c y) =
    ◃t (nzs (Ωₗ k h) ε B nb (Ωₗ k h) self β zβ x) (◃u (kid-nz k h ε B nb c x y))
  nzs zero     ε B nb _ self β zβ (up x () y)
  nzs (suc a) ε B nb j (ins v) β zβ (up x _ y) =
    nzs a ε (dS a ε B x) (nzS a ε B nb x) j v _ (nzs (suc a) ε B nb j (ins v) β zβ x) y
  nzs (lim g) ε B nb j (inl n v) β zβ (up x m y) with eqℕ m n
  ... | just refl = nzs (g m) (ε m) (dL g ε B m x) (nzL g ε B nb m x) j v _ (nzs (lim g) ε B nb j (inl m v) β zβ x) y
  ... | nothing   = +ι-nz _ (nzs (lim g) ε B nb j (inl n v) β zβ x) _
  nzs (lim g) ε B nb j (inlu vs) β zβ (up x m y) =
    nzs (g m) (ε m) (dL g ε B m x) (nzL g ε B nb m x) j (vs m) _ (nzs (lim g) ε B nb j (inlu vs) β zβ x) y
  nzs (Ωₗ k h) ε B nb j (ink v) β zβ (up x c y) =
    nzs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (nzW k h ε B nb c x) j (v ∙ proj₁ (proj₂ ε c)) _
      (nzs (Ωₗ k h) ε B nb j (ink v) β zβ x) y
  nzs (Ωₗ k h) ε B nb j (inu vs) β zβ (up x c y) =
    nzs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (nzW k h ε B nb c x) j (vs c) _
      (nzs (Ωₗ k h) ε B nb j (inu vs) β zβ x) y
  nzs (Ωₗ k h) ε B nb j (inb c′ v) β zβ (up x c y) =
    +ι-nz _ (nzs (Ωₗ k h) ε B nb j (inb c′ v) β zβ x) _
```

## 单调

```agda
mutual
  Up′-mono : ∀ {ℓ} (j : L) (ε : Ev j) (d : Dn ℓ j) (b : Tr ℓ) {x y : Tr j} → j ⊢ x ◃ y
    → ℓ ⊢ Up′ j ε d b x ◃ Up′ j ε d b y
  Up′-mono j ε d b ◃s     = ◃l zero
  Up′-mono j ε d b (◃l n) = ◃l n
  Up′-mono {ℓ} j ε d b (◃w {p = p} {g = g}) =
    subst (λ t → ℓ ⊢ Up′ j ε d b (g t) ◃ Ω (mv d p) (λ z → Up′ j ε d b (g (mvBr d p z)))) (mvFirst d p) ◃w
  Up′-mono (suc a)  ε d b (◃u {x = x} zy)         = Up′-mono a ε (down d tt) (Up′ (suc a) ε d b x) zy
  Up′-mono (lim g)  ε d b (◃u {x = x} {c = n} zy) = Up′-mono (g n) (ε n) (down d n) (Up′ (lim g) ε d b x) zy
  Up′-mono (Ωₗ k h) ε d b (◃u {x = x} {c = c} zy) =
    embD-inc d (Up′ (Ωₗ k h) ε d b x) (◃u (kid-nz k h ε (B₀ (Ωₗ k h)) (nzB₀ (Ωₗ k h)) c x _))
  Up′-mono (suc a)  ε d b (◃c {x = x} e)          = Up′-mono a ε (down d tt) (Up′ (suc a) ε d b x) e
  Up′-mono (lim g)  ε d b (◃c {x = x} {c = n} e)  = Up′-mono (g n) (ε n) (down d n) (Up′ (lim g) ε d b x) e
  Up′-mono (Ωₗ k h) ε d b (◃c {x = x} {c = c} e)  =
    embD-mono d (Up′ (Ωₗ k h) ε d b x)
      (◃c (monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε (B₀ (Ωₗ k h)) c x) (nzW k h ε (B₀ (Ωₗ k h)) (nzB₀ (Ωₗ k h)) c x)
            (h c) self (ψs (Ωₗ k h) ε (B₀ (Ωₗ k h)) (h c) (inb c self) (Ωt (h c)) x) e))
  Up′-mono j ε d b (◃t e f) = ◃t (Up′-mono j ε d b e) (Up′-mono j ε d b f)

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

  monos : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → NZB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ}
        → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε B j v β x ◃ ψs ℓ ε B j v β y
  monos ℓ ε B nb j v β ◃s     = ◃l zero
  monos ℓ ε B nb j v β (◃l n) = ◃l n
  monos ℓ ε B nb j v β (◃w {p = p} {g = g}) =
    kp-ind ℓ ε p v (λ X → j ⊢ ψs ℓ ε B j v β (g (fromBr ℓ p zero)) ◃ X)
      (λ q cv gd → subst (λ t → j ⊢ ψs ℓ ε B j v β (g t) ◃ Ω q (λ z → ψs ℓ ε B j v β (g (cv z))))
                     (proj₁ gd) ◃w)
      (◃l zero)
  monos (suc a)  ε B nb _ self      β (◃u {x = x} zy) =
    Up′-mono a ε (down stop tt) (ψs (suc a) ε B (suc a) self β x) zy
  monos (lim g)  ε B nb _ self      β (◃u {x = x} {c = n} zy) =
    Up′-mono (g n) (ε n) (down stop n) (ψs (lim g) ε B (lim g) self β x) zy
  monos (Ωₗ k h) ε B nb _ self      β (◃u {x = x} {c = c} zy) =
    ◃u (kid-nz k h ε B nb c x _)
  monos (suc a)  ε B nb j (ins v)   β (◃u {x = x} zy) =
    monos a ε (dS a ε B x) (nzS a ε B nb x) j v (ψs (suc a) ε B j (ins v) β x) zy
  monos (lim g)  ε B nb j (inl n v) β (◃u {x = x} {c = m} zy) with eqℕ m n
  ... | just refl = monos (g m) (ε m) (dL g ε B m x) (nzL g ε B nb m x) j v (ψs (lim g) ε B j (inl m v) β x) zy
  ... | nothing   = fb (ψs (lim g) ε B j (inl n v) β x) (g m) (ε m) zy
  monos (lim g)  ε B nb j (inlu vs) β (◃u {x = x} {c = m} zy) =
    monos (g m) (ε m) (dL g ε B m x) (nzL g ε B nb m x) j (vs m) (ψs (lim g) ε B j (inlu vs) β x) zy
  monos (Ωₗ k h) ε B nb j (ink v)    β (◃u {x = x} {c = c} zy) =
    monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (nzW k h ε B nb c x) j (v ∙ proj₁ (proj₂ ε c))
      (ψs (Ωₗ k h) ε B j (ink v) β x) zy
  monos (Ωₗ k h) ε B nb j (inu vs)   β (◃u {x = x} {c = c} zy) =
    monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (nzW k h ε B nb c x) j (vs c) (ψs (Ωₗ k h) ε B j (inu vs) β x) zy
  monos (Ωₗ k h) ε B nb j (inb c′ v) β (◃u {x = x} {c = c} zy) =
    fb (ψs (Ωₗ k h) ε B j (inb c′ v) β x) (h c) (proj₂ (proj₂ ε c)) zy
  monos (suc a)  ε B nb _ self      β (◃c {x = x} d) =
    Up′-mono a ε (down stop tt) (ψs (suc a) ε B (suc a) self β x) d
  monos (lim g)  ε B nb _ self      β (◃c {x = x} {c = n} d) =
    Up′-mono (g n) (ε n) (down stop n) (ψs (lim g) ε B (lim g) self β x) d
  monos (Ωₗ k h) ε B nb _ self      β (◃c {x = x} {c = c} d) =
    ◃c (monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (nzW k h ε B nb c x) (h c) self
          (ψs (Ωₗ k h) ε B (h c) (inb c self) (bs B (h c) (inb c self)) x) d)
  monos (suc a)  ε B nb j (ins v)   β (◃c {x = x} d) =
    monos a ε (dS a ε B x) (nzS a ε B nb x) j v (ψs (suc a) ε B j (ins v) β x) d
  monos (lim g)  ε B nb j (inl n v) β (◃c {x = x} {c = m} d) with eqℕ m n
  ... | just refl = monos (g m) (ε m) (dL g ε B m x) (nzL g ε B nb m x) j v (ψs (lim g) ε B j (inl m v) β x) d
  ... | nothing   = +-mono (ψs (lim g) ε B j (inl n v) β x) (ι-mono j (mono⊥ (g m) (ε m) (B₀ (g m)) d))
  monos (lim g)  ε B nb j (inlu vs) β (◃c {x = x} {c = m} d) =
    monos (g m) (ε m) (dL g ε B m x) (nzL g ε B nb m x) j (vs m) (ψs (lim g) ε B j (inlu vs) β x) d
  monos (Ωₗ k h) ε B nb j (ink v)    β (◃c {x = x} {c = c} d) =
    monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (nzW k h ε B nb c x) j (v ∙ proj₁ (proj₂ ε c))
      (ψs (Ωₗ k h) ε B j (ink v) β x) d
  monos (Ωₗ k h) ε B nb j (inu vs)   β (◃c {x = x} {c = c} d) =
    monos (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (nzW k h ε B nb c x) j (vs c) (ψs (Ωₗ k h) ε B j (inu vs) β x) d
  monos (Ωₗ k h) ε B nb j (inb c′ v) β (◃c {x = x} {c = c} d) =
    +-mono (ψs (Ωₗ k h) ε B j (inb c′ v) β x)
      (ι-mono j (mono⊥ (h c) (proj₂ (proj₂ ε c)) (B₀ (h c)) d))
  monos ℓ ε B nb j v β (◃t d e) = ◃t (monos ℓ ε B nb j v β d) (monos ℓ ε B nb j v β e)

LegB : (ℓ : L) → Base ℓ → Set
LegB ℓ B = LN zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → LN j (bs B j w))

LegB₀ : (ℓ : L) → LegB ℓ (B₀ ℓ)
LegB₀ ℓ = (Ωt-leg zero , Ωt-nz zero) , λ j _ → Ωt-leg j , Ωt-nz j

nzLeg : (ℓ : L) (B : Base ℓ) → LegB ℓ B → NZB ℓ B
nzLeg ℓ B hB j w = proj₂ (proj₂ hB j w)
```

## 保持合法且非零

```agda

mutual
  kid-LN : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) → LegB (Ωₗ k h) B → (c : Tr k)
    (x : Tr (Ωₗ k h)) → Leg (Ωₗ k h) x → (y : Tr (h c)) → Leg (h c) y → LN (h c) (kid k h ε B c x y)
  kid-LN k h ε B hB c x hx y hy =
    press (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (legW k h ε B hB c x hx) (h c) self _
      (press (Ωₗ k h) ε B hB (h c) (inb c self) (bs B (h c) (inb c self)) (proj₂ hB (h c) (inb c self)) x hx) y hy

  Up′-LN : ∀ {ℓ} (j : L) (ε : Ev j) (d : Dn ℓ j) (b : Tr ℓ) → LN ℓ b → (y : Tr j) → Leg j y
    → LN ℓ (Up′ j ε d b y)
  Up′-LN j ε d b hb zero    h = hb
  Up′-LN j ε d b hb (suc y) h = nextLN _ (Up′-LN j ε d b hb y h)
  Up′-LN j ε d b hb (lim f) (hf , adj) =
    ((λ n → proj₁ (Up′-LN j ε d b hb (f n) (hf n))) , (λ n → Up′-mono j ε d b (adj n)))
    , ◃t (proj₂ (Up′-LN j ε d b hb (f zero) (hf zero))) (◃l zero)
  Up′-LN {ℓ} j ε d b hb (Ω p g) h =
    (λ z hz → proj₁ (Up′-LN j ε d b hb (g (mvBr d p z)) (h _ (mvLeg d p z hz))))
    , ◃t (proj₂ (Up′-LN j ε d b hb (g (mvBr d p (fromBr ℓ (mv d p) zero)))
                  (h _ (mvLeg d p _ (legFrom ℓ (mv d p) zero tt))))) ◃w
  Up′-LN (suc a)  ε d b hb (up y _ y′) (hy , hy′ , zy) =
    Up′-LN a ε (down d tt) _ (Up′-LN (suc a) ε d b hb y hy) y′ hy′
  Up′-LN (lim g)  ε d b hb (up y n y′) (hy , hy′ , zy) =
    Up′-LN (g n) (ε n) (down d n) _ (Up′-LN (lim g) ε d b hb y hy) y′ hy′
  Up′-LN (Ωₗ k h) ε d b hb (up y c y′) (hy , hy′ , zy) =
    let X  = Up′-LN (Ωₗ k h) ε d b hb y hy
        F  = kid-LN k h ε (B₀ (Ωₗ k h)) (LegB₀ (Ωₗ k h)) c y hy y′ hy′
    in embD-leg d _ _ (proj₁ X) (tt , proj₁ F , proj₂ F) (◃u (proj₂ F))
     , ◃t (proj₂ X) (embD-inc d _ (◃u (proj₂ F)))
  Up′-LN zero     ε d b hb (up y () _)

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
    ((λ n → proj₁ (press ℓ ε B hB j v β hβ (f n) (hf n))) , (λ n → monos ℓ ε B (nzLeg ℓ B hB) j v β (adj n)))
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
  press (suc a) ε B hB _ self β hβ (up x _ y) (hx , hy , zy) =
    Up′-LN a ε (down stop tt) _ (press (suc a) ε B hB (suc a) self β hβ x hx) y hy
  press (lim g) ε B hB _ self β hβ (up x n y) (hx , hy , zy) =
    Up′-LN (g n) (ε n) (down stop n) _ (press (lim g) ε B hB (lim g) self β hβ x hx) y hy
  press (Ωₗ k h) ε B hB _ self β hβ (up x c y) (hx , hy , zy) =
    let X = press (Ωₗ k h) ε B hB (Ωₗ k h) self β hβ x hx
        F = kid-LN k h ε B hB c x hx y hy
    in (proj₁ X , proj₁ F , proj₂ F) , ◃t (proj₂ X) (◃u (proj₂ F))
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

## 闭项合法

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
