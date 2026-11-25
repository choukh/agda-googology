# ℕ 极限层号的路线: 合法性

> 判决: 成品候选 (合法性). 编译定理, 无前提: 新折叠对第一位置序单调 (`mono⊥`, `monos`), 保持 "合法且非零" (`pres⊥`, `press`; 底合法且非零); 塔各项与 Λ 的 Ω 树的 ψ₀ 值合法.
> 第一位置序的每条规则都给出读回层号之间不经下标层侧的路径 (`◃→⊑`), 所以合法树 t 读出的偏移带路线 `RtP↑ k t`; 其中 Ω 结点的分支是任意树, 那里仍没有路径.
> 不否定什么. 与 `YiUpLegal` 不同的只有 ℕ 极限层号指定孩子的各行 (按 `Way` 分三种情形) 与搬运 `emb` 的三条引理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLimLegal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι)
open import OCF.Lean.YiFreshLegal using
  ( _⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t; Leg; LegBr; LegBr⁼; LegCh; legFrom; legFrom⁼
  ; +-mono; +-leg; ι-mono; ι-leg; Ωt-nz; Ωt-leg; Good; Good⁼
  ; LN; iterInv; nextLN; cumLN )
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiLegal using (pshFirst; pshLeg)
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiUpLegal using (Up-mono; Up-LN; legCh)
open import OCF.Lean.YiLimBlock
open import OCF.Lean.YiLimFold
```

## 搬运的引理

```agda
emb-mono : (ℓ : L) (ε : Ev ℓ) {k : L} (v : k ≤ ℓ) {y′ y : Tr k} → k ⊢ y′ ◃ y → ℓ ⊢ emb ℓ ε v y′ ◃ emb ℓ ε v y
emb-mono ℓ        ε        self      d = d
emb-mono (suc a)  ε        (ins v)   d = ◃c (emb-mono a ε v d)
emb-mono (lim g)  ε        (inl n v) d = ◃c (emb-mono (g n) (ε n) v d)
emb-mono (lim g)  ε        (inlu vs) d = ◃c (emb-mono (g zero) (ε zero) (vs zero) d)
emb-mono (Ωₗ k h) (ek , e) (ink v)   d = ◃c (emb-mono (h zero) (proj₂ (e zero)) (v ∙ proj₁ (e zero)) d)
emb-mono (Ωₗ k h) (ek , e) (inb c v) d = ◃c (emb-mono (h c) (proj₂ (e c)) v d)
emb-mono (Ωₗ k h) (ek , e) (inu vs)  d = ◃c (emb-mono (h zero) (proj₂ (e zero)) (vs zero) d)

emb-nz : (ℓ : L) (ε : Ev ℓ) {k : L} (v : k ≤ ℓ) {y : Tr k} → k ⊢ zero ◃ y → ℓ ⊢ zero ◃ emb ℓ ε v y
emb-nz ℓ        ε        self      d = d
emb-nz (suc a)  ε        (ins v)   d = ◃u (emb-nz a ε v d)
emb-nz (lim g)  ε        (inl n v) d = ◃u (emb-nz (g n) (ε n) v d)
emb-nz (lim g)  ε        (inlu vs) d = ◃u (emb-nz (g zero) (ε zero) (vs zero) d)
emb-nz (Ωₗ k h) (ek , e) (ink v)   d = ◃u (emb-nz (h zero) (proj₂ (e zero)) (v ∙ proj₁ (e zero)) d)
emb-nz (Ωₗ k h) (ek , e) (inb c v) d = ◃u (emb-nz (h c) (proj₂ (e c)) v d)
emb-nz (Ωₗ k h) (ek , e) (inu vs)  d = ◃u (emb-nz (h zero) (proj₂ (e zero)) (vs zero) d)

emb-leg : (ℓ : L) (ε : Ev ℓ) {k : L} (v : k ≤ ℓ) (y : Tr k) → Leg k y → k ⊢ zero ◃ y → Leg ℓ (emb ℓ ε v y)
emb-leg ℓ        ε        self      y h d = h
emb-leg (suc a)  ε        (ins v)   y h d = tt , emb-leg a ε v y h d , emb-nz a ε v d
emb-leg (lim g)  ε        (inl n v) y h d = tt , emb-leg (g n) (ε n) v y h d , emb-nz (g n) (ε n) v d
emb-leg (lim g)  ε        (inlu vs) y h d =
  tt , emb-leg (g zero) (ε zero) (vs zero) y h d , emb-nz (g zero) (ε zero) (vs zero) d
emb-leg (Ωₗ k h) (ek , e) (ink v)   y hy d =
  tt , emb-leg (h zero) (proj₂ (e zero)) (v ∙ proj₁ (e zero)) y hy d
     , emb-nz (h zero) (proj₂ (e zero)) (v ∙ proj₁ (e zero)) d
emb-leg (Ωₗ k h) (ek , e) (inb c v) y hy d =
  tt , emb-leg (h c) (proj₂ (e c)) v y hy d , emb-nz (h c) (proj₂ (e c)) v d
emb-leg (Ωₗ k h) (ek , e) (inu vs)  y hy d =
  tt , emb-leg (h zero) (proj₂ (e zero)) (vs zero) y hy d , emb-nz (h zero) (proj₂ (e zero)) (vs zero) d
```

## 保留判定的归纳原理

```agda
mutual
  kp-ind : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (p : Pos ℓ) {j : L} (v : j ≤ ℓ) {X : Set} (Q : X → Set)
    {K : (q : Pos j) → (Br j q → Br ℓ p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br ℓ p) → Good ℓ p j q cv → Q (K q cv)) → Q d
    → Q (kp ℓ ε ρ p v K d)
  kp-ind ℓ        ε ρ p       self      Q hk hd = hk p (λ z → z) (refl , λ z h → h)
  kp-ind (suc a)  ε ρ p       (ins v)   Q hk hd = kp⁼-ind a ε ρ p v Q hk hd
  kp-ind (lim g)  ε (ρc , R) (m , p) (inl n v) Q hk hd with way g R m n
  ... | fwd r = kp⁼-ind (g n) (ε n) (ρc n) (psh r p) v Q
      (λ q cv gd → hk q (λ z → pshBr r p (cv z))
        ( trans (cong (pshBr r p) (proj₁ gd)) (pshFirst r p)
        , λ z hz → pshLeg r p (cv z) (proj₂ gd z hz))) hd
  ... | bwd r = kp⁼-ind (g m) (ε m) (ρc m) p (v ∙ r) Q hk hd
  ... | none  = hd
  kp-ind (lim g)  ε (ρc , R) (m , p) (inlu vs) Q hk hd = kp⁼-ind (g m) (ε m) (ρc m) p (vs m) Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (ink v)    Q hk hd = kp⁼-ind k ek ρk t v Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inb c v)  Q hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) (ρc c) (psh (proj₁ (e c)) t) v Q
      (λ q cv gd → hk q (λ z → pshBr (proj₁ (e c)) t (cv z))
        ( trans (cong (pshBr (proj₁ (e c)) t) (proj₁ gd)) (pshFirst (proj₁ (e c)) t)
        , λ z hz → pshLeg (proj₁ (e c)) t (cv z) (proj₂ gd z hz))) hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inu vs)   Q hk hd =
    kp⁼-ind (h zero) (proj₂ (e zero)) (ρc zero) (psh (proj₁ (e zero)) t) (vs zero) Q
      (λ q cv gd → hk q (λ z → pshBr (proj₁ (e zero)) t (cv z))
        ( trans (cong (pshBr (proj₁ (e zero)) t) (proj₁ gd)) (pshFirst (proj₁ (e zero)) t)
        , λ z hz → pshLeg (proj₁ (e zero)) t (cv z) (proj₂ gd z hz))) hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (ink v)    Q hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) (ρc c) t (v ∙ proj₁ (e c)) Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (inu vs)   Q hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) (ρc c) t (vs c) Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (inb c′ v) Q hk hd = hd

  kp⁼-ind : (a : L) (ε : Ev a) (ρ : Rt a) (p : Pos⁼ a) {j : L} (v : j ≤ a) {X : Set} (Q : X → Set)
    {K : (q : Pos j) → (Br j q → Br⁼ a p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br⁼ a p) → Good⁼ a p j q cv → Q (K q cv)) → Q d
    → Q (kp⁼ a ε ρ p v K d)
  kp⁼-ind a ε ρ (inj₁ _) v Q hk hd = hd
  kp⁼-ind a ε ρ (inj₂ p) v Q hk hd = kp-ind a ε ρ p v Q hk hd
```

## 折叠单调 (无前提)

```agda
dS : (a : L) → Ev (suc a) → Rt (suc a) → Base (suc a) → Tr (suc a) → Base a
dS a ε ρ B x = base (ψ⊥ (suc a) ε ρ B x) (λ j w → ψs (suc a) ε ρ B j (ins w) (bs B j (ins w)) x)

dL : (g : ℕ → L) → Ev (lim g) → Rt (lim g) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
dL g ε ρ B n x = base (ψ⊥ (lim g) ε ρ B x) (λ j w → ψs (lim g) ε ρ B j (inl n w) (bs B j (inl n w)) x)

dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Rt (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
dW k h ε ρ B c x = base (ψ⊥ (Ωₗ k h) ε ρ B x) (λ j w → ψs (Ωₗ k h) ε ρ B j (inb c w) (bs B j (inb c w)) x)

mutual
  fb : ∀ {j} (b : Tr j) (ℓ′ : L) (ε′ : Ev ℓ′) (ρ′ : Rt ℓ′) {y : Tr ℓ′} → ℓ′ ⊢ zero ◃ y
     → j ⊢ b ◃ b + ι j (ψ⊥ ℓ′ ε′ ρ′ (B₀ ℓ′) y)
  fb {j} b ℓ′ ε′ ρ′ zy = +-mono b (ι-mono j (◃t ◃s (mono⊥ ℓ′ ε′ ρ′ (B₀ ℓ′) zy)))

  mono⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) {x y : Tr ℓ}
        → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε ρ B x ◃ ψ⊥ ℓ ε ρ B y
  mono⊥ ℓ ε ρ B ◃s     = ◃l zero
  mono⊥ ℓ ε ρ B (◃l n) = ◃l n
  mono⊥ ℓ ε ρ B ◃w     = ◃l zero
  mono⊥ (suc a)  ε ρ B (◃u {x = x} zy)         = mono⊥ a ε ρ (dS a ε ρ B x) zy
  mono⊥ (lim g)  ε ρ B (◃u {x = x} {c = n} zy) = mono⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) zy
  mono⊥ (Ωₗ k h) ε ρ B (◃u {x = x} {c = c} zy) =
    mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) zy
  mono⊥ (suc a)  ε ρ B (◃c {x = x} d)          = mono⊥ a ε ρ (dS a ε ρ B x) d
  mono⊥ (lim g)  ε ρ B (◃c {x = x} {c = n} d)  = mono⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) d
  mono⊥ (Ωₗ k h) ε ρ B (◃c {x = x} {c = c} d)  =
    mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) d
  mono⊥ ℓ ε ρ B (◃t d e) = ◃t (mono⊥ ℓ ε ρ B d) (mono⊥ ℓ ε ρ B e)

  monos : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ}
        → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε ρ B j v β x ◃ ψs ℓ ε ρ B j v β y
  monos ℓ ε ρ B j v β ◃s     = ◃l zero
  monos ℓ ε ρ B j v β (◃l n) = ◃l n
  monos ℓ ε ρ B j v β (◃w {p = p} {g = g}) =
    kp-ind ℓ ε ρ p v (λ X → j ⊢ ψs ℓ ε ρ B j v β (g (fromBr ℓ p zero)) ◃ X)
      (λ q cv gd → subst (λ t → j ⊢ ψs ℓ ε ρ B j v β (g t) ◃ Ω q (λ z → ψs ℓ ε ρ B j v β (g (cv z))))
                     (proj₁ gd) ◃w)
      (◃l zero)
  monos ℓ        ε ρ B _ self      β (◃u {x = x} {c = c} zy) =
    Up-mono (chL ℓ c) (down stop c) (ψs ℓ ε ρ B ℓ self β x) zy
  monos (suc a)  ε ρ B j (ins v)   β (◃u {x = x} zy) =
    monos a ε ρ (dS a ε ρ B x) j v (ψs (suc a) ε ρ B j (ins v) β x) zy
  monos (lim g)  ε (ρc , R) B j (inl n v) β (◃u {x = x} {c = m} zy) with way g R m n
  ... | fwd r = monos (g n) (ε n) (ρc n) (dL g ε (ρc , R) B n x) j v
                  (ψs (lim g) ε (ρc , R) B j (inl n v) β x) (emb-nz (g n) (ε n) r zy)
  ... | bwd r = monos (g m) (ε m) (ρc m) (dL g ε (ρc , R) B m x) j (v ∙ r)
                  (ψs (lim g) ε (ρc , R) B j (inl n v) β x) zy
  ... | none  = fb (ψs (lim g) ε (ρc , R) B j (inl n v) β x) (g m) (ε m) (ρc m) zy
  monos (lim g)  ε ρ B j (inlu vs) β (◃u {x = x} {c = m} zy) =
    monos (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (vs m) (ψs (lim g) ε ρ B j (inlu vs) β x) zy
  monos (Ωₗ k h) ε ρ B j (ink v)    β (◃u {x = x} {c = c} zy) =
    monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (v ∙ proj₁ (proj₂ ε c))
      (ψs (Ωₗ k h) ε ρ B j (ink v) β x) zy
  monos (Ωₗ k h) ε ρ B j (inu vs)   β (◃u {x = x} {c = c} zy) =
    monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (vs c)
      (ψs (Ωₗ k h) ε ρ B j (inu vs) β x) zy
  monos (Ωₗ k h) ε ρ B j (inb c′ v) β (◃u {x = x} {c = c} zy) =
    fb (ψs (Ωₗ k h) ε ρ B j (inb c′ v) β x) (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) zy
  monos ℓ        ε ρ B _ self      β (◃c {x = x} {c = c} d) =
    Up-mono (chL ℓ c) (down stop c) (ψs ℓ ε ρ B ℓ self β x) d
  monos (suc a)  ε ρ B j (ins v)   β (◃c {x = x} d) =
    monos a ε ρ (dS a ε ρ B x) j v (ψs (suc a) ε ρ B j (ins v) β x) d
  monos (lim g)  ε (ρc , R) B j (inl n v) β (◃c {x = x} {c = m} d) with way g R m n
  ... | fwd r = monos (g n) (ε n) (ρc n) (dL g ε (ρc , R) B n x) j v
                  (ψs (lim g) ε (ρc , R) B j (inl n v) β x) (emb-mono (g n) (ε n) r d)
  ... | bwd r = monos (g m) (ε m) (ρc m) (dL g ε (ρc , R) B m x) j (v ∙ r)
                  (ψs (lim g) ε (ρc , R) B j (inl n v) β x) d
  ... | none  = +-mono (ψs (lim g) ε (ρc , R) B j (inl n v) β x)
                  (ι-mono j (mono⊥ (g m) (ε m) (ρc m) (B₀ (g m)) d))
  monos (lim g)  ε ρ B j (inlu vs) β (◃c {x = x} {c = m} d) =
    monos (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (vs m) (ψs (lim g) ε ρ B j (inlu vs) β x) d
  monos (Ωₗ k h) ε ρ B j (ink v)    β (◃c {x = x} {c = c} d) =
    monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (v ∙ proj₁ (proj₂ ε c))
      (ψs (Ωₗ k h) ε ρ B j (ink v) β x) d
  monos (Ωₗ k h) ε ρ B j (inu vs)   β (◃c {x = x} {c = c} d) =
    monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (vs c)
      (ψs (Ωₗ k h) ε ρ B j (inu vs) β x) d
  monos (Ωₗ k h) ε ρ B j (inb c′ v) β (◃c {x = x} {c = c} d) =
    +-mono (ψs (Ωₗ k h) ε ρ B j (inb c′ v) β x)
      (ι-mono j (mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) d))
  monos ℓ ε ρ B j v β (◃t d e) = ◃t (monos ℓ ε ρ B j v β d) (monos ℓ ε ρ B j v β e)
```

## 折叠保持合法

```agda
LegB : (ℓ : L) → Base ℓ → Set
LegB ℓ B = LN zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → LN j (bs B j w))

LegB₀ : (ℓ : L) → LegB ℓ (B₀ ℓ)
LegB₀ ℓ = (Ωt-leg zero , Ωt-nz zero) , λ j _ → Ωt-leg j , Ωt-nz j

mutual
  fbLN : ∀ {j} (b : Tr j) → LN j b → (ℓ′ : L) (ε′ : Ev ℓ′) (ρ′ : Rt ℓ′) (y : Tr ℓ′) → Leg ℓ′ y
       → ℓ′ ⊢ zero ◃ y → LN j (b + ι j (ψ⊥ ℓ′ ε′ ρ′ (B₀ ℓ′) y))
  fbLN {j} b (hb , zb) ℓ′ ε′ ρ′ y hy zy =
    +-leg b _ hb (ι-leg j _ (proj₁ (pres⊥ ℓ′ ε′ ρ′ (B₀ ℓ′) (LegB₀ ℓ′) y hy))) , ◃t zb (fb b ℓ′ ε′ ρ′ zy)

  pres⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → LegB ℓ B → (x : Tr ℓ) → Leg ℓ x
        → LN zero (ψ⊥ ℓ ε ρ B x)
  pres⊥ ℓ ε ρ B hB zero    h = proj₁ hB
  pres⊥ ℓ ε ρ B hB (suc x) h = nextLN _ (pres⊥ ℓ ε ρ B hB x h)
  pres⊥ ℓ ε ρ B hB (lim f) (hf , adj) =
    ((λ n → proj₁ (pres⊥ ℓ ε ρ B hB (f n) (hf n))) , (λ n → mono⊥ ℓ ε ρ B (adj n)))
    , ◃t (proj₂ (pres⊥ ℓ ε ρ B hB (f zero) (hf zero))) (◃l zero)
  pres⊥ ℓ ε ρ B hB (Ω p g) h =
    cumLN _ (λ n → pres⊥ ℓ ε ρ B hB (g _) (h _ (iterInv (LegBr ℓ p) _ _ (legFrom ℓ p zero tt)
      (λ z hz → legFrom ℓ p _ (proj₁ (press ℓ ε ρ B hB (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p))
        (proj₂ hB (at ℓ p) (posW ℓ p)) (g z) (h z hz)))) n)))
  pres⊥ (suc a)  ε ρ B hB (up x _ y) (hx , hy , zy) =
    pres⊥ a ε ρ (dS a ε ρ B x) (pres⊥ (suc a) ε ρ B hB x hx , λ j′ w′ → press (suc a) ε ρ B hB j′ (ins w′) (bs B j′ (ins w′)) (proj₂ hB j′ (ins w′)) x hx) y hy
  pres⊥ (lim g)  ε ρ B hB (up x n y) (hx , hy , zy) =
    pres⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) (pres⊥ (lim g) ε ρ B hB x hx , λ j′ w′ → press (lim g) ε ρ B hB j′ (inl n w′) (bs B j′ (inl n w′)) (proj₂ hB j′ (inl n w′)) x hx) y hy
  pres⊥ (Ωₗ k h) ε ρ B hB (up x c y) (hx , hy , zy) =
    pres⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) (pres⊥ (Ωₗ k h) ε ρ B hB x hx , λ j′ w′ → press (Ωₗ k h) ε ρ B hB j′ (inb c w′) (bs B j′ (inb c w′)) (proj₂ hB j′ (inb c w′)) x hx) y hy

  press : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → LN j β
        → (x : Tr ℓ) → Leg ℓ x → LN j (ψs ℓ ε ρ B j v β x)
  press ℓ ε ρ B hB j v β hβ zero    h = hβ
  press ℓ ε ρ B hB j v β hβ (suc x) h = nextLN _ (press ℓ ε ρ B hB j v β hβ x h)
  press ℓ ε ρ B hB j v β hβ (lim f) (hf , adj) =
    ((λ n → proj₁ (press ℓ ε ρ B hB j v β hβ (f n) (hf n))) , (λ n → monos ℓ ε ρ B j v β (adj n)))
    , ◃t (proj₂ (press ℓ ε ρ B hB j v β hβ (f zero) (hf zero))) (◃l zero)
  press ℓ ε ρ B hB j v β hβ (Ω p g) h =
    kp-ind ℓ ε ρ p v (LN j)
      (λ q cv gd →
        (λ z hz → proj₁ (press ℓ ε ρ B hB j v β hβ (g (cv z)) (h (cv z) (proj₂ gd z hz))))
        , ◃t (proj₂ (press ℓ ε ρ B hB j v β hβ (g (cv (fromBr j q zero)))
                      (h _ (proj₂ gd _ (legFrom j q zero tt))))) ◃w)
      (cumLN _ (λ n → press ℓ ε ρ B hB j v β hβ (g _) (h _ (iterInv (LegBr ℓ p) _ _ (legFrom ℓ p zero tt)
        (λ z hz → legFrom ℓ p _ (proj₁ (press ℓ ε ρ B hB (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p))
          (proj₂ hB (at ℓ p) (posW ℓ p)) (g z) (h z hz)))) n))))
  press ℓ ε ρ B hB _ self β hβ (up x c y) (hx , hy , zy) =
    Up-LN (chL ℓ c) (down stop c) (ψs ℓ ε ρ B ℓ self β x) (press ℓ ε ρ B hB ℓ self β hβ x hx)
      (chT ℓ c y) (legCh ℓ c y hy)
  press (suc a) ε ρ B hB j (ins v) β hβ (up x _ y) (hx , hy , zy) =
    press a ε ρ (dS a ε ρ B x) (pres⊥ (suc a) ε ρ B hB x hx , λ j′ w′ → press (suc a) ε ρ B hB j′ (ins w′) (bs B j′ (ins w′)) (proj₂ hB j′ (ins w′)) x hx) j v _ (press (suc a) ε ρ B hB j (ins v) β hβ x hx) y hy
  press (lim g) ε (ρc , R) B hB j (inl n v) β hβ (up x m y) (hx , hy , zy) =
    caseW-ind (LN j) (way g R m n)
      (λ r → press (g n) (ε n) (ρc n) (dL g ε (ρc , R) B n x) (pres⊥ (lim g) ε (ρc , R) B hB x hx , λ j′ w′ → press (lim g) ε (ρc , R) B hB j′ (inl n w′) (bs B j′ (inl n w′)) (proj₂ hB j′ (inl n w′)) x hx) j v _
        (press (lim g) ε (ρc , R) B hB j (inl n v) β hβ x hx)
        (emb (g n) (ε n) r y) (emb-leg (g n) (ε n) r y hy zy))
      (λ r → press (g m) (ε m) (ρc m) (dL g ε (ρc , R) B m x) (pres⊥ (lim g) ε (ρc , R) B hB x hx , λ j′ w′ → press (lim g) ε (ρc , R) B hB j′ (inl m w′) (bs B j′ (inl m w′)) (proj₂ hB j′ (inl m w′)) x hx) j (v ∙ r) _
        (press (lim g) ε (ρc , R) B hB j (inl n v) β hβ x hx) y hy)
      (fbLN _ (press (lim g) ε (ρc , R) B hB j (inl n v) β hβ x hx) (g m) (ε m) (ρc m) y hy zy)
  press (lim g) ε ρ B hB j (inlu vs) β hβ (up x m y) (hx , hy , zy) =
    press (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) (pres⊥ (lim g) ε ρ B hB x hx , λ j′ w′ → press (lim g) ε ρ B hB j′ (inl m w′) (bs B j′ (inl m w′)) (proj₂ hB j′ (inl m w′)) x hx) j (vs m) _
      (press (lim g) ε ρ B hB j (inlu vs) β hβ x hx) y hy
  press (Ωₗ k h) ε ρ B hB j (ink v) β hβ (up x c y) (hx , hy , zy) =
    press (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) (pres⊥ (Ωₗ k h) ε ρ B hB x hx , λ j′ w′ → press (Ωₗ k h) ε ρ B hB j′ (inb c w′) (bs B j′ (inb c w′)) (proj₂ hB j′ (inb c w′)) x hx) j
      (v ∙ proj₁ (proj₂ ε c)) _ (press (Ωₗ k h) ε ρ B hB j (ink v) β hβ x hx) y hy
  press (Ωₗ k h) ε ρ B hB j (inu vs) β hβ (up x c y) (hx , hy , zy) =
    press (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) (pres⊥ (Ωₗ k h) ε ρ B hB x hx , λ j′ w′ → press (Ωₗ k h) ε ρ B hB j′ (inb c w′) (bs B j′ (inb c w′)) (proj₂ hB j′ (inb c w′)) x hx) j (vs c) _
      (press (Ωₗ k h) ε ρ B hB j (inu vs) β hβ x hx) y hy
  press (Ωₗ k h) ε ρ B hB j (inb c′ v) β hβ (up x c y) (hx , hy , zy) =
    fbLN _ (press (Ωₗ k h) ε ρ B hB j (inb c′ v) β hβ x hx) (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) y hy zy
```

孩子的底合法 (供外部引用; 互递归块里逐处内联, 使每次调用的层号字面不增)。

```agda

legS : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) → LegB (suc a) B → (x : Tr (suc a))
     → Leg (suc a) x → LegB a (dS a ε ρ B x)
legS a ε ρ B hB x hx = pres⊥ (suc a) ε ρ B hB x hx
  , λ j w → press (suc a) ε ρ B hB j (ins w) (bs B j (ins w)) (proj₂ hB j (ins w)) x hx

legL : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) → LegB (lim g) B → (n : ℕ)
     (x : Tr (lim g)) → Leg (lim g) x → LegB (g n) (dL g ε ρ B n x)
legL g ε ρ B hB n x hx = pres⊥ (lim g) ε ρ B hB x hx
  , λ j w → press (lim g) ε ρ B hB j (inl n w) (bs B j (inl n w)) (proj₂ hB j (inl n w)) x hx

legW : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) → LegB (Ωₗ k h) B
     → (c : Tr k) (x : Tr (Ωₗ k h)) → Leg (Ωₗ k h) x → LegB (h c) (dW k h ε ρ B c x)
legW k h ε ρ B hB c x hx = pres⊥ (Ωₗ k h) ε ρ B hB x hx
  , λ j w → press (Ωₗ k h) ε ρ B hB j (inb c w) (bs B j (inb c w)) (proj₂ hB j (inb c w)) x hx
```

## 闭项合法 (无前提)

```agda
ψ₀-leg : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (x : Tr ℓ) → Leg ℓ x → Leg zero (ψ₀ ℓ ε ρ x)
ψ₀-leg ℓ ε ρ x h = proj₁ (pres⊥ ℓ ε ρ (B₀ ℓ) (LegB₀ ℓ) x h)

twᶜ : ℕ → Tr zero
twᶜ n = ψ₀ (tw n) (Ev-tw n) (Rt-tw n) (Ωt (tw n))

twᶜ-leg : (n : ℕ) → Leg zero (twᶜ n)
twᶜ-leg n = ψ₀-leg (tw n) (Ev-tw n) (Rt-tw n) (Ωt (tw n)) (Ωt-leg (tw n))

EBOᶜ : Tr zero
EBOᶜ = ψ₀ Λ Ev-Λ Rt-Λ (Ωt Λ)

EBOᶜ-leg : Leg zero EBOᶜ
EBOᶜ-leg = ψ₀-leg Λ Ev-Λ Rt-Λ (Ωt Λ) (Ωt-leg Λ)
```

## 合法性给出的路径

第一位置序的每条规则给一条不经下标层侧的路径: 后继 `ins`, 极限的第 n 项 `inl n`, 结点的第一分支 `inb zero`, 嵌入 `⊑lift`, 孩子里的一步在左加之下保持 (`⊕⊑`).

```agda
↑ch≡ : (k : L) (c : Ch k) (y : ChT k c) → ↑ch k c y ≡ ↑ (chL k c) (chT k c y)
↑ch≡ (suc a)  _ y = refl
↑ch≡ (lim g)  n y = refl
↑ch≡ (Ωₗ k h) c y = refl

◃→⊑ : ∀ {k x y} → k ⊢ x ◃ y → ↑ k x ⊑ ↑ k y
◃→⊑ ◃s       = ins self
◃→⊑ (◃l n)   = inl n self
◃→⊑ ◃w       = inb zero self
◃→⊑ {k} (◃u {x = x} {c = c} {y = y} _) = ⊑lift (↑ k x) (↑ch k c y)
◃→⊑ {k} (◃c {x = x} {c = c} {y′ = y′} {y = y} d) =
  subst (λ u → ↑ k x ⊕ ↑ch k c y′ ⊑ ↑ k x ⊕ u) (↑ch≡⁻ c y)
    (subst (λ u → ↑ k x ⊕ u ⊑ ↑ k x ⊕ ↑ (chL k c) (chT k c y)) (↑ch≡⁻ c y′) (⊕⊑ (↑ k x) (◃→⊑ d)))
  where
  ↑ch≡⁻ : (c : Ch k) (y : ChT k c) → ↑ (chL k c) (chT k c y) ≡ ↑ch k c y
  ↑ch≡⁻ c y with ↑ch k c y | ↑ch≡ k c y
  ... | _ | refl = refl
◃→⊑ (◃t d e) = ⊑-trans (◃→⊑ d) (◃→⊑ e)
```

合法树读出的偏移的路线: ℕ 极限处的相邻路径来自相邻项的第一位置序. Ω 结点的分支是任意树 (不带合法性), 那里取 `RtP₀`.

```agda
mutual
  RtP↑ : (k : L) (t : Tr k) → Leg k t → RtP (↑ k t)
  RtP↑ k zero       h = tt
  RtP↑ k (suc x)    h = RtP↑ k x h
  RtP↑ k (lim f)    (hf , adj) = (λ n → RtP↑ k (f n) (hf n)) , just (λ n → ◃→⊑ (adj n))
  RtP↑ k (Ω p g)    h = Rt₀ (at k p) , λ c → RtP₀ (↑ k (g (fromBr k p c)))
  RtP↑ k (up x c y) (hx , hy , zy) = RtP⊕ (↑ k x) (↑ch k c y) (RtP↑ k x hx) (RtP↑ch k c y hy)

  RtP↑ch : (k : L) (c : Ch k) (y : ChT k c) → LegCh k c y → RtP (↑ch k c y)
  RtP↑ch (suc a)  _ y h = RtP↑ a y h
  RtP↑ch (lim g)  n y h = RtP↑ (g n) y h
  RtP↑ch (Ωₗ k h) c y e = RtP↑ (h c) y e
```
