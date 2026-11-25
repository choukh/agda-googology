# 合法性进块: 折叠

> 判决: 成品候选 (折叠, 原型). `YiLimFold` 的各行, 去掉 "没有路径" 的回退 (路线必带); 折叠 `ψ⊥`, `ψs` 与它的非零 `nz⊥`, `nzs`, 单调 `mono⊥`, `monos` 是一个互递归块, 因为输出的 ℕ 极限要交相邻项的步进, `next` 要交非零.
> 检查器接受 (停机按层号, 再按树或推导). "折叠保持合法" 是 `ψ⊥`, `ψs` 的类型; 链步的回灌 `fromBr ℓ p (ψs …)` 因此直接是合法分支.
> 不否定什么. 仍有回退的只有 `(Ωₗ k h, inb c′, up x c y)` 一行 (与 `YiLimFold` 同). 验收在 `YiLegCheck`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLegFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
```

## 底

底的每个分量自带非零的证明. `chB` 由 x 的折叠造孩子层的底 (在互递归块里逐处展开, 使每次调用的层号字面不增).

```agda
record Base (ℓ : L) : Set where
  constructor base
  field
    b⊥ : Tr zero
    n⊥ : zero ⊢ zero ◃ b⊥
    bs : (j : L) → j ≤ ℓ → Tr j
    ns : (j : L) (w : j ≤ ℓ) → j ⊢ zero ◃ bs j w
open Base public

B₀ : (ℓ : L) → Base ℓ
B₀ ℓ = base (Ωt zero) (Ωt-nz zero) (λ j _ → Ωt j) (λ j _ → Ωt-nz j)

chB : {ℓ ℓ′ : L} (B : Base ℓ) (inj : ∀ {j} → j ≤ ℓ′ → j ≤ ℓ)
  (F⊥ : Tr zero) (N⊥ : zero ⊢ zero ◃ F⊥)
  (Fs : (j : L) (w : j ≤ ℓ) (β : Tr j) → j ⊢ zero ◃ β → Tr j)
  (Ns : (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) → j ⊢ zero ◃ Fs j w β nβ) → Base ℓ′
chB B inj F⊥ N⊥ Fs Ns =
  base F⊥ N⊥ (λ j w → Fs j (inj w) (bs B j (inj w)) (ns B j (inj w)))
             (λ j w → Ns j (inj w) (bs B j (inj w)) (ns B j (inj w)))
```

## 保留判定与它的归纳原理

与 `YiLimFold.kp` 同文, ℕ 极限层号一行只有 `fwd`, `bwd`. 保留时交出的换型把第一分支送到第一分支 (`Good`).

```agda
mutual
  kp : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) {X : Set}
     → ((q : Pos j) → (Br j q → Br ℓ p) → X) → X → X
  kp ℓ        ε ρ p        self      K d = K p (λ z → z)
  kp (suc a)  ε ρ p        (ins w)   K d = kp⁼ a ε ρ p w K d
  kp (lim g)  ε (ρc , R) (m , p)  (inl n w) K d =
    caseW (way g R m n)
      (λ v → kp⁼ (g n) (ε n) (ρc n) (psh v p) w (λ q cv → K q (λ z → pshBr v p (cv z))) d)
      (λ v → kp⁼ (g m) (ε m) (ρc m) p (w ∙ v) K d)
  kp (lim g)  ε (ρc , R) (m , p)  (inlu ws) K d = kp⁼ (g m) (ε m) (ρc m) p (ws m) K d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (ink w)    K d = kp⁼ k ek ρk t w K d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inb c w)  K d =
    kp⁼ (h c) (proj₂ (e c)) (ρc c) (psh (proj₁ (e c)) t) w
      (λ q cv → K q (λ z → pshBr (proj₁ (e c)) t (cv z))) d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inu ws)   K d =
    kp⁼ (h zero) (proj₂ (e zero)) (ρc zero) (psh (proj₁ (e zero)) t) (ws zero)
      (λ q cv → K q (λ z → pshBr (proj₁ (e zero)) t (cv z))) d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (ink w)    K d =
    kp⁼ (h c) (proj₂ (e c)) (ρc c) t (w ∙ proj₁ (e c)) K d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (inu ws)   K d = kp⁼ (h c) (proj₂ (e c)) (ρc c) t (ws c) K d
  kp (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (inb c′ w) K d = d

  kp⁼ : (a : L) (ε : Ev a) (ρ : Rt a) (p : Pos⁼ a) {j : L} (w : j ≤ a) {X : Set}
      → ((q : Pos j) → (Br j q → Br⁼ a p) → X) → X → X
  kp⁼ a ε ρ (inj₁ _) w K d = d
  kp⁼ a ε ρ (inj₂ p) w K d = kp a ε ρ p w K d

Good : (ℓ : L) (p : Pos ℓ) (j : L) (q : Pos j) (cv : Br j q → Br ℓ p) → Set
Good ℓ p j q cv = cv (br0 j q) ≡ br0 ℓ p

Good⁼ : (a : L) (p : Pos⁼ a) (j : L) (q : Pos j) (cv : Br j q → Br⁼ a p) → Set
Good⁼ a p j q cv = cv (br0 j q) ≡ br0⁼ a p

mutual
  kp-ind : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (p : Pos ℓ) {j : L} (v : j ≤ ℓ) {X : Set} (Q : X → Set)
    {K : (q : Pos j) → (Br j q → Br ℓ p) → X} {d : X}
    → ((q : Pos j) (cv : Br j q → Br ℓ p) → Good ℓ p j q cv → Q (K q cv)) → Q d
    → Q (kp ℓ ε ρ p v K d)
  kp-ind ℓ        ε ρ p       self      Q hk hd = hk p (λ z → z) refl
  kp-ind (suc a)  ε ρ p       (ins v)   Q hk hd = kp⁼-ind a ε ρ p v Q hk hd
  kp-ind (lim g)  ε (ρc , R) (m , p) (inl n v) Q hk hd with way g R m n
  ... | fwd r = kp⁼-ind (g n) (ε n) (ρc n) (psh r p) v Q
      (λ q cv gd → hk q (λ z → pshBr r p (cv z)) (trans (cong (pshBr r p) gd) (pshFirst r p))) hd
  ... | bwd r = kp⁼-ind (g m) (ε m) (ρc m) p (v ∙ r) Q hk hd
  kp-ind (lim g)  ε (ρc , R) (m , p) (inlu vs) Q hk hd = kp⁼-ind (g m) (ε m) (ρc m) p (vs m) Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (ink v)    Q hk hd = kp⁼-ind k ek ρk t v Q hk hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inb c v)  Q hk hd =
    kp⁼-ind (h c) (proj₂ (e c)) (ρc c) (psh (proj₁ (e c)) t) v Q
      (λ q cv gd → hk q (λ z → pshBr (proj₁ (e c)) t (cv z))
        (trans (cong (pshBr (proj₁ (e c)) t) gd) (pshFirst (proj₁ (e c)) t))) hd
  kp-ind (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inu vs)   Q hk hd =
    kp⁼-ind (h zero) (proj₂ (e zero)) (ρc zero) (psh (proj₁ (e zero)) t) (vs zero) Q
      (λ q cv gd → hk q (λ z → pshBr (proj₁ (e zero)) t (cv z))
        (trans (cong (pshBr (proj₁ (e zero)) t) gd) (pshFirst (proj₁ (e zero)) t))) hd
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

## 折叠, 非零, 单调 (一个互递归块)

先写折叠的全部子句, 再写非零与单调的 (后者的类型要前者已经能化简).
ℕ 极限层号上不同号孩子的两行: m < n 时孩子树沿路径搬进孩子 n (`emb`), m ≥ n 时目标沿路径搬进孩子 m; 同号时路径是 `self`.

```agda
mutual
  ψ⊥ : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → Tr ℓ → Tr zero
  ψs : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → (j : L) → j ≤ ℓ → (β : Tr j) → j ⊢ zero ◃ β → Tr ℓ → Tr j
  nz⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (x : Tr ℓ) → zero ⊢ zero ◃ ψ⊥ ℓ ε ρ B x
  nzs : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
      → j ⊢ zero ◃ ψs ℓ ε ρ B j w β nβ x
  mono⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) {x y : Tr ℓ}
        → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε ρ B x ◃ ψ⊥ ℓ ε ρ B y
  monos : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) {x y : Tr ℓ}
        → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε ρ B j w β nβ x ◃ ψs ℓ ε ρ B j w β nβ y

  ψ⊥ ℓ ε ρ B zero      = b⊥ B
  ψ⊥ ℓ ε ρ B (suc x)   = next (ψ⊥ ℓ ε ρ B x) (nz⊥ ℓ ε ρ B x)
  ψ⊥ ℓ ε ρ B (lim f a) = lim (λ n → ψ⊥ ℓ ε ρ B (f n)) (λ n → mono⊥ ℓ ε ρ B (a n))
  ψ⊥ ℓ ε ρ B (Ω p g)   =
    limc (λ n → ψ⊥ ℓ ε ρ B (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n)))
         (λ n → nz⊥ ℓ ε ρ B (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n)))
  ψ⊥ (suc a) ε ρ B (up x _ y e) =
    ψ⊥ a ε ρ
      (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)) y
  ψ⊥ (lim g) ε (ρc , R) B (up x n y e) =
    ψ⊥ (g n) (ε n) (ρc n)
      (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x)) y
  ψ⊥ (Ωₗ k h) ε ρ B (up x c y e) =
    ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)) y
  ψ⊥ zero ε ρ B (up x () y e)

  ψs ℓ ε ρ B j w β nβ zero      = β
  ψs ℓ ε ρ B j w β nβ (suc x)   = next (ψs ℓ ε ρ B j w β nβ x) (nzs ℓ ε ρ B j w β nβ x)
  ψs ℓ ε ρ B j w β nβ (lim f a) = lim (λ n → ψs ℓ ε ρ B j w β nβ (f n)) (λ n → monos ℓ ε ρ B j w β nβ (a n))
  ψs ℓ ε ρ B j w β nβ (Ω p g)   =
    kp ℓ ε ρ p w (λ q cv → Ω q (λ z → ψs ℓ ε ρ B j w β nβ (g (cv z))))
      (limc (λ n → ψs ℓ ε ρ B j w β nβ (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n)))
            (λ n → nzs ℓ ε ρ B j w β nβ (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n))))
  ψs ℓ ε ρ B _ self β nβ (up x c y e) = Upc ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y
  ψs (suc a) ε ρ B j (ins w) β nβ (up x _ y e) =
    ψs a ε ρ
      (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x))
      j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) y
  ψs (lim g) ε (ρc , R) B j (inl n w) β nβ (up x m y e) =
    caseW (way g R m n)
      (λ v → ψs (g n) (ε n) (ρc n)
        (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j w (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (emb (g n) (ε n) v y e))
      (λ v → ψs (g m) (ε m) (ρc m)
        (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) y)
  ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ (up x m y e) =
    ψs (g m) (ε m) (ρc m)
      (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
      j (ws m) (ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) y
  ψs (Ωₗ k h) ε ρ B j (ink w) β nβ (up x c y e) =
    ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) y
  ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ (up x c y e) =
    ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
      j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) y
  ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e) =
    (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y)

  nz⊥ ℓ ε ρ B zero      = n⊥ B
  nz⊥ ℓ ε ρ B (suc x)   = ◃t (nz⊥ ℓ ε ρ B x) (◃l zero)
  nz⊥ ℓ ε ρ B (lim f a) = ◃t (nz⊥ ℓ ε ρ B (f zero)) (◃l zero)
  nz⊥ ℓ ε ρ B (Ω p g)   = ◃t (nz⊥ ℓ ε ρ B (g (br0 ℓ p))) (◃l zero)
  nz⊥ (suc a) ε ρ B (up x _ y e) =
    nz⊥ a ε ρ
      (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)) y
  nz⊥ (lim g) ε (ρc , R) B (up x n y e) =
    nz⊥ (g n) (ε n) (ρc n)
      (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x)) y
  nz⊥ (Ωₗ k h) ε ρ B (up x c y e) =
    nz⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)) y
  nz⊥ zero ε ρ B (up x () y e)

  nzs ℓ ε ρ B j w β nβ zero      = nβ
  nzs ℓ ε ρ B j w β nβ (suc x)   = ◃t (nzs ℓ ε ρ B j w β nβ x) (◃l zero)
  nzs ℓ ε ρ B j w β nβ (lim f a) = ◃t (nzs ℓ ε ρ B j w β nβ (f zero)) (◃l zero)
  nzs ℓ ε ρ B j w β nβ (Ω p g)   =
    kp-ind ℓ ε ρ p w (λ Z → j ⊢ zero ◃ Z)
      (λ q cv gd → ◃t (nzs ℓ ε ρ B j w β nβ (g (cv (br0 j q)))) ◃w)
      (◃t (nzs ℓ ε ρ B j w β nβ (g (br0 ℓ p))) (◃l zero))
  nzs ℓ ε ρ B _ self β nβ (up x c y e) = Upc-nz ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y
  nzs (suc a) ε ρ B j (ins w) β nβ (up x _ y e) =
    nzs a ε ρ
      (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x))
      j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) y
  nzs (lim g) ε (ρc , R) B j (inl n w) β nβ (up x m y e) =
    caseW-ind (λ Z → j ⊢ zero ◃ Z) (way g R m n)
      (λ v → nzs (g n) (ε n) (ρc n)
        (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j w (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (emb (g n) (ε n) v y e))
      (λ v → nzs (g m) (ε m) (ρc m)
        (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) y)
  nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ (up x m y e) =
    nzs (g m) (ε m) (ρc m)
      (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
      j (ws m) (ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) y
  nzs (Ωₗ k h) ε ρ B j (ink w) β nβ (up x c y e) =
    nzs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) y
  nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ (up x c y e) =
    nzs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
      j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) y
  nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e) =
    ◃t (nzs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x)
       (+-mono (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (ι-mono j (nz⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y)))

  mono⊥ ℓ ε ρ B ◃s     = ◃l zero
  mono⊥ ℓ ε ρ B (◃l n) = ◃l n
  mono⊥ ℓ ε ρ B ◃w     = ◃l zero
  mono⊥ (suc a) ε ρ B (◃u x _ y e) =
    mono⊥ a ε ρ
      (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)) e
  mono⊥ (lim g) ε (ρc , R) B (◃u x n y e) =
    mono⊥ (g n) (ε n) (ρc n)
      (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x)) e
  mono⊥ (Ωₗ k h) ε ρ B (◃u x c y e) =
    mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)) e
  mono⊥ zero ε ρ B (◃u x () y e)
  mono⊥ (suc a) ε ρ B (◃c x _ d) =
    mono⊥ a ε ρ
      (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)) d
  mono⊥ (lim g) ε (ρc , R) B (◃c x n d) =
    mono⊥ (g n) (ε n) (ρc n)
      (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x)) d
  mono⊥ (Ωₗ k h) ε ρ B (◃c x c d) =
    mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)) d
  mono⊥ zero ε ρ B (◃c x () d)
  mono⊥ ℓ ε ρ B (◃t d e) = ◃t (mono⊥ ℓ ε ρ B d) (mono⊥ ℓ ε ρ B e)

  monos ℓ ε ρ B j w β nβ ◃s     = ◃l zero
  monos ℓ ε ρ B j w β nβ (◃l n) = ◃l n
  monos ℓ ε ρ B j w β nβ (◃w {p = p} {g = g}) =
    kp-ind ℓ ε ρ p w (λ Z → j ⊢ ψs ℓ ε ρ B j w β nβ (g (br0 ℓ p)) ◃ Z)
      (λ q cv gd → subst (λ t → j ⊢ ψs ℓ ε ρ B j w β nβ (g t) ◃ Ω q (λ z → ψs ℓ ε ρ B j w β nβ (g (cv z)))) gd ◃w)
      (◃l zero)
  monos ℓ ε ρ B _ self β nβ (◃u x c y e) = Upc-base ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y e
  monos (suc a) ε ρ B j (ins w) β nβ (◃u x _ y e) =
    monos a ε ρ
      (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x))
      j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) e
  monos (lim g) ε (ρc , R) B j (inl n w) β nβ (◃u x m y e) =
    caseW-ind (λ Z → j ⊢ (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) ◃ Z) (way g R m n)
      (λ v → monos (g n) (ε n) (ρc n)
        (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j w (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (emb-nz (g n) (ε n) v y e))
      (λ v → monos (g m) (ε m) (ρc m)
        (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) e)
  monos (lim g) ε (ρc , R) B j (inlu ws) β nβ (◃u x m y e) =
    monos (g m) (ε m) (ρc m)
      (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
      j (ws m) (ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) e
  monos (Ωₗ k h) ε ρ B j (ink w) β nβ (◃u x c y e) =
    monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) e
  monos (Ωₗ k h) ε ρ B j (inu ws) β nβ (◃u x c y e) =
    monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
      j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) e
  monos (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (◃u x c y e) =
    +-mono (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (ι-mono j (nz⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y))
  monos ℓ ε ρ B _ self β nβ (◃c x c d) = Upc-mono ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) d
  monos (suc a) ε ρ B j (ins w) β nβ (◃c x _ d) =
    monos a ε ρ
      (chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x))
      j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) d
  monos (lim g) ε (ρc , R) B j (inl n w) β nβ (◃c x m d) =
    caseW-ind₂ (λ Z Z′ → j ⊢ Z ◃ Z′) (way g R m n)
      (λ v → monos (g n) (ε n) (ρc n)
        (chB B (λ u → inl n u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j w (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (emb-mono (g n) (ε n) v d))
      (λ v → monos (g m) (ε m) (ρc m)
        (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
        j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) d)
  monos (lim g) ε (ρc , R) B j (inlu ws) β nβ (◃c x m d) =
    monos (g m) (ε m) (ρc m)
      (chB B (λ u → inl m u) (ψ⊥ (lim g) ε (ρc , R) B x) (nz⊥ (lim g) ε (ρc , R) B x)
        (λ j′ w′ β′ n′ → ψs (lim g) ε (ρc , R) B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε (ρc , R) B j′ w′ β′ n′ x))
      j (ws m) (ψs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) d
  monos (Ωₗ k h) ε ρ B j (ink w) β nβ (◃c x c d) =
    monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) d
  monos (Ωₗ k h) ε ρ B j (inu ws) β nβ (◃c x c d) =
    monos (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
        (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x))
      j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) d
  monos (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (◃c x c d) =
    +-mono (ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x) (ι-mono j (mono⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) d))
  monos ℓ ε ρ B j w β nβ (◃t d e) = ◃t (monos ℓ ε ρ B j w β nβ d) (monos ℓ ε ρ B j w β nβ e)
```

## 孩子的底, 读法, 闭项

孩子的底供外部陈述引用 (与块里展开的逐字相同). `twᶜ n` 与 `EBOᶜ` 是第 0 层的树, 合法性是它们的类型.

```agda
dS : (a : L) → Ev (suc a) → Rt (suc a) → Base (suc a) → Tr (suc a) → Base a
dS a ε ρ B x = chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
  (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)

dL : (g : ℕ → L) → Ev (lim g) → Rt (lim g) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
dL g ε ρ B n x = chB B (λ u → inl n u) (ψ⊥ (lim g) ε ρ B x) (nz⊥ (lim g) ε ρ B x)
  (λ j′ w′ β′ n′ → ψs (lim g) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε ρ B j′ w′ β′ n′ x)

dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Rt (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
dW k h ε ρ B c x = chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
  (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)

ψ₀ : (ℓ : L) → Ev ℓ → Rt ℓ → Tr ℓ → Tr zero
ψ₀ ℓ ε ρ = ψ⊥ ℓ ε ρ (B₀ ℓ)

twᶜ : ℕ → Tr zero
twᶜ n = ψ₀ (tw n) (Ev-tw n) (Rt-tw n) (Ωt (tw n))

EBOᶜ : Tr zero
EBOᶜ = ψ₀ Λ Ev-Λ Rt-Λ (Ωt Λ)
```
