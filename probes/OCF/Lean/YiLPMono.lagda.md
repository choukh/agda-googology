# 合法块: 起点单调与基底单调的陈述

> 判决: 成品候选. 编译定理, 无前提: 折叠对起点单调 (`ψs-start`: 底不变, 起点 β 的值变大, 对一切层号, 一切树, 一切目标路径, 输出的值不降); 上折对底单调 (`Up-base`); 第 0 层的树基底单调 (`bm-zero⊥`, `bm-zeros`).
> 陈述 (未证, 未否定): 底的序 `_⊴_` (各分量的值逐个不降), 一棵树的基底单调 `BM⊥ᵉ`, `BM⊥`, `BMs`, 规范域上的 `BaseMonoΩt`, 下一站分支的坐标单调 `CoordMono`. 条件定理 `bm-Nx`: `CoordMono a` 推出下一站 Ω 树基底单调.
> 不否定什么. 对一切树的 `BM⊥` 不成立 ([YiLPNoBM](YiLPNoBM.lagda.md)); 推出 Into 在 [YiLPInto](YiLPInto.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPMono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLPVal hiding (emb; emb-mono)
open import OCF.Lean.YiLPIface using (Nx; Ev-Nx; Rt-Nx)
```

## 运算对值单调

```agda
+≼ : ∀ {j} {a a′ b b′ : Tr j} → val j a ≼ val j a′ → val j b ≼ val j b′ → val j (a + b) ≼ val j (a′ + b′)
+≼ {j} {a} {a′} {b} {b′} da db =
  ≼-trans (proj₁ (val-+ a b)) (≼-trans (⊹-monoˡ da (val j b)) (≼-trans (⊹-mono (val j a′) db) (proj₂ (val-+ a′ b′))))

iter≼ : ∀ {j} {b b′ : Tr j} → val j b ≼ val j b′ → (n : ℕ) → val j (iter (b +_) b n) ≼ val j (iter (b′ +_) b′ n)
iter≼ d zero    = d
iter≼ d (suc n) = +≼ d (iter≼ d n)

next≼ : ∀ {j} {b b′ : Tr j} (nb : j ⊢ zero ◃ b) (nb′ : j ⊢ zero ◃ b′) → val j b ≼ val j b′
      → val j (next b nb) ≼ val j (next b′ nb′)
next≼ nb nb′ d = l≼ (λ n → ≼l n (iter≼ d n))

cum≼ : ∀ {j} (F F′ : ℕ → Tr j) → ((n : ℕ) → val j (F n) ≼ val j (F′ n)) → (n : ℕ) → val j (cum F n) ≼ val j (cum F′ n)
cum≼ F F′ h zero    = h zero
cum≼ F F′ h (suc n) = +≼ (cum≼ F F′ h n) (h (suc n))

limc≼ : ∀ {j} (F F′ : ℕ → Tr j) (nz : (n : ℕ) → j ⊢ zero ◃ F n) (nz′ : (n : ℕ) → j ⊢ zero ◃ F′ n)
      → ((n : ℕ) → val j (F n) ≼ val j (F′ n)) → val j (limc F nz) ≼ val j (limc F′ nz′)
limc≼ F F′ nz nz′ h = l≼ (λ n → ≼l n (cum≼ F F′ h n))
```

## 上折对底单调

```agda
mutual
  Up-base : ∀ {ℓ} (j : L) (d : Dn ℓ j) (b b′ : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (nb′ : ℓ ⊢ zero ◃ b′) (y : Tr j)
          → val ℓ b ≼ val ℓ b′ → val ℓ (Up j d b nb y) ≼ val ℓ (Up j d b′ nb′ y)
  Up-base j        d b b′ nb nb′ zero      h = h
  Up-base j        d b b′ nb nb′ (suc y)   h =
    next≼ (Up-nz j d b nb y) (Up-nz j d b′ nb′ y) (Up-base j d b b′ nb nb′ y h)
  Up-base j        d b b′ nb nb′ (lim f a) h = l≼ (λ n → ≼l n (Up-base j d b b′ nb nb′ (f n) h))
  Up-base j        d b b′ nb nb′ (Ω p g)   h = Ω≼ (λ z → ≼Ω z (Up-base j d b b′ nb nb′ (g (mvBr d p z)) h))
  Up-base (suc a)  d b b′ nb nb′ (up y _ y′ _) h =
    Up-base a (down d tt) _ _ (Up-nz (suc a) d b nb y) (Up-nz (suc a) d b′ nb′ y) y′ (Up-base (suc a) d b b′ nb nb′ y h)
  Up-base (lim g)  d b b′ nb nb′ (up y n y′ _) h =
    Up-base (g n) (down d n) _ _ (Up-nz (lim g) d b nb y) (Up-nz (lim g) d b′ nb′ y) y′ (Up-base (lim g) d b b′ nb nb′ y h)
  Up-base (Ωₗ k h) d b b′ nb nb′ (up y c y′ _) e =
    Up-base (h c) (down d c) _ _ (Up-nz (Ωₗ k h) d b nb y) (Up-nz (Ωₗ k h) d b′ nb′ y) y′ (Up-base (Ωₗ k h) d b b′ nb nb′ y e)
  Up-base zero     d b b′ nb nb′ (up y () _ _) h

Upc-base≼ : (ℓ : L) (c : Ch ℓ) (b b′ : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) (nb′ : ℓ ⊢ zero ◃ b′) (y : ChT ℓ c)
          → val ℓ b ≼ val ℓ b′ → val ℓ (Upc ℓ c b nb y) ≼ val ℓ (Upc ℓ c b′ nb′ y)
Upc-base≼ (suc a)  c b b′ nb nb′ y h = Up-base a (down stop c) b b′ nb nb′ y h
Upc-base≼ (lim g)  n b b′ nb nb′ y h = Up-base (g n) (down stop n) b b′ nb nb′ y h
Upc-base≼ (Ωₗ k h) c b b′ nb nb′ y e = Up-base (h c) (down stop c) b b′ nb nb′ y e
```

## 保留判定的两侧归纳原理

`kp` 的判定只看层号, 证据, 路线, 槽位与目标路径, 不看两个续延; 所以两侧同时落在 "保留" 或同时落在默认.

```agda
mutual
  kp-ind₂ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (p : Pos ℓ) {j : L} (v : j ≤ ℓ) {X : Set} (Q : X → X → Set)
    {K K′ : (q : Pos j) → (Br j q → Br ℓ p) → X} {d d′ : X}
    → ((q : Pos j) (cv : Br j q → Br ℓ p) → Q (K q cv) (K′ q cv)) → Q d d′
    → Q (kp ℓ ε ρ p v K d) (kp ℓ ε ρ p v K′ d′)
  kp-ind₂ ℓ        ε ρ p       self      Q hk hd = hk p (λ z → z)
  kp-ind₂ (suc a)  ε ρ p       (ins v)   Q hk hd = kp⁼-ind₂ a ε ρ p v Q hk hd
  kp-ind₂ (lim g)  ε (ρc , R) (m , p) (inl n v) Q hk hd with way g R m n
  ... | fwd r = kp⁼-ind₂ (g n) (ε n) (ρc n) (psh r p) v Q (λ q cv → hk q (λ z → pshBr r p (cv z))) hd
  ... | bwd r = kp⁼-ind₂ (g m) (ε m) (ρc m) p (v ∙ r) Q hk hd
  kp-ind₂ (lim g)  ε (ρc , R) (m , p) (inlu vs) Q hk hd = kp⁼-ind₂ (g m) (ε m) (ρc m) p (vs m) Q hk hd
  kp-ind₂ (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (ink v)    Q hk hd = kp⁼-ind₂ k ek ρk t v Q hk hd
  kp-ind₂ (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inb c v)  Q hk hd =
    kp⁼-ind₂ (h c) (proj₂ (e c)) (ρc c) (psh (proj₁ (e c)) t) v Q
      (λ q cv → hk q (λ z → pshBr (proj₁ (e c)) t (cv z))) hd
  kp-ind₂ (Ωₗ k h) (ek , e) (ρk , ρc) (inj₁ t)       (inu vs)   Q hk hd =
    kp⁼-ind₂ (h zero) (proj₂ (e zero)) (ρc zero) (psh (proj₁ (e zero)) t) (vs zero) Q
      (λ q cv → hk q (λ z → pshBr (proj₁ (e zero)) t (cv z))) hd
  kp-ind₂ (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (ink v)    Q hk hd =
    kp⁼-ind₂ (h c) (proj₂ (e c)) (ρc c) t (v ∙ proj₁ (e c)) Q hk hd
  kp-ind₂ (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (inu vs)   Q hk hd =
    kp⁼-ind₂ (h c) (proj₂ (e c)) (ρc c) t (vs c) Q hk hd
  kp-ind₂ (Ωₗ k h) (ek , e) (ρk , ρc) (inj₂ (c , t)) (inb c′ v) Q hk hd = hd

  kp⁼-ind₂ : (a : L) (ε : Ev a) (ρ : Rt a) (p : Pos⁼ a) {j : L} (v : j ≤ a) {X : Set} (Q : X → X → Set)
    {K K′ : (q : Pos j) → (Br j q → Br⁼ a p) → X} {d d′ : X}
    → ((q : Pos j) (cv : Br j q → Br⁼ a p) → Q (K q cv) (K′ q cv)) → Q d d′
    → Q (kp⁼ a ε ρ p v K d) (kp⁼ a ε ρ p v K′ d′)
  kp⁼-ind₂ a ε ρ (inj₁ _) v Q hk hd = hd
  kp⁼-ind₂ a ε ρ (inj₂ p) v Q hk hd = kp-ind₂ a ε ρ p v Q hk hd
```

## 起点单调

底 B 不变, 只换起点 β. 回灌链用的是底的分量 `bs B`, 不用 β, 所以两边的链坐标逐字相同; 孩子的底同理.

```agda
ψs-start : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β β′ : Tr j)
  (nβ : j ⊢ zero ◃ β) (nβ′ : j ⊢ zero ◃ β′) (x : Tr ℓ)
  → val j β ≼ val j β′ → val j (ψs ℓ ε ρ B j w β nβ x) ≼ val j (ψs ℓ ε ρ B j w β′ nβ′ x)
ψs-start ℓ ε ρ B j w β β′ nβ nβ′ zero      h = h
ψs-start ℓ ε ρ B j w β β′ nβ nβ′ (suc x)   h =
  next≼ (nzs ℓ ε ρ B j w β nβ x) (nzs ℓ ε ρ B j w β′ nβ′ x) (ψs-start ℓ ε ρ B j w β β′ nβ nβ′ x h)
ψs-start ℓ ε ρ B j w β β′ nβ nβ′ (lim f a) h = l≼ (λ n → ≼l n (ψs-start ℓ ε ρ B j w β β′ nβ nβ′ (f n) h))
ψs-start ℓ ε ρ B j w β β′ nβ nβ′ (Ω p g)   h =
  kp-ind₂ ℓ ε ρ p w (λ s t → val j s ≼ val j t)
    (λ q cv → Ω≼ (λ z → ≼Ω z (ψs-start ℓ ε ρ B j w β β′ nβ nβ′ (g (cv z)) h)))
    (limc≼ _ _ _ _ (λ n → ψs-start ℓ ε ρ B j w β β′ nβ nβ′
      (g (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (g z))) (br0 ℓ p) n)) h))
ψs-start ℓ ε ρ B _ self β β′ nβ nβ′ (up x c y e) h =
  Upc-base≼ ℓ c _ _ (nzs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β′ nβ′ x) y
    (ψs-start ℓ ε ρ B ℓ self β β′ nβ nβ′ x h)
ψs-start (suc a) ε ρ B j (ins w) β β′ nβ nβ′ (up x _ y e) h =
  ψs-start a ε ρ (dS a ε ρ B x) j w _ _ (nzs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β′ nβ′ x) y
    (ψs-start (suc a) ε ρ B j (ins w) β β′ nβ nβ′ x h)
ψs-start (lim g) ε (ρc , R) B j (inl n w) β β′ nβ nβ′ (up x m y e) h =
  caseW-ind₂ (λ s t → val j s ≼ val j t) (way g R m n)
    (λ v → ψs-start (g n) (ε n) (ρc n) (dL g ε (ρc , R) B n x) j w _ _
      (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β′ nβ′ x)
      (emb (g n) (ε n) v y e) (ψs-start (lim g) ε (ρc , R) B j (inl n w) β β′ nβ nβ′ x h))
    (λ v → ψs-start (g m) (ε m) (ρc m) (dL g ε (ρc , R) B m x) j (w ∙ v) _ _
      (nzs (lim g) ε (ρc , R) B j (inl n w) β nβ x) (nzs (lim g) ε (ρc , R) B j (inl n w) β′ nβ′ x)
      y (ψs-start (lim g) ε (ρc , R) B j (inl n w) β β′ nβ nβ′ x h))
ψs-start (lim g) ε (ρc , R) B j (inlu ws) β β′ nβ nβ′ (up x m y e) h =
  ψs-start (g m) (ε m) (ρc m) (dL g ε (ρc , R) B m x) j (ws m) _ _
    (nzs (lim g) ε (ρc , R) B j (inlu ws) β nβ x) (nzs (lim g) ε (ρc , R) B j (inlu ws) β′ nβ′ x)
    y (ψs-start (lim g) ε (ρc , R) B j (inlu ws) β β′ nβ nβ′ x h)
ψs-start (Ωₗ k h) ε ρ B j (ink w) β β′ nβ nβ′ (up x c y e) d =
  ψs-start (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (w ∙ proj₁ (proj₂ ε c)) _ _
    (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β′ nβ′ x)
    y (ψs-start (Ωₗ k h) ε ρ B j (ink w) β β′ nβ nβ′ x d)
ψs-start (Ωₗ k h) ε ρ B j (inu ws) β β′ nβ nβ′ (up x c y e) d =
  ψs-start (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (ws c) _ _
    (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β′ nβ′ x)
    y (ψs-start (Ωₗ k h) ε ρ B j (inu ws) β β′ nβ nβ′ x d)
ψs-start (Ωₗ k h) ε ρ B j (inb c′ w) β β′ nβ nβ′ (up x c y e) d =
  +≼ (ψs-start (Ωₗ k h) ε ρ B j (inb c′ w) β β′ nβ nβ′ x d)
     (≼-refl (val j (ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y))))
```

## 基底单调: 陈述

底的序: 第 0 层分量与每个目标分量的值逐个不降. `BM⊥ ℓ x`, `BMs ℓ x`: 对这棵树, 底按 `_⊴_` 变大 (后者起点也按值变大) 时折叠的值不降. 规范域取各层的 Ω 树 `Ωt ℓ`.

```agda
infix 4 _⊴_
_⊴_ : {ℓ : L} → Base ℓ → Base ℓ → Set
_⊴_ {ℓ} B B′ = (val zero (b⊥ B) ≼ val zero (b⊥ B′)) × ((j : L) (w : j ≤ ℓ) → val j (bs B j w) ≼ val j (bs B′ j w))

BM⊥ᵉ : (ℓ : L) → Ev ℓ → Rt ℓ → Tr ℓ → Set
BM⊥ᵉ ℓ ε ρ x = (B B′ : Base ℓ) → B ⊴ B′ → val zero (ψ⊥ ℓ ε ρ B x) ≼ val zero (ψ⊥ ℓ ε ρ B′ x)

BM⊥ : (ℓ : L) → Tr ℓ → Set
BM⊥ ℓ x = (ε : Ev ℓ) (ρ : Rt ℓ) → BM⊥ᵉ ℓ ε ρ x

BMs : (ℓ : L) → Tr ℓ → Set
BMs ℓ x = (ε : Ev ℓ) (ρ : Rt ℓ) (B B′ : Base ℓ) → B ⊴ B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr j)
  (nβ : j ⊢ zero ◃ β) (nβ′ : j ⊢ zero ◃ β′) → val j β ≼ val j β′
  → val j (ψs ℓ ε ρ B j w β nβ x) ≼ val j (ψs ℓ ε ρ B′ j w β′ nβ′ x)

BaseMonoΩt : Set
BaseMonoΩt = (ℓ : L) → BM⊥ ℓ (Ωt ℓ)
```

第 0 层没有槽位与孩子, 所以第 0 层的每棵树都基底单调 (`BM⊥`, `BMs` 的实例).

```agda
bm-zero⊥ : (x : Tr zero) → BM⊥ zero x
bm-zero⊥ zero          ε ρ B B′ (h⊥ , hs) = h⊥
bm-zero⊥ (suc x)       ε ρ B B′ h =
  next≼ (nz⊥ zero ε ρ B x) (nz⊥ zero ε ρ B′ x) (bm-zero⊥ x ε ρ B B′ h)
bm-zero⊥ (lim f a)     ε ρ B B′ h = l≼ (λ n → ≼l n (bm-zero⊥ (f n) ε ρ B B′ h))
bm-zero⊥ (Ω () _)
bm-zero⊥ (up _ () _ _)

bm-zeros : (x : Tr zero) → BMs zero x
bm-zeros zero          ε ρ B B′ hB j w β β′ nβ nβ′ h = h
bm-zeros (suc x)       ε ρ B B′ hB j w β β′ nβ nβ′ h =
  next≼ (nzs zero ε ρ B j w β nβ x) (nzs zero ε ρ B′ j w β′ nβ′ x) (bm-zeros x ε ρ B B′ hB j w β β′ nβ nβ′ h)
bm-zeros (lim f a)     ε ρ B B′ hB j w β β′ nβ nβ′ h = l≼ (λ n → ≼l n (bm-zeros (f n) ε ρ B B′ hB j w β β′ nβ nβ′ h))
bm-zeros (Ω () _)
bm-zeros (up _ () _ _)
```

## 下一站的 Ω 树: 基底单调归约到坐标单调

`Gc a c`: 下一站 Ω 树在坐标 c 的分支. `CoordMono a ea ra`: 底按 `_⊴_` 变大, 坐标的值也变大时, 这一分支到第 0 层的折叠, 以及到下标层 a 的折叠 (起点取底在 a 上的分量, 即回灌链的一步) 的值都不降. 两个坐标的孩子层 a ⊕ ↑c 与 a ⊕ ↑c′ 一般不是同一个层号.
`bm-Nx`: 编译定理, 前提 `CoordMono`: 下一站的 Ω 树基底单调 (两条回灌链逐项按值比较).

```agda
Gc : (a : L) (c : Tr a) → Tr (Nx a)
Gc a c = up zero c (Ωt (a ⊕ ↑ a c)) (Ωt-nz (a ⊕ ↑ a c))

CoordMono : (a : L) → Ev a → Rt a → Set
CoordMono a ea ra = (B B′ : Base (Nx a)) → B ⊴ B′ → (c c′ : Tr a) → val a c ≼ val a c′
  → (val zero (ψ⊥ (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B (Gc a c)) ≼ val zero (ψ⊥ (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B′ (Gc a c′)))
  × (val a (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) (bs B a (ink self)) (ns B a (ink self)) (Gc a c))
     ≼ val a (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B′ a (ink self) (bs B′ a (ink self)) (ns B′ a (ink self)) (Gc a c′)))

bm-Nx : (a : L) (ea : Ev a) (ra : Rt a) → CoordMono a ea ra → BM⊥ᵉ (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) (Ωt (Nx a))
bm-Nx a ea ra cm B B′ hB =
  limc≼ (F B) (F B′) (nF B) (nF B′) (λ n → proj₁ (cm B B′ hB _ _ (chain n)))
  where
  st : Base (Nx a) → Tr a → Tr a
  st B c = ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) (bs B a (ink self)) (ns B a (ink self)) (Gc a c)
  chain : (n : ℕ) → val a (iter (st B) zero n) ≼ val a (iter (st B′) zero n)
  chain zero    = z≼
  chain (suc n) = proj₂ (cm B B′ hB _ _ (chain n))
  F : Base (Nx a) → ℕ → Tr zero
  F B n = ψ⊥ (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B (Gc a (iter (st B) zero n))
  nF : (B : Base (Nx a)) (n : ℕ) → zero ⊢ zero ◃ F B n
  nF B n = nz⊥ (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B (Gc a (iter (st B) zero n))
```
