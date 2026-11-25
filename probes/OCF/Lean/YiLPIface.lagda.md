# 合法块的接口

> 判决: 接口 (只陈述), 成品候选. 字段照 `YiLimIface.Iface` 选, 搬到合法块 (`YiLegBlock`, `YiLegFold`): 折叠带 "非零" 的证明 (`nz⊥`, `nzs`), 路线必带, 所以 `kp-none`, `J2-lim-none` 去掉; 合法是类型, 所以 `LegB`, `pres⊥`, `press`, `tw-leg`, `EBO-leg` 去掉.
> 塔不写死: `kstep`, `kall` 对任意带证据的层号 a 陈述在下一站 `Nx a` 上 (塔第 n+1 项就是 `Nx (tw n)`, 证据也逐字相同); 没有字段提到 Λ.
> 不否定什么. 实填在 [YiLPInst](YiLPInst.lagda.md) (`legI`); `kall` 的证明在 [YiLPKall](YiLPKall.lagda.md). 定稿 (2026-11-13), 只增不改.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPIface where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (iter; limc; Upc)
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold using (Base; base; b⊥; n⊥; bs; ns; chB)
```

## 下一站与它的证据

`Nx a` 是以 a 为下标层, 孩子层为 a ⊕ ↑c 的层号; 证据与路线照 `Ev-tw`, `Rt-tw` 的后继一行.

```agda
Nx : L → L
Nx a = Ωₗ a (λ c → a ⊕ ↑ a c)

evc : (a : L) → Ev a → (c : Tr a) → EvO a (↑ a c)
evc a ea c = EvO↑ a a ea self c

Ev-Nx : (a : L) → Ev a → Ev (Nx a)
Ev-Nx a ea = ea , λ c → lift a (↑ a c) , Ev⊕ a (↑ a c) ea (evc a ea c)

Rt-Nx : (a : L) → Rt a → Rt (Nx a)
Rt-Nx a ra = ra , λ c → Rt⊕ a (↑ a c) ra (RtP↑ a ra c)
```

## 槽位在基底里的见证

与 `YiPhiNegK` 同文 (`InB`, `prE`, `liftBr`, `brE`, `Kept`), 换成合法块的路径与槽位.

```agda
data InB (a : L) : (b : L) → Pos (a ⊕ b) → Set where
  ib0 : (p : Pos a) → InB a zero p
  ibS : ∀ {b t} → InB a b t → InB a (suc b) (inj₂ t)
  ibL : ∀ {g} (n : ℕ) {t} → InB a (g n) t → InB a (lim g) (n , inj₂ t)
  ibW : ∀ {k h} (c : Tr k) {t} → InB a (h c) t → InB a (Ωₗ k h) (inj₂ (c , inj₂ t))
  ibK : ∀ {k h} (t : Pos⁼ k) → InB a (Ωₗ k h) (inj₁ t)

prE : ∀ {a b t} → InB a b t → EvO a b → Pos⁼ a
prE (ib0 p)   eb            = inj₂ p
prE (ibS i)   eb            = prE i eb
prE (ibL n i) eb            = prE i (eb n)
prE (ibW c i) (v , ek , eb) = prE i (eb c)
prE (ibK t)   (v , ek , eb) = psh v t

liftBr : (a b : L) {K : L} (v : K ≤ a) (t : Pos⁼ K) → Br⁼ a (psh v t) → Br⁼ (a ⊕ b) (psh (v ∙ lift a b) t)
liftBr a zero     v t z = z
liftBr a (suc b)  v t z = liftBr a b v t z
liftBr a (lim g)  v t z = liftBr a (g zero) v t z
liftBr a (Ωₗ k h) v t z = liftBr a (h zero) v t z

brE : ∀ {a b t} (i : InB a b t) (eb : EvO a b) → Br⁼ a (prE i eb) → Br (a ⊕ b) t
brE (ib0 p)   eb            z = z
brE (ibS i)   eb            z = brE i eb z
brE (ibL n i) eb            z = brE i (eb n) z
brE (ibW c i) (v , ek , eb) z = brE i (eb c) z
brE {a} (ibK {h = h} t) (v , ek , eb) z = pshBr (v ∙ lift a (h zero)) t (liftBr a (h zero) v t z)

Kept : ∀ {j} → Pos j → Tr j → Set
Kept {j} p o = Σ (Br j p → Tr j) λ G′ → o ≡ Ω p G′
```

## 记录

```agda
record Iface : Set₁ where
  field
    ψ⊥  : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → Tr ℓ → Tr zero
    ψs  : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → (j : L) → j ≤ ℓ → (β : Tr j) → j ⊢ zero ◃ β → Tr ℓ → Tr j
    nz⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (x : Tr ℓ) → zero ⊢ zero ◃ ψ⊥ ℓ ε ρ B x
    nzs : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
        → j ⊢ zero ◃ ψs ℓ ε ρ B j w β nβ x
    kp⁼ : (a : L) (ε : Ev a) (ρ : Rt a) (p : Pos⁼ a) {j : L} (w : j ≤ a) {X : Set}
        → ((q : Pos j) → (Br j q → Br⁼ a p) → X) → X → X

  dS : (a : L) → Ev (suc a) → Rt (suc a) → Base (suc a) → Tr (suc a) → Base a
  dS a ε ρ B x = chB B (λ u → ins u) (ψ⊥ (suc a) ε ρ B x) (nz⊥ (suc a) ε ρ B x)
    (λ j′ w′ β′ n′ → ψs (suc a) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (suc a) ε ρ B j′ w′ β′ n′ x)

  dL : (g : ℕ → L) → Ev (lim g) → Rt (lim g) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
  dL g ε ρ B n x = chB B (λ u → inl n u) (ψ⊥ (lim g) ε ρ B x) (nz⊥ (lim g) ε ρ B x)
    (λ j′ w′ β′ n′ → ψs (lim g) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (lim g) ε ρ B j′ w′ β′ n′ x)

  dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Rt (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
  dW k h ε ρ B c x = chB B (λ u → inb c u) (ψ⊥ (Ωₗ k h) ε ρ B x) (nz⊥ (Ωₗ k h) ε ρ B x)
    (λ j′ w′ β′ n′ → ψs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x) (λ j′ w′ β′ n′ → nzs (Ωₗ k h) ε ρ B j′ w′ β′ n′ x)

  step : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (p : Pos ℓ) (G : Br ℓ p → Tr ℓ) → Br ℓ p → Br ℓ p
  step ℓ ε ρ B p G z =
    fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (ns B (at ℓ p) (posW ℓ p)) (G z))

  field
```

嵌入一致 (J2 一族, 到第 0 层的 J2⊥ 一族). 嵌入 `up x c y e` 带孩子非零的证明 e.

```agda
    J2-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) (j : L) (w : j ≤ a) (β : Tr j)
      (nβ : j ⊢ zero ◃ β) (x : Tr (suc a)) (y : Tr a) (e : a ⊢ zero ◃ y)
      → ψs (suc a) ε ρ B j (ins w) β nβ (up x tt y e)
      ≡ ψs a ε ρ (dS a ε ρ B x) j w (ψs (suc a) ε ρ B j (ins w) β nβ x) (nzs (suc a) ε ρ B j (ins w) β nβ x) y
    J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n)
      (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g n)) (e : g n ⊢ zero ◃ y)
      → ψs (lim g) ε ρ B j (inl n w) β nβ (up x n y e)
      ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w
          (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) y
    J2-limu : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (j : L) (ws : (n : ℕ) → j ≤ g n)
      (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (m : ℕ) (y : Tr (g m)) (e : g m ⊢ zero ◃ y)
      → ψs (lim g) ε ρ B j (inlu ws) β nβ (up x m y e)
      ≡ ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (ws m)
          (ψs (lim g) ε ρ B j (inlu ws) β nβ x) (nzs (lim g) ε ρ B j (inlu ws) β nβ x) y
    J2-Ωk : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (w : j ≤ k)
      (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
      → ψs (Ωₗ k h) ε ρ B j (ink w) β nβ (up x c y e)
      ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (w ∙ proj₁ (proj₂ ε c))
          (ψs (Ωₗ k h) ε ρ B j (ink w) β nβ x) (nzs (Ωₗ k h) ε ρ B j (ink w) β nβ x) y
    J2-Ωu : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
      (ws : (c : Tr k) → j ≤ h c) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
      (e : h c ⊢ zero ◃ y)
      → ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ (up x c y e)
      ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (ws c)
          (ψs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) (nzs (Ωₗ k h) ε ρ B j (inu ws) β nβ x) y
    J2⊥-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) (x : Tr (suc a)) (y : Tr a)
      (e : a ⊢ zero ◃ y) → ψ⊥ (suc a) ε ρ B (up x tt y e) ≡ ψ⊥ a ε ρ (dS a ε ρ B x) y
    J2⊥-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (x : Tr (lim g)) (n : ℕ)
      (y : Tr (g n)) (e : g n ⊢ zero ◃ y)
      → ψ⊥ (lim g) ε ρ B (up x n y e) ≡ ψ⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) y
    J2⊥-Ω : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (x : Tr (Ωₗ k h))
      (c : Tr k) (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
      → ψ⊥ (Ωₗ k h) ε ρ B (up x c y e) ≡ ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) y
```

单调 (对第一位置序), 自身行, 结点行.

```agda
    mono⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) {x y : Tr ℓ}
      → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε ρ B x ◃ ψ⊥ ℓ ε ρ B y
    monos : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β)
      {x y : Tr ℓ} → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε ρ B j w β nβ x ◃ ψs ℓ ε ρ B j w β nβ y

    self-up : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (β : Tr ℓ) (nβ : ℓ ⊢ zero ◃ β) (x : Tr ℓ) (c : Ch ℓ)
      (y : ChT ℓ c) (e : RCh ℓ c (chZ ℓ c) y)
      → ψs ℓ ε ρ B ℓ self β nβ (up x c y e) ≡ Upc ℓ c (ψs ℓ ε ρ B ℓ self β nβ x) (nzs ℓ ε ρ B ℓ self β nβ x) y

    node : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β)
      (p : Pos ℓ) (G : Br ℓ p → Tr ℓ)
      → ψs ℓ ε ρ B j w β nβ (Ω p G)
      ≡ kp⁼ ℓ ε ρ (inj₂ p) w (λ q cv → Ω q (λ z → ψs ℓ ε ρ B j w β nβ (G (cv z))))
          (limc (λ n → ψs ℓ ε ρ B j w β nβ (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n)))
                (λ n → nzs ℓ ε ρ B j w β nβ (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n))))
    node⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (p : Pos ℓ) (G : Br ℓ p → Tr ℓ)
      → ψ⊥ ℓ ε ρ B (Ω p G)
      ≡ limc (λ n → ψ⊥ ℓ ε ρ B (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n)))
             (λ n → nz⊥ ℓ ε ρ B (G (iter (step ℓ ε ρ B p G) (br0 ℓ p) n)))
```

ℕ 极限层号上不同号孩子: 保留判定两条, 嵌入两条 (路线必带, 只有 `fwd`, `bwd`).

```agda
    kp-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
      {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g m ≤ g n)
      → way g (proj₂ ρ) m n ≡ fwd v
      → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d
      ≡ kp⁼ (g n) (ε n) (proj₁ ρ n) (psh v p) w (λ q cv → K q (λ z → pshBr v p (cv z))) d
    kp-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
      {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g n ≤ g m)
      → way g (proj₂ ρ) m n ≡ bwd v
      → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d ≡ kp⁼ (g m) (ε m) (proj₁ ρ m) p (w ∙ v) K d
    J2-lim-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
      (w : j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y)
      (v : g n ≤ g m) → way g (proj₂ ρ) m n ≡ bwd v
      → ψs (lim g) ε ρ B j (inl n w) β nβ (up x m y e)
      ≡ ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (w ∙ v)
          (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) y
    J2-lim-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
      (w : j ≤ g n) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (lim g)) (y : Tr (g m)) (e : g m ⊢ zero ◃ y)
      (v : g m ≤ g n) → way g (proj₂ ρ) m n ≡ fwd v
      → ψs (lim g) ε ρ B j (inl n w) β nβ (up x m y e)
      ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w
          (ψs (lim g) ε ρ B j (inl n w) β nβ x) (nzs (lim g) ε ρ B j (inl n w) β nβ x) (emb (g n) (ε n) v y e)
```

下一站的 k 侧: 第一个孩子 (层号 a ⊕ 0, 即 a) 里的结点原样保留 (`kstep`); 对一切孩子 c, 槽位带见证且严格在基底 a 里的结点以基底槽位保留 (`kall`).

```agda
    kstep : (a : L) (ea : Ev a) (ra : Rt a) (B : Base (Nx a)) (β : Tr a) (nβ : a ⊢ zero ◃ β) (x : Tr (Nx a))
      (p : Pos a) (g : Br a p → Tr a) (e : a ⊢ zero ◃ Ω p g)
      → ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ (up x zero (Ω p g) e)
      ≡ Ω p (λ z → ψs a ea ra (dW a (λ c → a ⊕ ↑ a c) (Ev-Nx a ea) (Rt-Nx a ra) B zero x) a self
                     (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ x)
                     (nzs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ x) (g z))

    kall : (a : L) (ea : Ev a) (ra : Rt a) (B : Base (Nx a)) (β : Tr a) (nβ : a ⊢ zero ◃ β) (x : Tr (Nx a))
      (c : Tr a) {t : Pos (a ⊕ ↑ a c)} (G : Br (a ⊕ ↑ a c) t → Tr (a ⊕ ↑ a c)) (e : a ⊕ ↑ a c ⊢ zero ◃ Ω t G)
      (i : InB a (↑ a c) t) (p : Pos a) → prE i (evc a ea c) ≡ inj₂ p
      → Kept p (ψs (Nx a) (Ev-Nx a ea) (Rt-Nx a ra) B a (ink self) β nβ (up x c (Ω t G) e))
```
