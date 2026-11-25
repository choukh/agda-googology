# ℕ 极限层号的路线: 接口

> 判决: 接口 (只陈述). 字段照 `YiUpIface.Iface`, 折叠多带一个路线证据 `Rt` (`YiLimBlock`), 另加保留判定 `kp⁼` 作字段与 ℕ 极限层号上不同号孩子的律: 结点三条 (`kp-fwd`, `kp-bwd`, `kp-none`), 嵌入三条 (`J2-lim-fwd`, `J2-lim-bwd`, `J2-lim-none`).
> 不同号且没有路径 (`none`) 时: 结点走默认, 嵌入走回退, 与 `YiUpFold` 同文. 律里的两个孩子只经 ℕ 编号的比较 `way` 出现, 被比较的槽位与目标路径都在同一个孩子层里.
> 不否定什么. 实填在 `YiLimCheck.limI` (塔各项, Λ, 以及带路径的层号如 ω+1). 定稿后只增不改.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLimIface where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; cum; Ωt; ι)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; Leg; LN)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiNegK using (InB; prE; evc; Kept)
open import OCF.Lean.YiUpBlock using (Upc)
open import OCF.Lean.YiLimBlock
```

```agda
LegB : (ℓ : L) → Base ℓ → Set
LegB ℓ B = LN zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → LN j (bs B j w))
```

`kp⁼ a ε ρ p w K d`: 槽位 p 沿目标路径 w 落进目标层时交给 K (目标层里的槽位与分支换型), 否则是 d.

```agda
record Iface : Set₁ where
  field
    ψ⊥ : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → Tr ℓ → Tr zero
    ψs : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr j → Tr ℓ → Tr j
    kp⁼ : (a : L) (ε : Ev a) (ρ : Rt a) (p : Pos⁼ a) {j : L} (w : j ≤ a) {X : Set}
        → ((q : Pos j) → (Br j q → Br⁼ a p) → X) → X → X

  dS : (a : L) → Ev (suc a) → Rt (suc a) → Base (suc a) → Tr (suc a) → Base a
  dS a ε ρ B x = base (ψ⊥ (suc a) ε ρ B x) (λ j w → ψs (suc a) ε ρ B j (ins w) (bs B j (ins w)) x)

  dL : (g : ℕ → L) → Ev (lim g) → Rt (lim g) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
  dL g ε ρ B n x = base (ψ⊥ (lim g) ε ρ B x) (λ j w → ψs (lim g) ε ρ B j (inl n w) (bs B j (inl n w)) x)

  dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Rt (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
  dW k h ε ρ B c x = base (ψ⊥ (Ωₗ k h) ε ρ B x) (λ j w → ψs (Ωₗ k h) ε ρ B j (inb c w) (bs B j (inb c w)) x)

  field
```

## 照 `YiUpIface` 的各条 (多传 `Rt`)

```agda
    J2-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) (j : L) (w : j ≤ a) (β : Tr j)
      (x : Tr (suc a)) (y : Tr a)
      → ψs (suc a) ε ρ B j (ins w) β (up x tt y)
      ≡ ψs a ε ρ (dS a ε ρ B x) j w (ψs (suc a) ε ρ B j (ins w) β x) y
    J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n)
      (β : Tr j) (x : Tr (lim g)) (y : Tr (g n))
      → ψs (lim g) ε ρ B j (inl n w) β (up x n y)
      ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w (ψs (lim g) ε ρ B j (inl n w) β x) y
    J2-limu : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (j : L)
      (ws : (n : ℕ) → j ≤ g n) (β : Tr j) (x : Tr (lim g)) (n : ℕ) (y : Tr (g n))
      → ψs (lim g) ε ρ B j (inlu ws) β (up x n y)
      ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j (ws n) (ψs (lim g) ε ρ B j (inlu ws) β x) y
    J2-Ωk : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
      (w : j ≤ k) (β : Tr j) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
      → ψs (Ωₗ k h) ε ρ B j (ink w) β (up x c y)
      ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (w ∙ proj₁ (proj₂ ε c))
          (ψs (Ωₗ k h) ε ρ B j (ink w) β x) y
    J2-Ωu : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
      (ws : (c : Tr k) → j ≤ h c) (β : Tr j) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
      → ψs (Ωₗ k h) ε ρ B j (inu ws) β (up x c y)
      ≡ ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) j (ws c)
          (ψs (Ωₗ k h) ε ρ B j (inu ws) β x) y
    J2⊥-suc : (a : L) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) (x : Tr (suc a)) (y : Tr a)
      → ψ⊥ (suc a) ε ρ B (up x tt y) ≡ ψ⊥ a ε ρ (dS a ε ρ B x) y
    J2⊥-lim : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (x : Tr (lim g)) (n : ℕ)
      (y : Tr (g n))
      → ψ⊥ (lim g) ε ρ B (up x n y) ≡ ψ⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) y
    J2⊥-Ω : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (x : Tr (Ωₗ k h))
      (c : Tr k) (y : Tr (h c))
      → ψ⊥ (Ωₗ k h) ε ρ B (up x c y) ≡ ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (dW k h ε ρ B c x) y

    mono⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) {x y : Tr ℓ}
      → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε ρ B x ◃ ψ⊥ ℓ ε ρ B y
    monos : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ}
      → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε ρ B j v β x ◃ ψs ℓ ε ρ B j v β y
    pres⊥ : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → LegB ℓ B → (x : Tr ℓ) → Leg ℓ x
      → LN zero (ψ⊥ ℓ ε ρ B x)
    press : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → LN j β
      → (x : Tr ℓ) → Leg ℓ x → LN j (ψs ℓ ε ρ B j v β x)

    tw-leg : (n : ℕ) → Leg zero (ψ⊥ (tw n) (Ev-tw n) (Rt-tw n) (B₀ (tw n)) (Ωt (tw n)))
    EBO-leg : Leg zero (ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (Ωt Λ))

    kstep : (n : ℕ) (B : Base (tw (suc n))) (β : Tr (tw n)) (x : Tr (tw (suc n)))
      (p : Pos (tw n)) (g : Br (tw n) p → Tr (tw n))
      → ψs (tw (suc n)) (Ev-tw (suc n)) (Rt-tw (suc n)) B (tw n) (ink self) β (up x zero (Ω p g))
      ≡ Ω p (λ z → ψs (tw n) (Ev-tw n) (Rt-tw n)
                     (dW (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ev-tw (suc n)) (Rt-tw (suc n)) B zero x)
                     (tw n) self (ψs (tw (suc n)) (Ev-tw (suc n)) (Rt-tw (suc n)) B (tw n) (ink self) β x) (g z))

    self-up : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (β : Tr ℓ) (x : Tr ℓ) (c : Ch ℓ) (y : ChT ℓ c)
      → ψs ℓ ε ρ B ℓ self β (up x c y) ≡ Upc ℓ c (ψs ℓ ε ρ B ℓ self β x) y

    kall : (n : ℕ) (B : Base (tw (suc n))) (β : Tr (tw n)) (x : Tr (tw (suc n))) (c : Tr (tw n))
      {t : Pos (tw n ⊕ ↑ (tw n) c)} (G : Br (tw n ⊕ ↑ (tw n) c) t → Tr (tw n ⊕ ↑ (tw n) c))
      (i : InB (tw n) (↑ (tw n) c) t) (p : Pos (tw n)) → prE i (evc n c) ≡ inj₂ p
      → Kept p (ψs (tw (suc n)) (Ev-tw (suc n)) (Rt-tw (suc n)) B (tw n) (ink self) β (up x c (Ω t G)))
```

## 结点行与保留判定在 ℕ 极限层号上的三条

结点的折叠是保留判定在 "保留" 与 "链的部分和" 之间的选择. 槽位在孩子 m, 目标在孩子 n:
m < n 且有路径 v : g m ≤ g n 时, 槽位沿 v 搬进孩子 n (`psh`), 在孩子 n 里按路径 w 判定;
m ≥ n 且有路径 v : g n ≤ g m 时, 目标沿 v 搬进孩子 m (`w ∙ v`), 在孩子 m 里判定; 没有路径时不保留.

```agda
    node : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j)
      (p : Pos ℓ) (G : Br ℓ p → Tr ℓ)
      → ψs ℓ ε ρ B j w β (Ω p G)
      ≡ kp⁼ ℓ ε ρ (inj₂ p) w (λ q cv → Ω q (λ z → ψs ℓ ε ρ B j w β (G (cv z))))
          (lim (cum (λ n → ψs ℓ ε ρ B j w β
            (G (iter (λ z → fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (G z)))
                  (fromBr ℓ p zero) n)))))

    kp-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
      {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g m ≤ g n)
      → way g (proj₂ ρ) m n ≡ fwd v
      → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d
      ≡ kp⁼ (g n) (ε n) (proj₁ ρ n) (psh v p) w (λ q cv → K q (λ z → pshBr v p (cv z))) d
    kp-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
      {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X) (v : g n ≤ g m)
      → way g (proj₂ ρ) m n ≡ bwd v
      → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d ≡ kp⁼ (g m) (ε m) (proj₁ ρ m) p (w ∙ v) K d
    kp-none : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (m n : ℕ) (p : Pos⁼ (g m)) {j : L} (w : j ≤ g n)
      {X : Set} (K : (q : Pos j) → (Br j q → Br⁼ (g m) p) → X) (d : X)
      → way g (proj₂ ρ) m n ≡ none
      → kp⁼ (lim g) ε ρ (inj₂ (m , p)) (inl n w) K d ≡ d
```

## 嵌入在 ℕ 极限层号上的三条

嵌入 `up x m y` 在孩子 m, 目标在孩子 n. m ≥ n 且有路径: 目标搬进孩子 m, 交孩子 m 的折叠, 孩子的底取 `dL … m x`, 当前目标的底是 x 对同一目标的折叠 (J2 的形状).
m < n 且有路径: 孩子树沿路径搬进孩子 n (`emb`), 交孩子 n 的折叠, 底同理. 没有路径: 回退 (孩子以 `B₀` 折到第 0 层再加).

```agda
    J2-lim-bwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
      (w : j ≤ g n) (β : Tr j) (x : Tr (lim g)) (y : Tr (g m)) (v : g n ≤ g m)
      → way g (proj₂ ρ) m n ≡ bwd v
      → ψs (lim g) ε ρ B j (inl n w) β (up x m y)
      ≡ ψs (g m) (ε m) (proj₁ ρ m) (dL g ε ρ B m x) j (w ∙ v) (ψs (lim g) ε ρ B j (inl n w) β x) y
    J2-lim-fwd : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
      (w : j ≤ g n) (β : Tr j) (x : Tr (lim g)) (y : Tr (g m)) (v : g m ≤ g n)
      → way g (proj₂ ρ) m n ≡ fwd v
      → ψs (lim g) ε ρ B j (inl n w) β (up x m y)
      ≡ ψs (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) j w (ψs (lim g) ε ρ B j (inl n w) β x)
          (emb (g n) (ε n) v y)
    J2-lim-none : (g : ℕ → L) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (m n : ℕ) (j : L)
      (w : j ≤ g n) (β : Tr j) (x : Tr (lim g)) (y : Tr (g m))
      → way g (proj₂ ρ) m n ≡ none
      → ψs (lim g) ε ρ B j (inl n w) β (up x m y)
      ≡ ψs (lim g) ε ρ B j (inl n w) β x + ι j (ψ⊥ (g m) (ε m) (proj₁ ρ m) (B₀ (g m)) y)
```
