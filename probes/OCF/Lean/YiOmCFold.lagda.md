# 留在孩子里, 底依赖左边: 折叠

> 判决: 成品候选 (折叠), 记作 (C′). 与 `YiUpFold` 不同在 Ω 结点层号的自身行: `up x c y` 的输出是 `up X c (kid … c x y)`, X 是 x 对自身的折叠, 孩子 y 在孩子层折到自身 (`kid`), 底是 x 折进孩子层 h c 的值 (路径 `inb c self`, 偏移取底 B 的对应分量).
> 后继与 ℕ 极限层号的自身行仍上折 (`Up′`); 上折走到 Ω 结点层号孩子里的 `up` 时沿下行链加法地重新嵌入 (`embD`), 那里的底取 `B₀`.
> 不否定什么. 不比较孩子下标. 合法性在 `YiOmCLegal`; 常量底的对照 (C) 在 `YiOmCConst`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOmCFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ; eqℕ-refl)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiFold using (kp; kp⁼)
open import OCF.Lean.YiUpBlock using (chP; chBr; Dn; stop; down; mv; mvBr)
```

## 重新嵌入

`unT` 是 `chT` 的逆 (恒等); `embD d x t` 沿下行链把 j 层的树 t 嵌回 ℓ 层, 读作 x + ↑t.

```agda
unT : (j : L) (c : Ch j) → Tr (chL j c) → ChT j c
unT (suc a)  _ y = y
unT (lim g)  n y = y
unT (Ωₗ k h) c y = y

embD : ∀ {ℓ j} → Dn ℓ j → Tr ℓ → Tr j → Tr ℓ
embD stop           x t = x + t
embD (down {j} d c) x t = embD d x (up zero c (unT j c t))
```

## 折叠

`kid k h ε B c x y`: 孩子树 y 在孩子层 h c 折到自身. 孩子的底记录与 J2 各行相同 (x 对各目标的折叠); 当前目标的底是 x 折进 h c 的值.

```agda
mutual
  Up′ : ∀ {ℓ} (j : L) → Ev j → Dn ℓ j → Tr ℓ → Tr j → Tr ℓ
  Up′ j        ε d b zero    = b
  Up′ j        ε d b (suc y) = next (Up′ j ε d b y)
  Up′ j        ε d b (lim f) = lim (λ n → Up′ j ε d b (f n))
  Up′ j        ε d b (Ω p g) = Ω (mv d p) (λ z → Up′ j ε d b (g (mvBr d p z)))
  Up′ (suc a)  ε d b (up y _ y′) = Up′ a ε (down d tt) (Up′ (suc a) ε d b y) y′
  Up′ (lim g)  ε d b (up y n y′) = Up′ (g n) (ε n) (down d n) (Up′ (lim g) ε d b y) y′
  Up′ (Ωₗ k h) ε d b (up y c y′) =
    embD d (Up′ (Ωₗ k h) ε d b y) (up zero c (kid k h ε (B₀ (Ωₗ k h)) c y y′))
  Up′ zero     ε d b (up y () _)

  kid : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Tr (h c) → Tr (h c)
  kid k h ε B c x y =
    ψs (h c) (proj₂ (proj₂ ε c))
      (base (ψ⊥ (Ωₗ k h) ε B x) (λ j w → ψs (Ωₗ k h) ε B j (inb c w) (bs B j (inb c w)) x))
      (h c) self (ψs (Ωₗ k h) ε B (h c) (inb c self) (bs B (h c) (inb c self)) x) y

  ψ⊥ : (ℓ : L) → Ev ℓ → Base ℓ → Tr ℓ → Tr zero
  ψ⊥ ℓ ε B zero    = b⊥ B
  ψ⊥ ℓ ε B (suc x) = next (ψ⊥ ℓ ε B x)
  ψ⊥ ℓ ε B (lim f) = lim (λ n → ψ⊥ ℓ ε B (f n))
  ψ⊥ ℓ ε B (Ω p g) = lim (cum (λ n → ψ⊥ ℓ ε B (g (iter step (fromBr ℓ p zero) n))))
    where
    step : Br ℓ p → Br ℓ p
    step z = fromBr ℓ p (ψs ℓ ε B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (g z))
  ψ⊥ (suc a)  ε B (up x _ y) =
    ψ⊥ a ε (base (ψ⊥ (suc a) ε B x) (λ j w → ψs (suc a) ε B j (ins w) (bs B j (ins w)) x)) y
  ψ⊥ (lim g)  ε B (up x n y) =
    ψ⊥ (g n) (ε n) (base (ψ⊥ (lim g) ε B x) (λ j w → ψs (lim g) ε B j (inl n w) (bs B j (inl n w)) x)) y
  ψ⊥ (Ωₗ k h) ε B (up x c y) =
    ψ⊥ (h c) (proj₂ (proj₂ ε c))
      (base (ψ⊥ (Ωₗ k h) ε B x) (λ j w → ψs (Ωₗ k h) ε B j (inb c w) (bs B j (inb c w)) x)) y
  ψ⊥ zero     ε B (up x () y)

  ψs : (ℓ : L) → Ev ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr j → Tr ℓ → Tr j
  ψs ℓ ε B j w β zero    = β
  ψs ℓ ε B j w β (suc x) = next (ψs ℓ ε B j w β x)
  ψs ℓ ε B j w β (lim f) = lim (λ n → ψs ℓ ε B j w β (f n))
  ψs ℓ ε B j w β (Ω p g) =
    kp ℓ ε p w (λ q cv → Ω q (λ z → ψs ℓ ε B j w β (g (cv z))))
               (lim (cum (λ n → ψs ℓ ε B j w β (g (iter step (fromBr ℓ p zero) n)))))
    where
    step : Br ℓ p → Br ℓ p
    step z = fromBr ℓ p (ψs ℓ ε B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (g z))
  ψs (suc a)  ε B _ self β (up x _ y) = Up′ a ε (down stop tt) (ψs (suc a) ε B (suc a) self β x) y
  ψs (lim g)  ε B _ self β (up x n y) = Up′ (g n) (ε n) (down stop n) (ψs (lim g) ε B (lim g) self β x) y
  ψs (Ωₗ k h) ε B _ self β (up x c y) =
    up (ψs (Ωₗ k h) ε B (Ωₗ k h) self β x) c (kid k h ε B c x y)
  ψs zero     ε B _ self β (up x () y)
  ψs (suc a) ε B j (ins w) β (up x _ y) =
    ψs a ε (base (ψ⊥ (suc a) ε B x) (λ j′ w′ → ψs (suc a) ε B j′ (ins w′) (bs B j′ (ins w′)) x))
      j w (ψs (suc a) ε B j (ins w) β x) y
  ψs (lim g) ε B j (inl n w) β (up x m y) with eqℕ m n
  ... | just refl =
    ψs (g m) (ε m) (base (ψ⊥ (lim g) ε B x) (λ j′ w′ → ψs (lim g) ε B j′ (inl m w′) (bs B j′ (inl m w′)) x))
      j w (ψs (lim g) ε B j (inl m w) β x) y
  ... | nothing   = ψs (lim g) ε B j (inl n w) β x + ι j (ψ⊥ (g m) (ε m) (B₀ (g m)) y)
  ψs (lim g) ε B j (inlu ws) β (up x m y) =
    ψs (g m) (ε m) (base (ψ⊥ (lim g) ε B x) (λ j′ w′ → ψs (lim g) ε B j′ (inl m w′) (bs B j′ (inl m w′)) x))
      j (ws m) (ψs (lim g) ε B j (inlu ws) β x) y
  ψs (Ωₗ k h) ε B j (ink w) β (up x c y) =
    ψs (h c) (proj₂ (proj₂ ε c))
      (base (ψ⊥ (Ωₗ k h) ε B x) (λ j′ w′ → ψs (Ωₗ k h) ε B j′ (inb c w′) (bs B j′ (inb c w′)) x))
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε B j (ink w) β x) y
  ψs (Ωₗ k h) ε B j (inu ws) β (up x c y) =
    ψs (h c) (proj₂ (proj₂ ε c))
      (base (ψ⊥ (Ωₗ k h) ε B x) (λ j′ w′ → ψs (Ωₗ k h) ε B j′ (inb c w′) (bs B j′ (inb c w′)) x))
      j (ws c) (ψs (Ωₗ k h) ε B j (inu ws) β x) y
  ψs (Ωₗ k h) ε B j (inb c′ w) β (up x c y) =
    ψs (Ωₗ k h) ε B j (inb c′ w) β x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (B₀ (h c)) y)

ψ₀ : (ℓ : L) → Ev ℓ → Tr ℓ → Tr zero
ψ₀ ℓ ε = ψ⊥ ℓ ε (B₀ ℓ)
```
