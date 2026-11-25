# ℕ 极限层号的路线: 折叠

> 判决: 成品候选 (折叠). 与 `YiUpFold` 不同的只有 ℕ 极限层号上 "目标在孩子 n, 结点或嵌入在孩子 m" 的两行: 按 `Way` 分情形, 有路径时搬到编号较大的那个孩子再处理.
> 结点: m < n 时槽位沿路径搬进孩子 n (`psh`), m ≥ n 时目标沿路径搬进孩子 m (`∙`; 同号时路径是 `self`). 嵌入: m ≥ n 时目标搬进孩子 m, 交孩子层折叠, 底是 x 对同一目标的折叠 (J2 的形状); m < n 时孩子树搬进孩子 n (`emb`) 再交孩子层折叠.
> 不否定什么. 没有路径 (`none`) 时两行照 `YiUpFold`: 结点走默认, 嵌入走回退. 其余各行逐字相同, 只多传一个 `Rt`. 合法性在 `YiLimLegal`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLimFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiLimBlock
```

## 保留判定

`YiPhiFold.kp` 加一个 `Rt` 参数; 只有 `(lim g, (m , p), inl n w)` 一行不同.

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
      d
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
```

## 折叠

```agda
mutual
  ψ⊥ : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → Tr ℓ → Tr zero
  ψ⊥ ℓ ε ρ B zero    = b⊥ B
  ψ⊥ ℓ ε ρ B (suc x) = next (ψ⊥ ℓ ε ρ B x)
  ψ⊥ ℓ ε ρ B (lim f) = lim (λ n → ψ⊥ ℓ ε ρ B (f n))
  ψ⊥ ℓ ε ρ B (Ω p g) = lim (cum (λ n → ψ⊥ ℓ ε ρ B (g (iter step (fromBr ℓ p zero) n))))
    where
    step : Br ℓ p → Br ℓ p
    step z = fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (g z))
  ψ⊥ (suc a)  ε ρ B (up x _ y) =
    ψ⊥ a ε ρ (base (ψ⊥ (suc a) ε ρ B x) (λ j w → ψs (suc a) ε ρ B j (ins w) (bs B j (ins w)) x)) y
  ψ⊥ (lim g)  ε ρ B (up x n y) =
    ψ⊥ (g n) (ε n) (proj₁ ρ n)
      (base (ψ⊥ (lim g) ε ρ B x) (λ j w → ψs (lim g) ε ρ B j (inl n w) (bs B j (inl n w)) x)) y
  ψ⊥ (Ωₗ k h) ε ρ B (up x c y) =
    ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (base (ψ⊥ (Ωₗ k h) ε ρ B x) (λ j w → ψs (Ωₗ k h) ε ρ B j (inb c w) (bs B j (inb c w)) x)) y
  ψ⊥ zero     ε ρ B (up x () y)

  ψs : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr j → Tr ℓ → Tr j
  ψs ℓ ε ρ B j w β zero    = β
  ψs ℓ ε ρ B j w β (suc x) = next (ψs ℓ ε ρ B j w β x)
  ψs ℓ ε ρ B j w β (lim f) = lim (λ n → ψs ℓ ε ρ B j w β (f n))
  ψs ℓ ε ρ B j w β (Ω p g) =
    kp ℓ ε ρ p w (λ q cv → Ω q (λ z → ψs ℓ ε ρ B j w β (g (cv z))))
                 (lim (cum (λ n → ψs ℓ ε ρ B j w β (g (iter step (fromBr ℓ p zero) n)))))
    where
    step : Br ℓ p → Br ℓ p
    step z = fromBr ℓ p (ψs ℓ ε ρ B (at ℓ p) (posW ℓ p) (bs B (at ℓ p) (posW ℓ p)) (g z))
  ψs ℓ ε ρ B _ self β (up x c y) = Upc ℓ c (ψs ℓ ε ρ B ℓ self β x) y
  ψs (suc a) ε ρ B j (ins w) β (up x _ y) =
    ψs a ε ρ (base (ψ⊥ (suc a) ε ρ B x) (λ j′ w′ → ψs (suc a) ε ρ B j′ (ins w′) (bs B j′ (ins w′)) x))
      j w (ψs (suc a) ε ρ B j (ins w) β x) y
  ψs (lim g) ε (ρc , R) B j (inl n w) β (up x m y) =
    caseW (way g R m n)
      (λ v → ψs (g n) (ε n) (ρc n)
        (base (ψ⊥ (lim g) ε (ρc , R) B x) (λ j′ w′ → ψs (lim g) ε (ρc , R) B j′ (inl n w′) (bs B j′ (inl n w′)) x))
        j w (ψs (lim g) ε (ρc , R) B j (inl n w) β x) (emb (g n) (ε n) v y))
      (λ v → ψs (g m) (ε m) (ρc m)
        (base (ψ⊥ (lim g) ε (ρc , R) B x) (λ j′ w′ → ψs (lim g) ε (ρc , R) B j′ (inl m w′) (bs B j′ (inl m w′)) x))
        j (w ∙ v) (ψs (lim g) ε (ρc , R) B j (inl n w) β x) y)
      (ψs (lim g) ε (ρc , R) B j (inl n w) β x + ι j (ψ⊥ (g m) (ε m) (ρc m) (B₀ (g m)) y))
  ψs (lim g) ε ρ B j (inlu ws) β (up x m y) =
    ψs (g m) (ε m) (proj₁ ρ m)
      (base (ψ⊥ (lim g) ε ρ B x) (λ j′ w′ → ψs (lim g) ε ρ B j′ (inl m w′) (bs B j′ (inl m w′)) x))
      j (ws m) (ψs (lim g) ε ρ B j (inlu ws) β x) y
  ψs (Ωₗ k h) ε ρ B j (ink w) β (up x c y) =
    ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (base (ψ⊥ (Ωₗ k h) ε ρ B x) (λ j′ w′ → ψs (Ωₗ k h) ε ρ B j′ (inb c w′) (bs B j′ (inb c w′)) x))
      j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε ρ B j (ink w) β x) y
  ψs (Ωₗ k h) ε ρ B j (inu ws) β (up x c y) =
    ψs (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c)
      (base (ψ⊥ (Ωₗ k h) ε ρ B x) (λ j′ w′ → ψs (Ωₗ k h) ε ρ B j′ (inb c w′) (bs B j′ (inb c w′)) x))
      j (ws c) (ψs (Ωₗ k h) ε ρ B j (inu ws) β x) y
  ψs (Ωₗ k h) ε ρ B j (inb c′ w) β (up x c y) =
    ψs (Ωₗ k h) ε ρ B j (inb c′ w) β x + ι j (ψ⊥ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) (B₀ (h c)) y)

ψ₀ : (ℓ : L) → Ev ℓ → Rt ℓ → Tr ℓ → Tr zero
ψ₀ ℓ ε ρ = ψ⊥ ℓ ε ρ (B₀ ℓ)
```
