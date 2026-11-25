# φ 并进折叠: 折叠

> 判决: 成品候选 (折叠). `Ωₗ k h` 层的 k 侧目标遇到嵌入分支 `up x c y` 时, 沿证据路径 k ≤ h c 交给孩子层的折叠, 底是 x 对同一目标的折叠; 对一切 c 同一行, 不比较 c.
> 保留判定 `kp` 同样沿证据路径走: 槽位在孩子里而目标在 k 侧, 或槽位在 k 侧而目标在孩子里, 都先搬到同一个孩子层再比路径.
> 不否定什么. 仍有的退让 (判断): 目标在分支 c′ 而嵌入在分支 c 的那一行照旧回退; 孩子的底 `bs` 仍经 `inb c` 取.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι; eqℕ; eqℕ-refl)
open import OCF.Lean.YiPhiBlock
```

## 保留判定

对层号 ℓ 递归 (路径 `w ∙ e` 不比 `ink w` 小, 层号 h c 比 `Ωₗ k h` 小).
`Ωₗ` 的六行: 槽位与目标同在 k 侧, 在 k 里比; 一个在 k 侧一个在孩子里, 把 k 侧的那个沿证据路径搬进那个孩子 (槽位用 `psh`, 目标用 `∙`); 目标对一切孩子给出, 取槽位所在的孩子 (槽位在 k 侧时取第一个孩子); 槽位与目标在两个指定的孩子里, 不比较, 走默认.

```agda
mutual
  kp : (ℓ : L) (ε : Ev ℓ) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) {X : Set}
     → ((q : Pos j) → (Br j q → Br ℓ p) → X) → X → X
  kp ℓ        ε p        self      K d = K p (λ z → z)
  kp (suc a)  ε p        (ins w)   K d = kp⁼ a ε p w K d
  kp (lim g)  ε (m , p)  (inl n w) K d with eqℕ m n
  ... | just refl = kp⁼ (g m) (ε m) p w K d
  ... | nothing   = d
  kp (lim g)  ε (m , p)  (inlu ws) K d = kp⁼ (g m) (ε m) p (ws m) K d
  kp (Ωₗ k h) (ek , e) (inj₁ t)       (ink w)    K d = kp⁼ k ek t w K d
  kp (Ωₗ k h) (ek , e) (inj₁ t)       (inb c w)  K d =
    kp⁼ (h c) (proj₂ (e c)) (psh (proj₁ (e c)) t) w
      (λ q cv → K q (λ z → pshBr (proj₁ (e c)) t (cv z))) d
  kp (Ωₗ k h) (ek , e) (inj₁ t)       (inu ws)   K d =
    kp⁼ (h zero) (proj₂ (e zero)) (psh (proj₁ (e zero)) t) (ws zero)
      (λ q cv → K q (λ z → pshBr (proj₁ (e zero)) t (cv z))) d
  kp (Ωₗ k h) (ek , e) (inj₂ (c , t)) (ink w)    K d = kp⁼ (h c) (proj₂ (e c)) t (w ∙ proj₁ (e c)) K d
  kp (Ωₗ k h) (ek , e) (inj₂ (c , t)) (inu ws)   K d = kp⁼ (h c) (proj₂ (e c)) t (ws c) K d
  kp (Ωₗ k h) (ek , e) (inj₂ (c , t)) (inb c′ w) K d = d

  kp⁼ : (a : L) (ε : Ev a) (p : Pos⁼ a) {j : L} (w : j ≤ a) {X : Set}
      → ((q : Pos j) → (Br j q → Br⁼ a p) → X) → X → X
  kp⁼ a ε (inj₁ _) w K d = d
  kp⁼ a ε (inj₂ p) w K d = kp a ε p w K d
```

## 折叠

`ψs ℓ ε B j w β x`: β 是偏移对当前目标的折叠. 结点: 保留, 或沿结点自己的层做链, 取部分和的极限 (与 `YiFreshFold` 同式).
`up x c y`: 目标是 ℓ 自身则原样保留; 目标经孩子 c 可达 (`ins`, 同号的 `inl`, `inlu`, `ink` 经证据路径, `inu`) 则交孩子层折叠, 底是 x 对同一目标的折叠; 其余 (不同号的 `inl`, `inb`) 回退.

```agda
mutual
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
  ψs ℓ ε B _ self β (up x c y) = up (ψs ℓ ε B ℓ self β x) c y
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
