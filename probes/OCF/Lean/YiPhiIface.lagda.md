# φ 并进折叠: 接口

> 判决: 接口 (只陈述). 记录 `Iface` 的字段是两个折叠与它们的律; 律里的目标都带路径 j ≤ ℓ (字面公共上界), `J2-Ωk` 里的分支 c 是变量.
> 路径, 层号证据 `Ev`, 底 `Base` 取自 `YiPhiBlock`; 序与合法性取自 `YiFreshLegal` (块没有改). 实填在 `YiPhiCheck.phi`.
> 不否定什么. 定稿后只增不改; 配对的否定对这一记录写.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiIface where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; Leg; LN)
open import OCF.Lean.YiPhiBlock
```

底合法: 每个分量合法且非零.

```agda
LegB : (ℓ : L) → Base ℓ → Set
LegB ℓ B = LN zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → LN j (bs B j w))
```

`ψs ℓ ε B j w β x`: 第 ℓ 层的树 x 折到目标 j (路径 w), β 是偏移对这个目标的折叠 (x = 0 时的值).
孩子的底 `dS`, `dL`, `dW` 由折叠本身给出.

```agda
record Iface : Set where
  field
    ψ⊥ : (ℓ : L) → Ev ℓ → Base ℓ → Tr ℓ → Tr zero
    ψs : (ℓ : L) → Ev ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr j → Tr ℓ → Tr j

  dS : (a : L) → Ev (suc a) → Base (suc a) → Tr (suc a) → Base a
  dS a ε B x = base (ψ⊥ (suc a) ε B x) (λ j w → ψs (suc a) ε B j (ins w) (bs B j (ins w)) x)

  dL : (g : ℕ → L) → Ev (lim g) → Base (lim g) → (n : ℕ) → Tr (lim g) → Base (g n)
  dL g ε B n x = base (ψ⊥ (lim g) ε B x) (λ j w → ψs (lim g) ε B j (inl n w) (bs B j (inl n w)) x)

  dW : (k : L) (h : Tr k → L) → Ev (Ωₗ k h) → Base (Ωₗ k h) → (c : Tr k) → Tr (Ωₗ k h) → Base (h c)
  dW k h ε B c x = base (ψ⊥ (Ωₗ k h) ε B x) (λ j w → ψs (Ωₗ k h) ε B j (inb c w) (bs B j (inb c w)) x)

  field
```

嵌入一致: 后继, ℕ 极限 (指定孩子与对一切孩子), 到第 0 层, 以及 `Ωₗ` 的 k 侧与 "对一切孩子" 的目标. 后两条对一切分支 c, 不比较 c.

```agda
    J2-suc : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) (j : L) (w : j ≤ a) (β : Tr j)
      (x : Tr (suc a)) (y : Tr a)
      → ψs (suc a) ε B j (ins w) β (up x tt y)
      ≡ ψs a ε (dS a ε B x) j w (ψs (suc a) ε B j (ins w) β x) y
    J2-lim : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (n : ℕ) (j : L) (w : j ≤ g n) (β : Tr j)
      (x : Tr (lim g)) (y : Tr (g n))
      → ψs (lim g) ε B j (inl n w) β (up x n y)
      ≡ ψs (g n) (ε n) (dL g ε B n x) j w (ψs (lim g) ε B j (inl n w) β x) y
    J2-limu : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (j : L) (ws : (n : ℕ) → j ≤ g n) (β : Tr j)
      (x : Tr (lim g)) (n : ℕ) (y : Tr (g n))
      → ψs (lim g) ε B j (inlu ws) β (up x n y)
      ≡ ψs (g n) (ε n) (dL g ε B n x) j (ws n) (ψs (lim g) ε B j (inlu ws) β x) y
    J2-Ωk : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L) (w : j ≤ k) (β : Tr j)
      (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
      → ψs (Ωₗ k h) ε B j (ink w) β (up x c y)
      ≡ ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (w ∙ proj₁ (proj₂ ε c))
          (ψs (Ωₗ k h) ε B j (ink w) β x) y
    J2-Ωu : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
      (ws : (c : Tr k) → j ≤ h c) (β : Tr j) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
      → ψs (Ωₗ k h) ε B j (inu ws) β (up x c y)
      ≡ ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (ws c) (ψs (Ωₗ k h) ε B j (inu ws) β x) y
    J2⊥-suc : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) (x : Tr (suc a)) (y : Tr a)
      → ψ⊥ (suc a) ε B (up x tt y) ≡ ψ⊥ a ε (dS a ε B x) y
    J2⊥-lim : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (x : Tr (lim g)) (n : ℕ) (y : Tr (g n))
      → ψ⊥ (lim g) ε B (up x n y) ≡ ψ⊥ (g n) (ε n) (dL g ε B n x) y
    J2⊥-Ω : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (x : Tr (Ωₗ k h))
      (c : Tr k) (y : Tr (h c))
      → ψ⊥ (Ωₗ k h) ε B (up x c y) ≡ ψ⊥ (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) y
```

折叠对第一位置序单调 (无前提), 保持 "合法且非零" (底合法且非零).

```agda
    mono⊥ : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) {x y : Tr ℓ}
      → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε B x ◃ ψ⊥ ℓ ε B y
    monos : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ}
      → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε B j v β x ◃ ψs ℓ ε B j v β y
    pres⊥ : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (x : Tr ℓ) → Leg ℓ x → LN zero (ψ⊥ ℓ ε B x)
    press : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → LN j β
      → (x : Tr ℓ) → Leg ℓ x → LN j (ψs ℓ ε B j v β x)
```

闭项合法: 塔各项与 Λ 的 Ω 树折到第 0 层 (后者是读法 ψ₀(Λ) 的闭项).

```agda
    tw-leg : (n : ℕ) → Leg zero (ψ⊥ (tw n) (Ev-tw n) (B₀ (tw n)) (Ωt (tw n)))
    EBO-leg : Leg zero (ψ⊥ Λ Ev-Λ (B₀ Λ) (Ωt Λ))
```

k 侧链步保留基底里的结点: 塔第 n+1 项, 目标是下标层 tw n, 嵌入在第一个孩子 (层号 tw n ⊕ 0) 里的 Ω 结点原样保留, 分支继续折.

```agda
    kstep : (n : ℕ) (B : Base (tw (suc n))) (β : Tr (tw n)) (x : Tr (tw (suc n)))
      (p : Pos (tw n)) (g : Br (tw n) p → Tr (tw n))
      → ψs (tw (suc n)) (Ev-tw (suc n)) B (tw n) (ink self) β (up x zero (Ω p g))
      ≡ Ω p (λ z → ψs (tw n) (Ev-tw n) (dW (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ev-tw (suc n)) B zero x)
                     (tw n) self (ψs (tw (suc n)) (Ev-tw (suc n)) B (tw n) (ink self) β x) (g z))
```
