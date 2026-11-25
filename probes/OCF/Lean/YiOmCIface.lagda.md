# 留在孩子里, 底依赖左边: 接口

> 判决: 接口 (只陈述). 字段照 `YiUpIface.Iface`, 三处不同: 单调 `monos` 带前提 `NZB` (底的每个分量非零); 自身行按层号分三条 (`self-suc`, `self-lim` 是上折 `U`, `self-Ω` 把孩子留在孩子里, 孩子的底是 x 折进孩子层的值); 上折 `U` 是接口的字段, 它在 Ω 结点层号的 `up` 上的行为另列 (`U-Ω`).
> 实填在 `YiOmCCheck.omI` (对一切带证据的层号).
> 不否定什么. `YiUpIface.self-up` 在 Ω 结点层号上不成立于本接口的实填 (两边的头不同: `up` 对上折的输出), 这里不陈述.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOmCIface where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; Leg; LN)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiPhiNegK using (InB; prE; evc; Kept)
open import OCF.Lean.YiUpBlock using (Dn; stop; down)
open import OCF.Lean.YiOmCFold using (embD)
```

底合法: 每个分量合法且非零.

```agda
LegB : (ℓ : L) → Base ℓ → Set
LegB ℓ B = LN zero (b⊥ B) × ((j : L) (w : j ≤ ℓ) → LN j (bs B j w))

NZB : (ℓ : L) → Base ℓ → Set
NZB ℓ B = (j : L) (w : j ≤ ℓ) → j ⊢ zero ◃ bs B j w
```

`ψs ℓ ε B j w β x`: 第 ℓ 层的树 x 折到目标 j (路径 w), β 是偏移对这个目标的折叠 (x = 0 时的值).
孩子的底 `dS`, `dL`, `dW` 由折叠本身给出.

```agda
record Iface : Set where
  field
    ψ⊥ : (ℓ : L) → Ev ℓ → Base ℓ → Tr ℓ → Tr zero
    ψs : (ℓ : L) → Ev ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr j → Tr ℓ → Tr j
    U  : ∀ {ℓ} (j : L) → Ev j → Dn ℓ j → Tr ℓ → Tr j → Tr ℓ

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

折叠对第一位置序单调 (到第 0 层无前提; 到目标 j 要底的每个分量非零), 保持 "合法且非零" (底合法且非零).

```agda
    mono⊥ : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) {x y : Tr ℓ}
      → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε B x ◃ ψ⊥ ℓ ε B y
    monos : (ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → NZB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ}
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

自身行. 后继与 ℕ 极限层号: 孩子树上折进本层 (`U`), 底是 x 对自身的折叠. Ω 结点层号: 孩子树留在孩子 c 里, 在孩子层折到自身;
孩子的底记录是 `dW` (与 J2 各行相同), 当前目标的底是 x 折进孩子层 h c 的值 (路径 `inb c self`). 对一切 c 同一条, 不比较 c.

```agda
    self-suc : (a : L) (ε : Ev (suc a)) (B : Base (suc a)) (β x : Tr (suc a)) (y : Tr a)
      → ψs (suc a) ε B (suc a) self β (up x tt y) ≡ U a ε (down stop tt) (ψs (suc a) ε B (suc a) self β x) y
    self-lim : (g : ℕ → L) (ε : Ev (lim g)) (B : Base (lim g)) (β x : Tr (lim g)) (n : ℕ) (y : Tr (g n))
      → ψs (lim g) ε B (lim g) self β (up x n y) ≡ U (g n) (ε n) (down stop n) (ψs (lim g) ε B (lim g) self β x) y
    self-Ω : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) (β x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
      → ψs (Ωₗ k h) ε B (Ωₗ k h) self β (up x c y)
      ≡ up (ψs (Ωₗ k h) ε B (Ωₗ k h) self β x) c
           (ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) (h c) self
              (ψs (Ωₗ k h) ε B (h c) (inb c self) (bs B (h c) (inb c self)) x) y)
```

上折走到 Ω 结点层号孩子里的 `up`: 不再上折, 孩子树在孩子层折到自身 (底取 `B₀`), 沿下行链加法地嵌回.

```agda
    U-Ω : ∀ {ℓ} (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (d : Dn ℓ (Ωₗ k h)) (b : Tr ℓ)
      (y : Tr (Ωₗ k h)) (c : Tr k) (y′ : Tr (h c))
      → U (Ωₗ k h) ε d b (up y c y′)
      ≡ embD d (U (Ωₗ k h) ε d b y)
          (up zero c (ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε (B₀ (Ωₗ k h)) c y) (h c) self
                        (ψs (Ωₗ k h) ε (B₀ (Ωₗ k h)) (h c) (inb c self) (Ωt (h c)) y) y′))
```

只增字段: `kstep` 对一切孩子 c 的加强 (`YiPhiNegK.KAll` 的陈述).

```agda
    kall : (n : ℕ) (B : Base (tw (suc n))) (β : Tr (tw n)) (x : Tr (tw (suc n))) (c : Tr (tw n))
      {t : Pos (tw n ⊕ ↑ (tw n) c)} (G : Br (tw n ⊕ ↑ (tw n) c) t → Tr (tw n ⊕ ↑ (tw n) c))
      (i : InB (tw n) (↑ (tw n) c) t) (p : Pos (tw n)) → prE i (evc n c) ≡ inj₂ p
      → Kept p (ψs (tw (suc n)) (Ev-tw (suc n)) B (tw n) (ink self) β (up x c (Ω t G)))
```
