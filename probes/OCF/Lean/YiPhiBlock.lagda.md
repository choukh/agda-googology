# φ 并进折叠: 目标路径与层号证据

> 判决: 成品候选 (块的增量). 块 `L`, `Tr` 不改 (`YiFreshBlock`); 新增带 "对一切孩子" 的目标路径 `_≤_` (`inlu`, `inu`) 与层号证据 `Ev`: `Ωₗ k h` 的每个孩子层 h c 带一条路径 k ≤ h c.
> 塔与 Λ 的证据 `Ev-tw`, `Ev-Λ` 是闭项, 无前提; 基底到 "基底加偏移" 的路径 `lift a b : a ≤ a ⊕ b` 在 `Ωₗ` 处对一切分支给出, 不比较分支.
> 不否定什么. `Ev` 不是对一切层号可满足的 (量化域是带证据的层号). 折叠在 `YiPhiFold`, 合法性在 `YiPhiLegal`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPhiBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshFold using (Ωt)
```

## 目标路径

`inlu`, `inu` 是对一切孩子各给一条路径的目标; 嵌入分支 `up x c y` 遇到它时交给孩子 c, 不看 c 是谁.

```agda
infix 4 _≤_
data _≤_ : L → L → Set where
  self : ∀ {ℓ} → ℓ ≤ ℓ
  ins  : ∀ {j a} → j ≤ a → j ≤ suc a
  inl  : ∀ {j g} (n : ℕ) → j ≤ g n → j ≤ lim g
  inlu : ∀ {j g} → ((n : ℕ) → j ≤ g n) → j ≤ lim g
  ink  : ∀ {j k h} → j ≤ k → j ≤ Ωₗ k h
  inb  : ∀ {j k h} (c : Tr k) → j ≤ h c → j ≤ Ωₗ k h
  inu  : ∀ {j k h} → ((c : Tr k) → j ≤ h c) → j ≤ Ωₗ k h

infixl 6 _∙_
_∙_ : ∀ {i j ℓ} → i ≤ j → j ≤ ℓ → i ≤ ℓ
w ∙ self     = w
w ∙ ins v    = ins (w ∙ v)
w ∙ inl n v  = inl n (w ∙ v)
w ∙ inlu vs  = inlu (λ n → w ∙ vs n)
w ∙ ink v    = ink (w ∙ v)
w ∙ inb c v  = inb c (w ∙ v)
w ∙ inu vs   = inu (λ c → w ∙ vs c)

lift : (a b : L) → a ≤ a ⊕ b
lift a zero     = self
lift a (suc b)  = ins (lift a b)
lift a (lim g)  = inlu (λ n → lift a (g n))
lift a (Ωₗ k h) = inu (λ c → lift a (h c))

mutual
  posW : (ℓ : L) (p : Pos ℓ) → at ℓ p ≤ ℓ
  posW (suc a)  t              = ins (posW⁼ a t)
  posW (lim g)  (n , t)        = inl n (posW⁼ (g n) t)
  posW (Ωₗ k h) (inj₁ t)       = ink (posW⁼ k t)
  posW (Ωₗ k h) (inj₂ (c , t)) = inb c (posW⁼ (h c) t)

  posW⁼ : (a : L) (t : Pos⁼ a) → at⁼ a t ≤ a
  posW⁼ a (inj₁ _) = self
  posW⁼ a (inj₂ p) = posW a p
```

槽位沿路径推到上层 (`psh`); 分支类型不变 (`pshBr` 每一情形都是恒等). 路径对一切孩子给出时取第一个孩子, 这是取定, 不是比较.

```agda
psh : ∀ {k a} → k ≤ a → Pos⁼ k → Pos⁼ a
psh self      t = t
psh (ins v)   t = inj₂ (psh v t)
psh (inl n v) t = inj₂ (n , psh v t)
psh (inlu vs) t = inj₂ (zero , psh (vs zero) t)
psh (ink v)   t = inj₂ (inj₁ (psh v t))
psh (inb c v) t = inj₂ (inj₂ (c , psh v t))
psh (inu vs)  t = inj₂ (inj₂ (zero , psh (vs zero) t))

pshBr : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → Br⁼ a (psh v t) → Br⁼ k t
pshBr self      t z = z
pshBr (ins v)   t z = pshBr v t z
pshBr (inl n v) t z = pshBr v t z
pshBr (inlu vs) t z = pshBr (vs zero) t z
pshBr (ink v)   t z = pshBr v t z
pshBr (inb c v) t z = pshBr v t z
pshBr (inu vs)  t z = pshBr (vs zero) t z
```

## 层号的证据

`Ev` 只在 `Ωₗ k h` 处有内容: 下标层 k 的证据, 以及每个孩子层 h c 的路径 k ≤ h c 与证据. `EvO a b` 说偏移 b 里的 `Ωₗ` 的下标层都在基底 a 里.

```agda
Ev : L → Set
Ev zero     = ⊤
Ev (suc a)  = Ev a
Ev (lim g)  = (n : ℕ) → Ev (g n)
Ev (Ωₗ k h) = Ev k × ((c : Tr k) → (k ≤ h c) × Ev (h c))

EvO : L → L → Set
EvO a zero     = ⊤
EvO a (suc b)  = EvO a b
EvO a (lim g)  = (n : ℕ) → EvO a (g n)
EvO a (Ωₗ k h) = (k ≤ a) × Ev k × ((c : Tr k) → EvO a (h c))

Ev⊕ : (a b : L) → Ev a → EvO a b → Ev (a ⊕ b)
Ev⊕ a zero     ea eb = ea
Ev⊕ a (suc b)  ea eb = Ev⊕ a b ea eb
Ev⊕ a (lim g)  ea eb = λ n → Ev⊕ a (g n) ea (eb n)
Ev⊕ a (Ωₗ k h) ea (v , ek , eb) = ek , λ c → v ∙ lift a (h c) , Ev⊕ a (h c) ea (eb c)

EvO⊕ : (a b₁ b₂ : L) → EvO a b₁ → EvO a b₂ → EvO a (b₁ ⊕ b₂)
EvO⊕ a b₁ zero     e₁ e₂ = e₁
EvO⊕ a b₁ (suc b)  e₁ e₂ = EvO⊕ a b₁ b e₁ e₂
EvO⊕ a b₁ (lim g)  e₁ e₂ = λ n → EvO⊕ a b₁ (g n) e₁ (e₂ n)
EvO⊕ a b₁ (Ωₗ k h) e₁ (v , ek , e₂) = v , ek , λ c → EvO⊕ a b₁ (h c) e₁ (e₂ c)

mutual
  Ev-at : (ℓ : L) → Ev ℓ → (p : Pos ℓ) → Ev (at ℓ p)
  Ev-at (suc a)  e        t              = Ev-at⁼ a e t
  Ev-at (lim g)  e        (n , t)        = Ev-at⁼ (g n) (e n) t
  Ev-at (Ωₗ k h) (ek , e) (inj₁ t)       = Ev-at⁼ k ek t
  Ev-at (Ωₗ k h) (ek , e) (inj₂ (c , t)) = Ev-at⁼ (h c) (proj₂ (e c)) t

  Ev-at⁼ : (a : L) → Ev a → (t : Pos⁼ a) → Ev (at⁼ a t)
  Ev-at⁼ a e (inj₁ _) = e
  Ev-at⁼ a e (inj₂ p) = Ev-at a e p
```

读回 `↑ k t` 作偏移: 它的 `Ωₗ` 的下标层是 t 的结点的槽位层, 经 `posW` 在 k 里, 再经 v 在基底 a 里. 这里对树 t 递归, 槽位没有丢.

```agda
mutual
  EvO↑ : (a k : L) → Ev k → k ≤ a → (t : Tr k) → EvO a (↑ k t)
  EvO↑ a k ek v zero       = tt
  EvO↑ a k ek v (suc x)    = EvO↑ a k ek v x
  EvO↑ a k ek v (lim f)    = λ n → EvO↑ a k ek v (f n)
  EvO↑ a k ek v (Ω p g)    = posW k p ∙ v , Ev-at k ek p , λ c → EvO↑ a k ek v (g (fromBr k p c))
  EvO↑ a k ek v (up x c y) = EvO⊕ a (↑ k x) (↑ch k c y) (EvO↑ a k ek v x) (EvO↑ch a k ek v c y)

  EvO↑ch : (a k : L) → Ev k → k ≤ a → (c : Ch k) (y : ChT k c) → EvO a (↑ch k c y)
  EvO↑ch a (suc k)  ek       v _ y = EvO↑ a k ek (ins self ∙ v) y
  EvO↑ch a (lim g)  ek       v n y = EvO↑ a (g n) (ek n) (inl n self ∙ v) y
  EvO↑ch a (Ωₗ k h) (_ , ek) v c y = EvO↑ a (h c) (proj₂ (ek c)) (inb c self ∙ v) y
```

塔与 Λ 的证据 (闭项). 第 n+1 项的孩子层是 tw n ⊕ ↑c, 路径是 `lift`.

```agda
Ev-tw : (n : ℕ) → Ev (tw n)
Ev-tw zero    = tt
Ev-tw (suc n) = Ev-tw n , λ c →
  lift (tw n) (↑ (tw n) c) , Ev⊕ (tw n) (↑ (tw n) c) (Ev-tw n) (EvO↑ (tw n) (tw n) (Ev-tw n) self c)

Ev-Λ : Ev Λ
Ev-Λ = Ev-tw
```

## 底

`b⊥` 是偏移到第 0 层的折叠, `bs` 是偏移对每条目标路径的折叠 (只供结点的链步取用; 当前目标的底另作参数传).

```agda
record Base (ℓ : L) : Set where
  constructor base
  field
    b⊥ : Tr zero
    bs : (j : L) → j ≤ ℓ → Tr j
open Base public

B₀ : (ℓ : L) → Base ℓ
B₀ ℓ = base (Ωt zero) (λ j _ → Ωt j)
```
