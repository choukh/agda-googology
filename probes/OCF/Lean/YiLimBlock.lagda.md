# ℕ 极限层号的路线: 块的增量

> 判决: 成品候选 (块的增量). 新证据 `Rt`: ℕ 极限层号 `lim g` 处可选地带相邻孩子的路径 g n ≤ g (n+1) (`just`), 没有就是 `nothing`; 其余层号只往下传.
> 两个孩子编号 m, n 只在 ℕ 上比较 (`cmp`), 由相邻路径合成 `Way`: 低孩子到高孩子的路径 (`fwd`: m < n; `bwd`: m ≥ n, 同号时是 `self`), 或没有路径 (`none`). 孩子层的树沿路径搬进高孩子 (`emb`, 一串 `up zero c ·`).
> 不否定什么. 路径可选的理由: 塔第 1 项的孩子层由任意树读出, 必带路径的证据不可满足 (`YiLimCheck.no-req`). 折叠在 `YiLimFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLimBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiPhiBlock
```

## 孩子编号的比较 (只在 ℕ 上)

```agda
infix 4 _<ₙ_
data _<ₙ_ (m : ℕ) : ℕ → Set where
  here : m <ₙ suc m
  nxt  : ∀ {n} → m <ₙ n → m <ₙ suc n

z< : (n : ℕ) → zero <ₙ suc n
z< zero    = here
z< (suc n) = nxt (z< n)

s< : ∀ {m n} → m <ₙ n → suc m <ₙ suc n
s< here     = here
s< (nxt l)  = nxt (s< l)

data Cmp : ℕ → ℕ → Set where
  eq : ∀ {m} → Cmp m m
  lt : ∀ {m n} → m <ₙ n → Cmp m n
  gt : ∀ {m n} → n <ₙ m → Cmp m n

sC : ∀ {m n} → Cmp m n → Cmp (suc m) (suc n)
sC eq     = eq
sC (lt l) = lt (s< l)
sC (gt l) = gt (s< l)

cmp : (m n : ℕ) → Cmp m n
cmp zero    zero    = eq
cmp zero    (suc n) = lt (z< n)
cmp (suc m) zero    = gt (z< m)
cmp (suc m) (suc n) = sC (cmp m n)

cmp-refl : (n : ℕ) → cmp n n ≡ eq
cmp-refl zero = refl
cmp-refl (suc n) rewrite cmp-refl n = refl
```

## 路线

相邻路径合成任意 m < n 的路径. `Way g m n` 是折叠在 ℕ 极限层号上实际分情形的东西; 同号并进 `bwd self`, 用不依赖的消去 `caseW` 分情形 (折叠里不用 `with`, 使层号在每次调用中字面下降).

```agda
Adj : (ℕ → L) → Set
Adj g = (n : ℕ) → g n ≤ g (suc n)

rt : (g : ℕ → L) → Adj g → ∀ {m n} → m <ₙ n → g m ≤ g n
rt g r {m} here       = r m
rt g r (nxt {n} l)    = rt g r l ∙ r n

data Way (g : ℕ → L) (m n : ℕ) : Set where
  fwd  : g m ≤ g n → Way g m n
  bwd  : g n ≤ g m → Way g m n
  none : Way g m n

caseW : ∀ {g m n} {X : Set} → Way g m n → (g m ≤ g n → X) → (g n ≤ g m → X) → X → X
caseW (fwd v) F B N = F v
caseW (bwd v) F B N = B v
caseW none    F B N = N

caseW-ind : ∀ {g m n} {X : Set} (Q : X → Set) (W : Way g m n) {F : g m ≤ g n → X} {B : g n ≤ g m → X} {N : X}
  → ((v : g m ≤ g n) → Q (F v)) → ((v : g n ≤ g m) → Q (B v)) → Q N → Q (caseW W F B N)
caseW-ind Q (fwd v) hF hB hN = hF v
caseW-ind Q (bwd v) hF hB hN = hB v
caseW-ind Q none    hF hB hN = hN

way′ : (g : ℕ → L) → Maybe (Adj g) → ∀ {m n} → Cmp m n → Way g m n
way′ g R        eq     = bwd self
way′ g (just r) (lt l) = fwd (rt g r l)
way′ g (just r) (gt l) = bwd (rt g r l)
way′ g nothing  (lt l) = none
way′ g nothing  (gt l) = none

way : (g : ℕ → L) → Maybe (Adj g) → (m n : ℕ) → Way g m n
way g R m n = way′ g R (cmp m n)

way-refl : (g : ℕ → L) (R : Maybe (Adj g)) (n : ℕ) → way g R n n ≡ bwd self
way-refl g R n rewrite cmp-refl n = refl
```

`Rt` 只在 `lim g` 处有新内容. `Rt₀` 处处没有路径 (这时折叠与 `YiUpFold` 走同样的行).

```agda
Rt : L → Set
Rt zero     = ⊤
Rt (suc a)  = Rt a
Rt (lim g)  = ((n : ℕ) → Rt (g n)) × Maybe (Adj g)
Rt (Ωₗ k h) = Rt k × ((c : Tr k) → Rt (h c))

Rt₀ : (ℓ : L) → Rt ℓ
Rt₀ zero     = tt
Rt₀ (suc a)  = Rt₀ a
Rt₀ (lim g)  = (λ n → Rt₀ (g n)) , nothing
Rt₀ (Ωₗ k h) = Rt₀ k , λ c → Rt₀ (h c)
```

## 不经下标层侧的路径

`_⊑_` 是没有 `ink` 的路径; 它在左加基底之下保持 (`⊕⊑`), 这是 `_≤_` 没有的 (`ink` 的端点在基底里). 偏移的路线 `RtP` 用它陈述, 再平移成 a ⊕ b 的路线.

```agda
infix 4 _⊑_
data _⊑_ : L → L → Set where
  self : ∀ {ℓ} → ℓ ⊑ ℓ
  ins  : ∀ {j a} → j ⊑ a → j ⊑ suc a
  inl  : ∀ {j g} (n : ℕ) → j ⊑ g n → j ⊑ lim g
  inlu : ∀ {j g} → ((n : ℕ) → j ⊑ g n) → j ⊑ lim g
  inb  : ∀ {j k h} (c : Tr k) → j ⊑ h c → j ⊑ Ωₗ k h
  inu  : ∀ {j k h} → ((c : Tr k) → j ⊑ h c) → j ⊑ Ωₗ k h

⊑→≤ : ∀ {j ℓ} → j ⊑ ℓ → j ≤ ℓ
⊑→≤ self      = self
⊑→≤ (ins v)   = ins (⊑→≤ v)
⊑→≤ (inl n v) = inl n (⊑→≤ v)
⊑→≤ (inlu vs) = inlu (λ n → ⊑→≤ (vs n))
⊑→≤ (inb c v) = inb c (⊑→≤ v)
⊑→≤ (inu vs)  = inu (λ c → ⊑→≤ (vs c))

⊑-trans : ∀ {i j ℓ} → i ⊑ j → j ⊑ ℓ → i ⊑ ℓ
⊑-trans w self      = w
⊑-trans w (ins v)   = ins (⊑-trans w v)
⊑-trans w (inl n v) = inl n (⊑-trans w v)
⊑-trans w (inlu vs) = inlu (λ n → ⊑-trans w (vs n))
⊑-trans w (inb c v) = inb c (⊑-trans w v)
⊑-trans w (inu vs)  = inu (λ c → ⊑-trans w (vs c))

⊕⊑ : (a : L) {u u′ : L} → u ⊑ u′ → a ⊕ u ⊑ a ⊕ u′
⊕⊑ a self      = self
⊕⊑ a (ins v)   = ins (⊕⊑ a v)
⊕⊑ a (inl n v) = inl n (⊕⊑ a v)
⊕⊑ a (inlu vs) = inlu (λ n → ⊕⊑ a (vs n))
⊕⊑ a (inb c v) = inb c (⊕⊑ a v)
⊕⊑ a (inu vs)  = inu (λ c → ⊕⊑ a (vs c))

⊑lift : (a b : L) → a ⊑ a ⊕ b
⊑lift a zero     = self
⊑lift a (suc b)  = ins (⊑lift a b)
⊑lift a (lim g)  = inlu (λ n → ⊑lift a (g n))
⊑lift a (Ωₗ k h) = inu (λ c → ⊑lift a (h c))

AdjP : (ℕ → L) → Set
AdjP g = (n : ℕ) → g n ⊑ g (suc n)

RtP : L → Set
RtP zero     = ⊤
RtP (suc b)  = RtP b
RtP (lim g)  = ((n : ℕ) → RtP (g n)) × Maybe (AdjP g)
RtP (Ωₗ k h) = Rt k × ((c : Tr k) → RtP (h c))

RtP₀ : (b : L) → RtP b
RtP₀ zero     = tt
RtP₀ (suc b)  = RtP₀ b
RtP₀ (lim g)  = (λ n → RtP₀ (g n)) , nothing
RtP₀ (Ωₗ k h) = Rt₀ k , λ c → RtP₀ (h c)

shiftA : (a : L) (g : ℕ → L) → Maybe (AdjP g) → Maybe (Adj (λ n → a ⊕ g n))
shiftA a g (just r) = just (λ n → ⊑→≤ (⊕⊑ a (r n)))
shiftA a g nothing  = nothing

shiftP : (a : L) (g : ℕ → L) → Maybe (AdjP g) → Maybe (AdjP (λ n → a ⊕ g n))
shiftP a g (just r) = just (λ n → ⊕⊑ a (r n))
shiftP a g nothing  = nothing

Rt⊕ : (a b : L) → Rt a → RtP b → Rt (a ⊕ b)
Rt⊕ a zero     ra rb        = ra
Rt⊕ a (suc b)  ra rb        = Rt⊕ a b ra rb
Rt⊕ a (lim g)  ra (rb , R)  = (λ n → Rt⊕ a (g n) ra (rb n)) , shiftA a g R
Rt⊕ a (Ωₗ k h) ra (rk , rb) = rk , λ c → Rt⊕ a (h c) ra (rb c)

RtP⊕ : (b₁ b₂ : L) → RtP b₁ → RtP b₂ → RtP (b₁ ⊕ b₂)
RtP⊕ b₁ zero     r₁ r₂        = r₁
RtP⊕ b₁ (suc b)  r₁ r₂        = RtP⊕ b₁ b r₁ r₂
RtP⊕ b₁ (lim g)  r₁ (r₂ , R)  = (λ n → RtP⊕ b₁ (g n) r₁ (r₂ n)) , shiftP b₁ g R
RtP⊕ b₁ (Ωₗ k h) r₁ (rk , r₂) = rk , λ c → RtP⊕ b₁ (h c) r₁ (r₂ c)
```

## 孩子层的树沿路径搬进高层

对层号递归 (与 `YiPhiFold.kp` 同一个理由: `ink` 一步经证据路径进第一个孩子). 每一步是 `up zero c ·`, 读作 0 + ↑y.

```agda
emb : (ℓ : L) → Ev ℓ → ∀ {k} → k ≤ ℓ → Tr k → Tr ℓ
emb ℓ        ε        self      y = y
emb (suc a)  ε        (ins v)   y = up zero tt (emb a ε v y)
emb (lim g)  ε        (inl n v) y = up zero n (emb (g n) (ε n) v y)
emb (lim g)  ε        (inlu vs) y = up zero zero (emb (g zero) (ε zero) (vs zero) y)
emb (Ωₗ k h) (ek , e) (ink v)   y = up zero zero (emb (h zero) (proj₂ (e zero)) (v ∙ proj₁ (e zero)) y)
emb (Ωₗ k h) (ek , e) (inb c v) y = up zero c (emb (h c) (proj₂ (e c)) v y)
emb (Ωₗ k h) (ek , e) (inu vs)  y = up zero zero (emb (h zero) (proj₂ (e zero)) (vs zero) y)
```

## 塔与 Λ 的路线 (闭项)

Λ = lim tw 的相邻路径是 `ink self` (tw n 是 tw (n+1) 的下标层). 塔第 n+1 项的孩子层 tw n ⊕ ↑c 里, 由任意树 c 读出的 ℕ 极限没有路径 (`RtP₀`).

```agda
Rt-tw : (n : ℕ) → Rt (tw n)
Rt-tw zero    = tt
Rt-tw (suc n) = Rt-tw n , λ c → Rt⊕ (tw n) (↑ (tw n) c) (Rt-tw n) (RtP₀ (↑ (tw n) c))

Adj-Λ : Adj tw
Adj-Λ n = ink self

Rt-Λ : Rt Λ
Rt-Λ = Rt-tw , just Adj-Λ
```
