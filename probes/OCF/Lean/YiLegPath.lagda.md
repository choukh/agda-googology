# 合法性进块: 路径, 层号证据, 必带的路线

> 判决: 成品候选 (块的增量, 原型). 目标路径 `_≤_`, 层号证据 `Ev` 与 `YiPhiBlock` 同文; 路线证据 `Rt` 在 ℕ 极限层号处**必带**相邻孩子的路径 (不是 `Maybe`), 所以 `Way` 只有 `fwd`, `bwd` 两种, 没有 `none`.
> 编译定理: 第一位置序的每一步给读回层号之间的路径 (`◃→⊑`), 所以任意树读出的偏移带必带的路线 (`RtP↑`, 对一切树, 只要所在层号带路线); 塔各项与 Λ 的路线是闭项 (`Rt-tw`, `Rt-Λ`), 无前提.
> 不否定什么. 对照 `YiLimCheck.no-req`: 那里的反例 `lim (1,0,0,…)` 在本块里不是树. 折叠在 `YiLegFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLegPath where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiLegBlock
```

## 目标路径

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

pshFirst : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → pshBr v t (br0⁼ a (psh v t)) ≡ br0⁼ k t
pshFirst self      t = refl
pshFirst (ins v)   t = pshFirst v t
pshFirst (inl n v) t = pshFirst v t
pshFirst (inlu vs) t = pshFirst (vs zero) t
pshFirst (ink v)   t = pshFirst v t
pshFirst (inb c v) t = pshFirst v t
pshFirst (inu vs)  t = pshFirst (vs zero) t
```

## 层号的证据 (`Ev`)

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

mutual
  EvO↑ : (a k : L) → Ev k → k ≤ a → (t : Tr k) → EvO a (↑ k t)
  EvO↑ a k ek v zero         = tt
  EvO↑ a k ek v (suc x)      = EvO↑ a k ek v x
  EvO↑ a k ek v (lim f _)    = λ n → EvO↑ a k ek v (f n)
  EvO↑ a k ek v (Ω p g)      = posW k p ∙ v , Ev-at k ek p , λ c → EvO↑ a k ek v (g (fromBr k p c))
  EvO↑ a k ek v (up x c y _) = EvO⊕ a (↑ k x) (↑ch k c y) (EvO↑ a k ek v x) (EvO↑ch a k ek v c y)

  EvO↑ch : (a k : L) → Ev k → k ≤ a → (c : Ch k) (y : ChT k c) → EvO a (↑ch k c y)
  EvO↑ch a (suc k)  ek       v _ y = EvO↑ a k ek (ins self ∙ v) y
  EvO↑ch a (lim g)  ek       v n y = EvO↑ a (g n) (ek n) (inl n self ∙ v) y
  EvO↑ch a (Ωₗ k h) (_ , ek) v c y = EvO↑ a (h c) (proj₂ (ek c)) (inb c self ∙ v) y

Ev-tw : (n : ℕ) → Ev (tw n)
Ev-tw zero    = tt
Ev-tw (suc n) = Ev-tw n , λ c →
  lift (tw n) (↑ (tw n) c) , Ev⊕ (tw n) (↑ (tw n) c) (Ev-tw n) (EvO↑ (tw n) (tw n) (Ev-tw n) self c)

Ev-Λ : Ev Λ
Ev-Λ = Ev-tw
```

## 孩子编号的比较 (只在 ℕ 上) 与路线

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

Adj : (ℕ → L) → Set
Adj g = (n : ℕ) → g n ≤ g (suc n)

rt : (g : ℕ → L) → Adj g → ∀ {m n} → m <ₙ n → g m ≤ g n
rt g r {m} here    = r m
rt g r (nxt {n} l) = rt g r l ∙ r n

data Way (g : ℕ → L) (m n : ℕ) : Set where
  fwd : g m ≤ g n → Way g m n
  bwd : g n ≤ g m → Way g m n

caseW : ∀ {g m n} {X : Set} → Way g m n → (g m ≤ g n → X) → (g n ≤ g m → X) → X
caseW (fwd v) F B = F v
caseW (bwd v) F B = B v

caseW-ind : ∀ {g m n} {X : Set} (Q : X → Set) (W : Way g m n) {F : g m ≤ g n → X} {B : g n ≤ g m → X}
  → ((v : g m ≤ g n) → Q (F v)) → ((v : g n ≤ g m) → Q (B v)) → Q (caseW W F B)
caseW-ind Q (fwd v) hF hB = hF v
caseW-ind Q (bwd v) hF hB = hB v

caseW-ind₂ : ∀ {g m n} {X : Set} (Q : X → X → Set) (W : Way g m n)
  {F F′ : g m ≤ g n → X} {B B′ : g n ≤ g m → X}
  → ((v : g m ≤ g n) → Q (F v) (F′ v)) → ((v : g n ≤ g m) → Q (B v) (B′ v))
  → Q (caseW W F B) (caseW W F′ B′)
caseW-ind₂ Q (fwd v) hF hB = hF v
caseW-ind₂ Q (bwd v) hF hB = hB v

way′ : (g : ℕ → L) → Adj g → ∀ {m n} → Cmp m n → Way g m n
way′ g r eq     = bwd self
way′ g r (lt l) = fwd (rt g r l)
way′ g r (gt l) = bwd (rt g r l)

way : (g : ℕ → L) → Adj g → (m n : ℕ) → Way g m n
way g r m n = way′ g r (cmp m n)

way-refl : (g : ℕ → L) (r : Adj g) (n : ℕ) → way g r n n ≡ bwd self
way-refl g r n rewrite cmp-refl n = refl

Rt : L → Set
Rt zero     = ⊤
Rt (suc a)  = Rt a
Rt (lim g)  = ((n : ℕ) → Rt (g n)) × Adj g
Rt (Ωₗ k h) = Rt k × ((c : Tr k) → Rt (h c))

mutual
  Rt-at : (ℓ : L) → Rt ℓ → (p : Pos ℓ) → Rt (at ℓ p)
  Rt-at (suc a)  ρ        t              = Rt-at⁼ a ρ t
  Rt-at (lim g)  (ρc , _) (n , t)        = Rt-at⁼ (g n) (ρc n) t
  Rt-at (Ωₗ k h) (ρk , _) (inj₁ t)       = Rt-at⁼ k ρk t
  Rt-at (Ωₗ k h) (_ , ρc) (inj₂ (c , t)) = Rt-at⁼ (h c) (ρc c) t

  Rt-at⁼ : (a : L) → Rt a → (t : Pos⁼ a) → Rt (at⁼ a t)
  Rt-at⁼ a ρ (inj₁ _) = ρ
  Rt-at⁼ a ρ (inj₂ p) = Rt-at a ρ p
```

## 不经下标层侧的路径, 偏移的路线

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
RtP (lim g)  = ((n : ℕ) → RtP (g n)) × AdjP g
RtP (Ωₗ k h) = Rt k × ((c : Tr k) → RtP (h c))

Rt⊕ : (a b : L) → Rt a → RtP b → Rt (a ⊕ b)
Rt⊕ a zero     ra rb        = ra
Rt⊕ a (suc b)  ra rb        = Rt⊕ a b ra rb
Rt⊕ a (lim g)  ra (rb , R)  = (λ n → Rt⊕ a (g n) ra (rb n)) , (λ n → ⊑→≤ (⊕⊑ a (R n)))
Rt⊕ a (Ωₗ k h) ra (rk , rb) = rk , λ c → Rt⊕ a (h c) ra (rb c)

RtP⊕ : (b₁ b₂ : L) → RtP b₁ → RtP b₂ → RtP (b₁ ⊕ b₂)
RtP⊕ b₁ zero     r₁ r₂        = r₁
RtP⊕ b₁ (suc b)  r₁ r₂        = RtP⊕ b₁ b r₁ r₂
RtP⊕ b₁ (lim g)  r₁ (r₂ , R)  = (λ n → RtP⊕ b₁ (g n) r₁ (r₂ n)) , (λ n → ⊕⊑ b₁ (R n))
RtP⊕ b₁ (Ωₗ k h) r₁ (rk , r₂) = rk , λ c → RtP⊕ b₁ (h c) r₁ (r₂ c)
```

## 树的序给出路径; 任意树读出的偏移带路线

后继 `ins`, 极限的第 n 项 `inl n`, 结点的第一分支 `inb zero`, 嵌入 `⊑lift`, 孩子里的一步在左加之下保持 (`⊕⊑`).
`RtP↑` 的 ℕ 极限一行直接取树自带的相邻步进; Ω 结点一行对分支递归 (分支是合法树), 下标层的路线由所在层号的路线读出 (`Rt-at`).

```agda
◃→⊑ : (k : L) {x y : Tr k} → k ⊢ x ◃ y → ↑ k x ⊑ ↑ k y
◃→⊑ k ◃s       = ins self
◃→⊑ k (◃l n)   = inl n self
◃→⊑ k (◃w {p = p} {g = g}) =
  subst (λ z → ↑ k (g z) ⊑ Ωₗ (at k p) (λ c → ↑ k (g (fromBr k p c)))) (sym (br0≡ k p)) (inb zero self)
◃→⊑ k (◃u x c y e) = ⊑lift (↑ k x) (↑ch k c y)
◃→⊑ (suc a)  (◃c x _ d) = ⊕⊑ (↑ (suc a) x) (◃→⊑ a d)
◃→⊑ (lim g)  (◃c x n d) = ⊕⊑ (↑ (lim g) x) (◃→⊑ (g n) d)
◃→⊑ (Ωₗ k h) (◃c x c d) = ⊕⊑ (↑ (Ωₗ k h) x) (◃→⊑ (h c) d)
◃→⊑ zero     (◃c x () d)
◃→⊑ k (◃t d e) = ⊑-trans (◃→⊑ k d) (◃→⊑ k e)

mutual
  RtP↑ : (k : L) → Rt k → (t : Tr k) → RtP (↑ k t)
  RtP↑ k ρ zero         = tt
  RtP↑ k ρ (suc x)      = RtP↑ k ρ x
  RtP↑ k ρ (lim f a)    = (λ n → RtP↑ k ρ (f n)) , (λ n → ◃→⊑ k (a n))
  RtP↑ k ρ (Ω p g)      = Rt-at k ρ p , λ c → RtP↑ k ρ (g (fromBr k p c))
  RtP↑ k ρ (up x c y _) = RtP⊕ (↑ k x) (↑ch k c y) (RtP↑ k ρ x) (RtP↑ch k ρ c y)

  RtP↑ch : (k : L) → Rt k → (c : Ch k) (y : ChT k c) → RtP (↑ch k c y)
  RtP↑ch (suc a)  ρ        _ y = RtP↑ a ρ y
  RtP↑ch (lim g)  (ρc , _) n y = RtP↑ (g n) (ρc n) y
  RtP↑ch (Ωₗ k h) (_ , ρc) c y = RtP↑ (h c) (ρc c) y
```

## 塔与 Λ 的必带路线 (闭项, 无前提)

```agda
Rt-tw : (n : ℕ) → Rt (tw n)
Rt-tw zero    = tt
Rt-tw (suc n) = Rt-tw n , λ c → Rt⊕ (tw n) (↑ (tw n) c) (Rt-tw n) (RtP↑ (tw n) (Rt-tw n) c)

Rt-Λ : Rt Λ
Rt-Λ = Rt-tw , λ n → ink self
```

## 孩子层的树沿路径搬进高层

每一步是 `up zero c ·`; 嵌入要 "孩子非零", 所以搬运与它的非零互递归.

```agda
mutual
  emb : (ℓ : L) → Ev ℓ → ∀ {k} → k ≤ ℓ → (y : Tr k) → k ⊢ zero ◃ y → Tr ℓ
  emb ℓ        ε        self      y nz = y
  emb (suc a)  ε        (ins v)   y nz = up zero tt (emb a ε v y nz) (emb-nz a ε v y nz)
  emb (lim g)  ε        (inl n v) y nz = up zero n (emb (g n) (ε n) v y nz) (emb-nz (g n) (ε n) v y nz)
  emb (lim g)  ε        (inlu vs) y nz =
    up zero zero (emb (g zero) (ε zero) (vs zero) y nz) (emb-nz (g zero) (ε zero) (vs zero) y nz)
  emb (Ωₗ k h) (ek , e) (ink v)   y nz =
    up zero zero (emb (h zero) (proj₂ (e zero)) (v ∙ proj₁ (e zero)) y nz)
                 (emb-nz (h zero) (proj₂ (e zero)) (v ∙ proj₁ (e zero)) y nz)
  emb (Ωₗ k h) (ek , e) (inb c v) y nz = up zero c (emb (h c) (proj₂ (e c)) v y nz) (emb-nz (h c) (proj₂ (e c)) v y nz)
  emb (Ωₗ k h) (ek , e) (inu vs)  y nz =
    up zero zero (emb (h zero) (proj₂ (e zero)) (vs zero) y nz) (emb-nz (h zero) (proj₂ (e zero)) (vs zero) y nz)

  emb-nz : (ℓ : L) (ε : Ev ℓ) {k : L} (v : k ≤ ℓ) (y : Tr k) (nz : k ⊢ zero ◃ y) → ℓ ⊢ zero ◃ emb ℓ ε v y nz
  emb-nz ℓ        ε        self      y nz = nz
  emb-nz (suc a)  ε        (ins v)   y nz = ◃u zero tt _ _
  emb-nz (lim g)  ε        (inl n v) y nz = ◃u zero n _ _
  emb-nz (lim g)  ε        (inlu vs) y nz = ◃u zero zero _ _
  emb-nz (Ωₗ k h) (ek , e) (ink v)   y nz = ◃u zero zero _ _
  emb-nz (Ωₗ k h) (ek , e) (inb c v) y nz = ◃u zero c _ _
  emb-nz (Ωₗ k h) (ek , e) (inu vs)  y nz = ◃u zero zero _ _

emb-mono : (ℓ : L) (ε : Ev ℓ) {k : L} (v : k ≤ ℓ) {y′ y : Tr k} {n′ : k ⊢ zero ◃ y′} {n : k ⊢ zero ◃ y}
         → k ⊢ y′ ◃ y → ℓ ⊢ emb ℓ ε v y′ n′ ◃ emb ℓ ε v y n
emb-mono ℓ        ε        self      d = d
emb-mono (suc a)  ε        (ins v)   d = ◃c zero tt (emb-mono a ε v d)
emb-mono (lim g)  ε        (inl n v) d = ◃c zero n (emb-mono (g n) (ε n) v d)
emb-mono (lim g)  ε        (inlu vs) d = ◃c zero zero (emb-mono (g zero) (ε zero) (vs zero) d)
emb-mono (Ωₗ k h) (ek , e) (ink v)   d = ◃c zero zero (emb-mono (h zero) (proj₂ (e zero)) (v ∙ proj₁ (e zero)) d)
emb-mono (Ωₗ k h) (ek , e) (inb c v) d = ◃c zero c (emb-mono (h c) (proj₂ (e c)) v d)
emb-mono (Ωₗ k h) (ek , e) (inu vs)  d = ◃c zero zero (emb-mono (h zero) (proj₂ (e zero)) (vs zero) d)
```
