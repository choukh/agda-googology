# 从头重写: 路径与层号的证据

> 判决: 成品候选 (块的增量). 路径 `Pth b` 一个类型两用: `b = true` 可经下标层侧 (`ink`), 是目标路径 `≤`; `b = false` 不经, 是 `⊑`. 层号的证据 `Ok` 一个谓词同时带 F2 的 `Ev` (下标层 ≤ 每个孩子) 与必带的路线 `Rt` (ℕ 极限层号相邻孩子的路径).
> 编译定理: 塔各项与 Λ 的证据是闭项 (`Ok-tw`, `Ok-Λ`), 无前提; 其中 ℕ 极限层号的相邻路径由树自带的相邻步进读出 (`◃→⊑`).
> 不否定什么. 折叠在 `YiRWFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRWPath where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
```

## 路径

```agda
data Pth : Bool → L → L → Set where
  self : ∀ {b ℓ} → Pth b ℓ ℓ
  inc  : ∀ {b j s h} (c : Ch s) → Pth b j (h c) → Pth b j (nd s h)
  inu  : ∀ {b j s h} → ((c : Ch s) → Pth b j (h c)) → Pth b j (nd s h)
  ink  : ∀ {j k h} → Pth true j k → Pth true j (nd (sΩ k) h)

infix 4 _≤_ _⊑_
_≤_ _⊑_ : L → L → Set
j ≤ ℓ = Pth true j ℓ
j ⊑ ℓ = Pth false j ℓ

infixl 6 _∙_
_∙_ : ∀ {b i j ℓ} → Pth b i j → Pth b j ℓ → Pth b i ℓ
w ∙ self    = w
w ∙ inc c v = inc c (w ∙ v)
w ∙ inu vs  = inu (λ c → w ∙ vs c)
w ∙ ink v   = ink (w ∙ v)

wk : ∀ {b j ℓ} → Pth b j ℓ → j ≤ ℓ
wk self      = self
wk (inc c v) = inc c (wk v)
wk (inu vs)  = inu (λ c → wk (vs c))
wk (ink v)   = ink v

lift : ∀ {b} (a c : L) → Pth b a (a ⊕ c)
lift a zero     = self
lift a (nd s h) = inu (λ c → lift a (h c))

⊕⊑ : (a : L) {u u′ : L} → u ⊑ u′ → a ⊕ u ⊑ a ⊕ u′
⊕⊑ a self      = self
⊕⊑ a (inc c v) = inc c (⊕⊑ a v)
⊕⊑ a (inu vs)  = inu (λ c → ⊕⊑ a (vs c))

z≤ : (ℓ : L) → zero ≤ ℓ
z≤ zero     = self
z≤ (nd s h) = inu (λ c → z≤ (h c))
```

槽位所在层号的路径 (`posW`); 下标层的槽位沿路径推进高层 (`psh`), 分支换回 (`pshBr`), 第一分支到第一分支 (`pshFirst`).

```agda
bz⁼ : (a : L) (t : Pos⁼ a) → Br⁼ a t
bz⁼ a t = proj₂ (sl⁼ a t) zero

mutual
  posW : (ℓ : L) (p : Pos ℓ) → at ℓ p ≤ ℓ
  posW (nd s h)      (inj₂ (c , t)) = inc c (posW⁼ (h c) t)
  posW (nd (sΩ k) h) (inj₁ t)       = ink (posW⁼ k t)

  posW⁼ : (a : L) (t : Pos⁼ a) → proj₁ (sl⁼ a t) ≤ a
  posW⁼ a (inj₁ _) = self
  posW⁼ a (inj₂ p) = posW a p

psh : ∀ {k a} → k ≤ a → Pos⁼ k → Pos⁼ a
psh self                 t = t
psh (inc c v)            t = inj₂ (inj₂ (c , psh v t))
psh {a = nd s h} (inu vs) t = inj₂ (inj₂ (c₀ s , psh (vs (c₀ s)) t))
psh (ink v)              t = inj₂ (inj₁ (psh v t))

pshBr : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → Br⁼ a (psh v t) → Br⁼ k t
pshBr self                 t z = z
pshBr (inc c v)            t z = pshBr v t z
pshBr {a = nd s h} (inu vs) t z = pshBr (vs (c₀ s)) t z
pshBr (ink v)              t z = pshBr v t z

pshFirst : ∀ {k a} (v : k ≤ a) (t : Pos⁼ k) → pshBr v t (bz⁼ a (psh v t)) ≡ bz⁼ k t
pshFirst self                 t = refl
pshFirst (inc c v)            t = pshFirst v t
pshFirst {a = nd s h} (inu vs) t = pshFirst (vs (c₀ s)) t
pshFirst (ink v)              t = pshFirst v t
```

## 层号的证据

`Ok`: Ω 形状的下标层合法且 ≤ 每个孩子; ℕ 极限形状的相邻孩子有路径 (必带). `OkO a b`: 偏移 b 加在 a 上之后合法所需 (Ω 形状的下标层 ≤ a; ℕ 极限形状的相邻孩子有不经下标层侧的路径).

```agda
mutual
  Ok : L → Set
  Ok zero     = ⊤
  Ok (nd s h) = OkS s h × ((c : Ch s) → Ok (h c))

  OkS : (s : Sh) → (Ch s → L) → Set
  OkS sS     h = ⊤
  OkS sL     g = (n : ℕ) → g n ≤ g (suc n)
  OkS (sΩ k) h = Ok k × ((c : Tr k) → k ≤ h c)

mutual
  Ok-at : (ℓ : L) → Ok ℓ → (p : Pos ℓ) → Ok (at ℓ p)
  Ok-at (nd s h)      (_ , oc)      (inj₂ (c , t)) = Ok-at⁼ (h c) (oc c) t
  Ok-at (nd (sΩ k) h) ((ok , _) , _) (inj₁ t)      = Ok-at⁼ k ok t

  Ok-at⁼ : (a : L) → Ok a → (t : Pos⁼ a) → Ok (proj₁ (sl⁼ a t))
  Ok-at⁼ a o (inj₁ _) = o
  Ok-at⁼ a o (inj₂ p) = Ok-at a o p

OkOS : L → (s : Sh) → (Ch s → L) → Set
OkOS a sS     h = ⊤
OkOS a sL     g = (n : ℕ) → g n ⊑ g (suc n)
OkOS a (sΩ k) h = (k ≤ a) × Ok k

OkO : L → L → Set
OkO a zero     = ⊤
OkO a (nd s h) = OkOS a s h × ((c : Ch s) → OkO a (h c))

OkS⊕ : (a : L) (s : Sh) (h : Ch s → L) → OkOS a s h → OkS s (λ c → a ⊕ h c)
OkS⊕ a sS     h _        = tt
OkS⊕ a sL     g r        = λ n → wk (⊕⊑ a (r n))
OkS⊕ a (sΩ k) h (v , ok) = ok , λ c → v ∙ lift a (h c)

Ok⊕ : (a b : L) → Ok a → OkO a b → Ok (a ⊕ b)
Ok⊕ a zero     oa _         = oa
Ok⊕ a (nd s h) oa (os , ob) = OkS⊕ a s h os , λ c → Ok⊕ a (h c) oa (ob c)

OkO⊕ : (a b₁ b₂ : L) → OkO a b₁ → OkO a b₂ → OkO a (b₁ ⊕ b₂)
OkO⊕ a b₁ zero          e₁ _         = e₁
OkO⊕ a b₁ (nd sS h)     e₁ (_ , e₂)  = tt , λ c → OkO⊕ a b₁ (h c) e₁ (e₂ c)
OkO⊕ a b₁ (nd sL g)     e₁ (r , e₂)  = (λ n → ⊕⊑ b₁ (r n)) , λ n → OkO⊕ a b₁ (g n) e₁ (e₂ n)
OkO⊕ a b₁ (nd (sΩ k) h) e₁ (o , e₂)  = o , λ c → OkO⊕ a b₁ (h c) e₁ (e₂ c)
```

树的序给出读回层号之间不经下标层侧的路径; 所以任意树读出的偏移带证据, 塔各项与 Λ 的证据是闭项.

```agda
◃→⊑ : (k : L) {x y : Tr k} → k ⊢ x ◃ y → ↑ k x ⊑ ↑ k y
◃→⊑ k        ◃s           = inc tt self
◃→⊑ k        (◃l n)       = inc n self
◃→⊑ k        ◃w           = inc zero self
◃→⊑ (nd s h) (◃u x c y e) = lift (↑ (nd s h) x) (↑ (h c) y)
◃→⊑ (nd s h) (◃c x c d)   = ⊕⊑ (↑ (nd s h) x) (◃→⊑ (h c) d)
◃→⊑ k        (◃t d e)     = ◃→⊑ k d ∙ ◃→⊑ k e

OkO↑ : (a k : L) → Ok k → k ≤ a → (t : Tr k) → OkO a (↑ k t)
OkO↑ a k        ok v zero         = tt
OkO↑ a k        ok v (suc x)      = tt , λ _ → OkO↑ a k ok v x
OkO↑ a k        ok v (lim f r)    = (λ n → ◃→⊑ k (r n)) , λ n → OkO↑ a k ok v (f n)
OkO↑ a k        ok v (Ω p g)      = (posW k p ∙ v , Ok-at k ok p) , λ c → OkO↑ a k ok v (g (fromBr k p c))
OkO↑ a (nd s h) ok v (up x c y _) =
  OkO⊕ a (↑ (nd s h) x) (↑ (h c) y) (OkO↑ a (nd s h) ok v x) (OkO↑ a (h c) (proj₂ ok c) (inc c self ∙ v) y)

Ok-tw : (n : ℕ) → Ok (tw n)
Ok-tw zero    = tt
Ok-tw (suc n) = (Ok-tw n , λ c → lift (tw n) (↑ (tw n) c)) , λ c →
  Ok⊕ (tw n) (↑ (tw n) c) (Ok-tw n) (OkO↑ (tw n) (tw n) (Ok-tw n) self c)

Ok-Λ : Ok Λ
Ok-Λ = (λ n → ink self) , Ok-tw
```

## ℕ 极限层号上两个孩子的比较, 孩子树沿路径搬进高层

`way g r m n`: m < n 给 `inj₁` (g m ≤ g n), 否则 `inj₂` (g n ≤ g m); 路径由相邻路径接成. `emb` 每一步是 `upz`.

```agda
from0 : (g : ℕ → L) → ((n : ℕ) → g n ≤ g (suc n)) → (n : ℕ) → g zero ≤ g n
from0 g r zero    = self
from0 g r (suc n) = from0 g r n ∙ r n

way : (g : ℕ → L) → ((n : ℕ) → g n ≤ g (suc n)) → (m n : ℕ) → (g m ≤ g n) ⊎ (g n ≤ g m)
way g r m       zero    = inj₂ (from0 g r m)
way g r zero    (suc n) = inj₁ (from0 g r (suc n))
way g r (suc m) (suc n) = way (λ i → g (suc i)) (λ i → r (suc i)) m n

cW : ∀ {A B X : Set} → A ⊎ B → (A → X) → (B → X) → X
cW (inj₁ a) F G = F a
cW (inj₂ b) F G = G b

cW-ind : ∀ {A B X : Set} (Q : X → Set) (W : A ⊎ B) {F : A → X} {G : B → X}
       → ((a : A) → Q (F a)) → ((b : B) → Q (G b)) → Q (cW W F G)
cW-ind Q (inj₁ a) hF hG = hF a
cW-ind Q (inj₂ b) hF hG = hG b

cW-ind₂ : ∀ {A B X : Set} (Q : X → X → Set) (W : A ⊎ B) {F F′ : A → X} {G G′ : B → X}
        → ((a : A) → Q (F a) (F′ a)) → ((b : B) → Q (G b) (G′ b)) → Q (cW W F G) (cW W F′ G′)
cW-ind₂ Q (inj₁ a) hF hG = hF a
cW-ind₂ Q (inj₂ b) hF hG = hG b

emb : (ℓ : L) → Ok ℓ → ∀ {k} → k ≤ ℓ → Tr⁺ k → Tr⁺ ℓ
emb ℓ             o self      y = y
emb (nd s h)      o (inc c v) y = upz c (emb (h c) (proj₂ o c) v y)
emb (nd s h)      o (inu vs)  y = upz (c₀ s) (emb (h (c₀ s)) (proj₂ o (c₀ s)) (vs (c₀ s)) y)
emb (nd (sΩ k) h) o (ink v)   y = upz zero (emb (h zero) (proj₂ o zero) (v ∙ proj₂ (proj₁ o) zero) y)

emb-mono : (ℓ : L) (o : Ok ℓ) {k : L} (v : k ≤ ℓ) {y′ y : Tr⁺ k}
         → k ⊢ proj₁ y′ ◃ proj₁ y → ℓ ⊢ proj₁ (emb ℓ o v y′) ◃ proj₁ (emb ℓ o v y)
emb-mono ℓ             o self      d = d
emb-mono (nd s h)      o (inc c v) d = ◃c zero c (emb-mono (h c) (proj₂ o c) v d)
emb-mono (nd s h)      o (inu vs)  d = ◃c zero (c₀ s) (emb-mono (h (c₀ s)) (proj₂ o (c₀ s)) (vs (c₀ s)) d)
emb-mono (nd (sΩ k) h) o (ink v)   d = ◃c zero zero (emb-mono (h zero) (proj₂ o zero) (v ∙ proj₂ (proj₁ o) zero) d)
```
