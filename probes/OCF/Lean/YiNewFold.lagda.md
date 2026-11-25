# YiNew 折叠: 朝一切有限层同时折叠, 带底

判决 (编译定理): 折叠 `Ψ` 对第一位置序单调 (`mono`), 不降底 (`infl`), 输出非零 (`nz`); 嵌入一致是 `refl` (`up-Om`).
做了什么: 目标只取有限层 j, 对一切层与一切孩子一致给出; 底是 "每个有限层一棵树" 的族; 进孩子时把 x 的整族折叠当底.
不否定什么: 非有限层的分支码只有局部一步折叠 `D` 或退到第 0 层, 这些码不认得左边的项; 输出树的合法性没有证.
入口: 验收与闭项在 `OCF.Lean.YiNewKey`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNewFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiNewBlock
```

## 泛型树上的加法, 后继步, 迭代

后继步 `S b` 是 b·2, b·3, … 的 ℕ 极限 (第一位置是 b + b).

```agda
module _ {U : Set} {B : U → Set} {E : Set} {M : E → Set} where
  infixl 6 _+_
  _+_ : Tr U B E M → Tr U B E M → Tr U B E M
  a + zr       = a
  a + sc b     = sc (a + b)
  a + lm f     = lm (λ n → a + f n)
  a + Lm u g   = Lm u (λ z → a + g z)
  a + up x e y = up (a + x) e y

  tms : Tr U B E M → ℕ → Tr U B E M
  tms b zero    = b + b
  tms b (suc n) = tms b n + b

  S : Tr U B E M → Tr U B E M
  S b = lm (tms b)

iter : {A : Set} → (A → A) → A → ℕ → A
iter f a zero    = a
iter f a (suc n) = f (iter f a n)
```

## 第一位置序

极限与分支只看第一位置 (ℕ 极限看第 0 项, 分支看分支类型里的零 `z u`). 这是一个粗的预序.

```agda
module Ord {U : Set} {B : U → Set} {E : Set} {M : E → Set} (z : ∀ u → B u) where
  infix 4 _≤_
  data _≤_ : Tr U B E M → Tr U B E M → Set where
    z≤  : ∀ {a} → zr ≤ a
    s≤s : ∀ {a b} → a ≤ b → sc a ≤ sc b
    ≤s  : ∀ {a b} → a ≤ b → a ≤ sc b
    ≤l  : ∀ {a f} → a ≤ f 0 → a ≤ lm f
    l≤l : ∀ {f g} → f 0 ≤ g 0 → lm f ≤ lm g
    ≤L  : ∀ {a u g} → a ≤ g (z u) → a ≤ Lm u g
    L≤L : ∀ {u f g} → f (z u) ≤ g (z u) → Lm u f ≤ Lm u g
    ≤u  : ∀ {a x e y} → a ≤ x → a ≤ up x e y
    u≤u : ∀ {x x′ e y} → x ≤ x′ → up x e y ≤ up x′ e y

  ≤-refl : ∀ a → a ≤ a
  ≤-refl zr         = z≤
  ≤-refl (sc a)     = s≤s (≤-refl a)
  ≤-refl (lm f)     = l≤l (≤-refl (f 0))
  ≤-refl (Lm u g)   = L≤L (≤-refl (g (z u)))
  ≤-refl (up x e y) = u≤u (≤-refl x)

  ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  ≤-trans z≤      _       = z≤
  ≤-trans p       (≤s q)  = ≤s (≤-trans p q)
  ≤-trans p       (≤l q)  = ≤l (≤-trans p q)
  ≤-trans p       (≤L q)  = ≤L (≤-trans p q)
  ≤-trans p       (≤u q)  = ≤u (≤-trans p q)
  ≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)
  ≤-trans (≤s p)  (s≤s q) = ≤s (≤-trans p q)
  ≤-trans (≤l p)  (l≤l q) = ≤l (≤-trans p q)
  ≤-trans (l≤l p) (l≤l q) = l≤l (≤-trans p q)
  ≤-trans (≤L p)  (L≤L q) = ≤L (≤-trans p q)
  ≤-trans (L≤L p) (L≤L q) = L≤L (≤-trans p q)
  ≤-trans (≤u p)  (u≤u q) = ≤u (≤-trans p q)
  ≤-trans (u≤u p) (u≤u q) = u≤u (≤-trans p q)

  ≤+ : ∀ {a b} c → a ≤ b → a ≤ b + c
  ≤+ zr         p = p
  ≤+ (sc c)     p = ≤s (≤+ c p)
  ≤+ (lm f)     p = ≤l (≤+ (f 0) p)
  ≤+ (Lm u g)   p = ≤L (≤+ (g (z u)) p)
  ≤+ (up x e y) p = ≤u (≤+ x p)

  +mono : ∀ {a a′ b b′} → a ≤ a′ → b ≤ b′ → a + b ≤ a′ + b′
  +mono {b′ = b′} p z≤ = ≤+ b′ p
  +mono p (s≤s q) = s≤s (+mono p q)
  +mono p (≤s q)  = ≤s (+mono p q)
  +mono p (≤l q)  = ≤l (+mono p q)
  +mono p (l≤l q) = l≤l (+mono p q)
  +mono p (≤L q)  = ≤L (+mono p q)
  +mono p (L≤L q) = L≤L (+mono p q)
  +mono p (≤u q)  = ≤u (+mono p q)
  +mono p (u≤u q) = u≤u (+mono p q)

  S-mono : ∀ {b b′} → b ≤ b′ → S b ≤ S b′
  S-mono p = l≤l (+mono p p)

  ≤S : ∀ {a b} → a ≤ b → a ≤ S b
  ≤S {b = b} p = ≤l (≤+ b p)

module O (ℓ : Lv) = Ord {U ℓ} {Br ℓ} {E ℓ} {Em ℓ} (z0 ℓ)

Le : (ℓ : Lv) → T ℓ → T ℓ → Set
Le ℓ = O._≤_ ℓ
```

## 局部一步折叠

`D ℓ` 把 `su ℓ` 层的树折到 ℓ 层: 顶码 (分支类型是 ℓ 层的树) 对角化, 其余码原样保留.
它只用层号的后继构造子, 不看孩子. `K` 是低层嵌入进来的那一段的处理 (逐个后继施 `S`).

```agda
module _ {U : Set} {B : U → Set} {E : Set} {M : E → Set} where
  K : Tr U B E M → Tr U B E M → Tr U B E M
  K zr         b = b
  K (sc y)     b = S (K y b)
  K (lm f)     b = lm (λ n → K (f n) b)
  K (Lm u g)   b = Lm u (λ z → K (g z) b)
  K (up x e y) b = up (K x b) e y

D : (ℓ : Lv) → T (su ℓ) → T ℓ → T ℓ
D ℓ zr                b = b
D ℓ (sc y)            b = S (D ℓ y b)
D ℓ (lm f)            b = lm (λ n → D ℓ (f n) b)
D ℓ (Lm (inj₁ _) g)   b = lm (λ n → D ℓ (g (iter (λ ζ → D ℓ (g ζ) b) zr n)) b)
D ℓ (Lm (inj₂ u) g)   b = Lm u (λ z → D ℓ (g z) b)
D ℓ (up x _ y)        b = K y (D ℓ x b)
```

## 分支码的分类

每个码按它自己的字面结构分两类, 不比较孩子:

- `abs k`: 分支类型字面上是有限层 k 的树 (或经 `e0` 退到第 0 层), 带换算 `to` 与 "零对零" 的证据;
- `loc`: 后继层的顶码而下面的层不是有限层, 只有局部的一步折叠 `D`.

识别 "有限层" 只匹配 `ze` 与 `su`, 遇到 `li` 与 `Om` 一律答否, 所以不判定任何函数的相等.
跨过 ℕ 极限或 Ω 结点时, `loc` 码降成 `abs 0`: 这一处就是没有认得左边的项的地方.

```agda
data Fin? : Lv → Set where
  yes : (k : ℕ) → Fin? (fin k)
  no  : ∀ {ℓ} → Fin? ℓ

fin? : (ℓ : Lv) → Fin? ℓ
fin? ze       = yes 0
fin? (su ℓ) with fin? ℓ
... | yes k = yes (suc k)
... | no    = no
fin? (li _)   = no
fin? (Om _ _) = no

e0 : (ℓ : Lv) → F 0 → T ℓ
e0 ℓ zr     = zr
e0 ℓ (sc x) = sc (e0 ℓ x)
e0 ℓ (lm f) = lm (λ n → e0 ℓ (f n))

ez : (ℓ : Lv) (u : U ℓ) → F 0 → Br ℓ u
ez (su ℓ)   (inj₁ _) x = e0 ℓ x
ez (su ℓ)   (inj₂ u) x = ez ℓ u x
ez (li f)   (n , u)  x = ez (f n) u x
ez (Om a f) (c , u)  x = ez (f c) u x

ez0 : (ℓ : Lv) (u : U ℓ) → ez ℓ u zr ≡ z0 ℓ u
ez0 (su ℓ)   (inj₁ _) = refl
ez0 (su ℓ)   (inj₂ u) = ez0 ℓ u
ez0 (li f)   (n , u)  = ez0 (f n) u
ez0 (Om a f) (c , u)  = ez0 (f c) u

one : ∀ {U B E M} → Tr U B E M
one = sc zr

data Cls (ℓ : Lv) (u : U ℓ) : Set where
  abs : (k : ℕ) (to : F k → Br ℓ u) → to zr ≡ z0 ℓ u → Cls ℓ u
  loc : ((Br ℓ u → T ℓ) → Br ℓ u → Br ℓ u) → Cls ℓ u

cls : (ℓ : Lv) (u : U ℓ) → Cls ℓ u
cls (su ℓ) (inj₁ _) with fin? ℓ
... | yes k = abs k (λ x → x) refl
... | no    = loc (λ g ζ → D ℓ (g ζ) one)
cls (su ℓ) (inj₂ u) with cls ℓ u
... | abs k to e = abs k to e
... | loc s      = loc (λ g → s (λ z → D ℓ (g z) one))
cls (li f) (n , u) with cls (f n) u
... | abs k to e = abs k to e
... | loc _      = abs 0 (ez (f n) u) (ez0 (f n) u)
cls (Om a f) (c , u) with cls (f c) u
... | abs k to e = abs k to e
... | loc _      = abs 0 (ez (f c) u) (ez0 (f c) u)
```

## 有限目标里的槽位

`slot k j`: 目标层 j 里分支类型为有限层 k 的树的码 (当 k < j). 这是两个自然数的比较, 可判定.

```agda
data Cmp (k : ℕ) : ℕ → Set where
  eq : Cmp k k
  ne : ∀ {j} → Cmp k j

cmp : (k j : ℕ) → Cmp k j
cmp zero    zero    = eq
cmp zero    (suc j) = ne
cmp (suc k) zero    = ne
cmp (suc k) (suc j) with cmp k j
... | eq = eq
... | ne = ne

Slot : ℕ → ℕ → Set
Slot k j = Σ (U (fin j)) (λ v → Σ (Br (fin j) v → F k) (λ bk → bk (z0 (fin j) v) ≡ zr))

slot : (k j : ℕ) → Maybe (Slot k j)
slot k zero = nothing
slot k (suc j) with cmp k j
... | eq = just (inj₁ tt , (λ x → x) , refl)
... | ne with slot k j
...   | just (v , bk , e) = just (inj₂ v , bk , e)
...   | nothing           = nothing
```

## 折叠

底 `Base` 是每个有限层一棵树. `Ψ ℓ y B j` 读作: 左边的项对各有限层的折叠是 B 时, 再接上 y, 朝第 j 层折叠.
分支结点: 有槽位就保留成目标层里的分支, 没有就对角化, 对角化的下一项是 "同一棵树朝第 k 层的折叠", 用的是同一个底.
嵌入 `up x e y`: 先折 x 得到整族, 把它当底交给孩子层的 y. 孩子是哪一个只由 `up` 自己的 e 决定, 目标 j 与孩子无关.

```agda
Base : Set
Base = (j : ℕ) → F j

LimC : ∀ {ℓ u} → Cls ℓ u → (Br ℓ u → T ℓ) → (Br ℓ u → Base) → Base
LimC (abs k to _) g r j with slot k j
... | just (v , bk , _) = Lm v (λ z′ → r (to (bk z′)) j)
... | nothing           = lm (λ n → r (to (iter (λ ζ → r (to ζ) k) zr n)) j)
LimC {ℓ} {u} (loc s) g r j = lm (λ n → r (iter (s g) (z0 ℓ u) n) j)

Ψ  : (ℓ : Lv) → T ℓ → Base → Base
ΨE : (ℓ : Lv) (e : E ℓ) → Em ℓ e → Base → Base
Ψ ℓ zr         B = B
Ψ ℓ (sc y)     B = λ j → S (Ψ ℓ y B j)
Ψ ℓ (lm g)     B = λ j → lm (λ n → Ψ ℓ (g n) B j)
Ψ ℓ (Lm u g)   B = LimC (cls ℓ u) g (λ z → Ψ ℓ (g z) B)
Ψ ℓ (up x e y) B = ΨE ℓ e y (Ψ ℓ x B)
ΨE (su ℓ)   _ y = Ψ ℓ y
ΨE (li f)   n y = Ψ (f n) y
ΨE (Om a f) c y = Ψ (f c) y
```

嵌入一致: 定义等式.

```agda
up-Om : ∀ a f x c y B → Ψ (Om a f) (up x c y) B ≡ Ψ (f c) y (Ψ (Om a f) x B)
up-Om a f x c y B = refl

up-li : ∀ f x n y B → Ψ (li f) (up x n y) B ≡ Ψ (f n) y (Ψ (li f) x B)
up-li f x n y B = refl

up-su : ∀ ℓ x y B → Ψ (su ℓ) (up x tt y) B ≡ Ψ ℓ y (Ψ (su ℓ) x B)
up-su ℓ x y B = refl
```

## 不降底与单调

```agda
module _ {j : ℕ} where
  open O (fin j)

  LimC-infl : ∀ {ℓ u} (c : Cls ℓ u) g r {b} → b ≤ r (z0 ℓ u) j → b ≤ LimC c g r j
  LimC-infl (abs k to e) g r {b} p with slot k j
  ... | just (v , bk , e′) = ≤L (subst (λ w → b ≤ r w j) (sym (trans (cong to e′) e)) p)
  ... | nothing            = ≤l (subst (λ w → b ≤ r w j) (sym e) p)
  LimC-infl (loc s) g r p = ≤l p

  LimC-mono : ∀ {ℓ u} (c : Cls ℓ u) g g′ r r′ → r (z0 ℓ u) j ≤ r′ (z0 ℓ u) j → LimC c g r j ≤ LimC c g′ r′ j
  LimC-mono (abs k to e) g g′ r r′ p with slot k j
  ... | just (v , bk , e′) = L≤L (subst (λ w → r w j ≤ r′ w j) (sym (trans (cong to e′) e)) p)
  ... | nothing            = l≤l (subst (λ w → r w j ≤ r′ w j) (sym e) p)
  LimC-mono (loc s) g g′ r r′ p = l≤l p

infl  : ∀ ℓ y B j {b} → Le (fin j) b (B j) → Le (fin j) b (Ψ ℓ y B j)
inflE : ∀ ℓ e y B j {b} → Le (fin j) b (B j) → Le (fin j) b (ΨE ℓ e y B j)
infl ℓ zr         B j p = p
infl ℓ (sc y)     B j p = O.≤S (fin j) (infl ℓ y B j p)
infl ℓ (lm g)     B j p = Ord.≤l (infl ℓ (g 0) B j p)
infl ℓ (Lm u g)   B j p = LimC-infl (cls ℓ u) g (λ z → Ψ ℓ (g z) B) (infl ℓ (g (z0 ℓ u)) B j p)
infl ℓ (up x e y) B j p = inflE ℓ e y (Ψ ℓ x B) j (infl ℓ x B j p)
inflE (su ℓ)   _ y B j p = infl ℓ y B j p
inflE (li f)   n y B j p = infl (f n) y B j p
inflE (Om a f) c y B j p = infl (f c) y B j p

_≤ᴮ_ : Base → Base → Set
B ≤ᴮ B′ = ∀ j → Le (fin j) (B j) (B′ j)

mono  : ∀ ℓ {x y} → Le ℓ x y → ∀ {B B′} → B ≤ᴮ B′ → Ψ ℓ x B ≤ᴮ Ψ ℓ y B′
monoE : ∀ ℓ e y {B B′} → B ≤ᴮ B′ → ΨE ℓ e y B ≤ᴮ ΨE ℓ e y B′
mono ℓ (Ord.z≤ {a = a}) {B′ = B′} q j = infl ℓ a B′ j (q j)
mono ℓ (Ord.s≤s p) q j = O.S-mono (fin j) (mono ℓ p q j)
mono ℓ (Ord.≤s p)  q j = O.≤S (fin j) (mono ℓ p q j)
mono ℓ (Ord.≤l p)  q j = Ord.≤l (mono ℓ p q j)
mono ℓ (Ord.l≤l p) q j = Ord.l≤l (mono ℓ p q j)
mono ℓ (Ord.≤L {u = u} {g = g} p) {B′ = B′} q j =
  LimC-infl (cls ℓ u) g (λ z → Ψ ℓ (g z) B′) (mono ℓ p q j)
mono ℓ (Ord.L≤L {u = u} {f = f} {g = g} p) {B = B} {B′ = B′} q j =
  LimC-mono (cls ℓ u) f g (λ z → Ψ ℓ (f z) B) (λ z → Ψ ℓ (g z) B′) (mono ℓ p q j)
mono ℓ (Ord.≤u {x = x} {e = e} {y = y} p) {B′ = B′} q j =
  inflE ℓ e y (Ψ ℓ x B′) j (mono ℓ p q j)
mono ℓ (Ord.u≤u {e = e} {y = y} p) q j = monoE ℓ e y (mono ℓ p q) j
monoE (su ℓ)   _ y q = mono ℓ (O.≤-refl ℓ y) q
monoE (li f)   n y q = mono (f n) (O.≤-refl (f n) y) q
monoE (Om a f) c y q = mono (f c) (O.≤-refl (f c) y) q
```

## 起始的底与非零

起始的底 `B°`: 第 0 层是一, 第 j+1 层是 "一再加上第 j 层的每棵树" 的分支 (该层的顶码).

```agda
B° : Base
B° zero    = one
B° (suc j) = Lm (inj₁ tt) (λ ζ → up one tt ζ)

B°-nz : ∀ j → Le (fin j) one (B° j)
B°-nz zero    = Ord.s≤s Ord.z≤
B°-nz (suc j) = Ord.≤L (Ord.≤u (Ord.s≤s Ord.z≤))

nz : ∀ ℓ y j → Le (fin j) one (Ψ ℓ y B° j)
nz ℓ y j = infl ℓ y B° j (B°-nz j)
```
