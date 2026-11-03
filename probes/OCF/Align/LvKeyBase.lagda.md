# 不带标签的层号: 键就是节点自己 (底座)

> 底座, 不含记号. 结论写在 [LvKey](LvKey.lagda.md). 由 [UniformLvBase](UniformLvBase.lagda.md) 改写: `lcl` 不再带 $\mathbb N$ 标签. 三件事换了: 世界是一张**表** (`Ents`), 按节点 (模 `≈`) 查, 查表是一个关系, 不做测试; 节点的**位置** `Cp`; 两个节点是否同一由 `kdec` 回答, 只读字面证据.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKeyBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑;
   ≅ᴵ-refl; ≅ᴵ-sym; ≅ᴵ-trans; <ᴵ-trans; <ᴵ-dec; ⊑ᴵ-trans; ⊑ᴵ-refl; Sim→⊑ᴵ)
open import OCF.Align.InaccFloorBase using (≺→⊑ᴵ; ≅→⊑ᴵ)
```

## §1 层号, 路径, 位置

`lcl g`: $\sup_{\eta<\Omega}g\,\eta$. 没有标签. 路径 `a <ᴸ c` 与 [UniformLvBase](UniformLvBase.lagda.md) 同形. 位置 `Cp a c`: $a$ 作为子项出现在 $c$ 的哪里; 路径 $k<c$ 就是 `suc k` 的位置再走一步 (`toCp`). 键是 `Cp (lcl g) c`.

```agda
data LI : Set where
  zero : LI
  base : LI
  suc  : LI → LI
  lim  : (ℕ → LI) → LI
  lcl  : (Ordᴵ → LI) → LI

one : Ordᴵ
one = suc zero

infix 4 _<ᴸ_
data _<ᴸ_ : LI → LI → Set where
  zero : ∀ {a} → a <ᴸ suc a
  suc  : ∀ {a b} → a <ᴸ b → a <ᴸ suc b
  lim  : ∀ {a f} n → a <ᴸ f n → a <ᴸ lim f
  fst  : ∀ {a g} → a <ᴸ g one → a <ᴸ lcl g
  bra  : ∀ {a g} η → a <ᴸ g η → a <ᴸ lcl g

data Cp : LI → LI → Set where
  self : ∀ {c} → Cp c c
  suc  : ∀ {a b} → Cp a b → Cp a (suc b)
  lim  : ∀ {a f} n → Cp a (f n) → Cp a (lim f)
  fst  : ∀ {a g} → Cp a (g one) → Cp a (lcl g)
  bra  : ∀ {a g} η → Cp a (g η) → Cp a (lcl g)

-- 接上: q 在 a 里, p 把 a 放进 b
infixr 9 _⊙_
_⊙_ : ∀ {k a b} → Cp a b → Cp k a → Cp k b
self    ⊙ q = q
suc p   ⊙ q = suc (p ⊙ q)
lim n p ⊙ q = lim n (p ⊙ q)
fst p   ⊙ q = fst (p ⊙ q)
bra η p ⊙ q = bra η (p ⊙ q)

toCp : ∀ {k c} → k <ᴸ c → Cp k c
toCp zero      = suc self
toCp (suc r)   = suc (toCp r)
toCp (lim n r) = lim n (toCp r)
toCp (fst r)   = fst (toCp r)
toCp (bra η r) = bra η (toCp r)
```

## §2 结构相等: 一个部分等价

```agda
infix 4 _≈_
data _≈_ : LI → LI → Set where
  z≈ : zero ≈ zero
  b≈ : base ≈ base
  s≈ : ∀ {a b} → a ≈ b → suc a ≈ suc b
  l≈ : ∀ {f g} → (∀ n → f n ≈ g n) → lim f ≈ lim g
  o≈ : ∀ {g g′} → (∀ η η′ → η ≅ᴵ η′ → g η ≈ g′ η′) → lcl g ≈ lcl g′

≈-sym : ∀ {a b} → a ≈ b → b ≈ a
≈-sym z≈     = z≈
≈-sym b≈     = b≈
≈-sym (s≈ e) = s≈ (≈-sym e)
≈-sym (l≈ h) = l≈ (λ n → ≈-sym (h n))
≈-sym (o≈ h) = o≈ (λ η η′ d → ≈-sym (h η′ η (≅ᴵ-sym d)))

≈-trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
≈-trans z≈     z≈      = z≈
≈-trans b≈     b≈      = b≈
≈-trans (s≈ e) (s≈ e′) = s≈ (≈-trans e e′)
≈-trans (l≈ h) (l≈ h′) = l≈ (λ n → ≈-trans (h n) (h′ n))
≈-trans (o≈ h) (o≈ h′) = o≈ (λ η η′ d → ≈-trans (h η η (≅ᴵ-refl η)) (h′ η η′ d))

≈-reflˡ : ∀ {a b} → a ≈ b → a ≈ a
≈-reflˡ e = ≈-trans e (≈-sym e)

≈-reflʳ : ∀ {a b} → a ≈ b → b ≈ b
≈-reflʳ e = ≈-trans (≈-sym e) e

-- 合法的层号的子项也合法
selfAt : ∀ {a c} → c ≈ c → Cp a c → a ≈ a
selfAt e self = e
selfAt (s≈ e) (suc p) = selfAt e p
selfAt (l≈ h) (lim n p) = selfAt (h n) p
selfAt (o≈ h) (fst p) = selfAt (h one one (≅ᴵ-refl one)) p
selfAt (o≈ h) (bra η p) = selfAt (h η η (≅ᴵ-refl η)) p
```

## §3 严格子项不与自己相等

结构递归, 没有用任何判定. 这就是 "一个节点与它下面的节点不是同一个键" 的全部内容.

```agda
data Strict (k : LI) : LI → Set where
  st-suc : ∀ {b} → Cp k b → Strict k (suc b)
  st-lim : ∀ {f} n → Cp k (f n) → Strict k (lim f)
  st-lcl : ∀ {g} x → Cp k (g x) → Strict k (lcl g)

st⊙ : ∀ {k a b} → Cp a b → Strict k a → Strict k b
stCp : ∀ {k a} → Strict k a → Cp k a
stCp (st-suc r)   = suc r
stCp (st-lim n r) = lim n r
stCp (st-lcl x r) = bra x r

st⊙ self s = s
st⊙ (suc p) s = st-suc (p ⊙ stCp s)
st⊙ (lim n p) s = st-lim n (p ⊙ stCp s)
st⊙ (fst p) s = st-lcl one (p ⊙ stCp s)
st⊙ (bra η p) s = st-lcl η (p ⊙ stCp s)

irr : ∀ a {k} → Strict k a → a ≈ k → ⊥
irr (suc a) (st-suc r) (s≈ e) = irr a (st⊙ r (st-suc self)) e
irr (lim f) (st-lim n r) (l≈ h) = irr (f n) (st⊙ r (st-lim n self)) (h n)
irr (lcl g) (st-lcl x r) (o≈ h) = irr (g x) (st⊙ r (st-lcl x self)) (h x x (≅ᴵ-refl x))
```

## §4 世界是一张表

`at E y ℓ`: 在表 $E$ 里, 节点 $y$ 的界是 $\ell$. 这是**关系**: 新表 `E ▸ κ , X` 在 $y\approx\kappa$ 处是 $X$, 在 $y\not\approx\kappa$ 处沿用旧表. 写下这个定义不需要判定 $y\approx\kappa$, 所以没有任何判定藏在世界的更新里 (`dec-A→WLPO`, `no-uniform` 说这个判定对原始层号做不到). 代价是: 只有带证据的查询才有答案 (`Bel`), 而证据的来源是树的地板.

`∅ d`: 一切节点的界都是 $d$.

```agda
infixl 5 _▸_,_
data Ents : Set where
  ∅      : Ordᴵ → Ents
  _▸_,_  : Ents → LI → Ordᴵ → Ents

at : Ents → LI → Ordᴵ → Set
at (∅ d)       y ℓ = ℓ ≡ d
at (E ▸ κ , X) y ℓ = ((y ≈ κ) × (ℓ ≡ X)) ⊎ (((y ≈ κ) → ⊥) × at E y ℓ)

at-resp : ∀ {E y y′ ℓ} → y ≈ y′ → at E y ℓ → at E y′ ℓ
at-resp {∅ d} e a = a
at-resp {E ▸ κ , X} e (inj₁ (d , r)) = inj₁ (≈-trans (≈-sym e) d , r)
at-resp {E ▸ κ , X} e (inj₂ (n , a)) = inj₂ ((λ d → n (≈-trans e d)) , at-resp {E} e a)

at-uq : ∀ {E y y′ ℓ ℓ′} → y ≈ y′ → at E y ℓ → at E y′ ℓ′ → ℓ ≡ ℓ′
at-uq {∅ d} e refl refl = refl
at-uq {E ▸ κ , X} e (inj₁ (_ , refl)) (inj₁ (_ , refl)) = refl
at-uq {E ▸ κ , X} e (inj₁ (d , _)) (inj₂ (n , _)) = ⊥-elim (n (≈-trans (≈-sym e) d))
at-uq {E ▸ κ , X} e (inj₂ (n , _)) (inj₁ (d , _)) = ⊥-elim (n (≈-trans e d))
at-uq {E ▸ κ , X} e (inj₂ (_ , a)) (inj₂ (_ , b)) = at-uq {E} e a b

OkE : Ents → Set
OkE (∅ d)       = zero <ᴵ d
OkE (E ▸ κ , X) = OkE E × (zero <ᴵ X)

at-pos : ∀ {E y ℓ} → OkE E → at E y ℓ → zero <ᴵ ℓ
at-pos {∅ d} z refl = z
at-pos {E ▸ κ , X} (_ , z) (inj₁ (_ , refl)) = z
at-pos {E ▸ κ , X} (o , _) (inj₂ (_ , a)) = at-pos {E} o a

Bel : Ents → LI → Ordᴵ → Set
Bel E y η = Σ Ordᴵ λ ℓ → at E y ℓ × (η <ᴵ ℓ)

Bel-resp : ∀ {E y y′ η} → y ≈ y′ → Bel E y η → Bel E y′ η
Bel-resp {E} e (ℓ , a , q) = ℓ , at-resp {E} e a , q

-- 同一节点上的两个分支有公共的字面上界, 所以 `<ᴵ-dec` 可用
bel-dec : ∀ {E y a b} → y ≈ y → Bel E y a → Bel E y b → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
bel-dec {E} e (ℓ , a , p) (ℓ′ , b , q) with at-uq {E} e a b
... | refl = <ᴵ-dec p q

-- 分支与 0 的比较: 第一支 `fst` 只要这个
bel-zero : ∀ {E y a} → OkE E → Bel E y a → zero ≺ᴵ a ⊎ a ≺ᴵ zero ⊎ zero ≅ᴵ a
bel-zero {E} ok (ℓ , a , q) = <ᴵ-dec (at-pos {E} ok a) q

Adm : Ents → ∀ {a c} → a <ᴸ c → Set
Adm E zero      = ⊤
Adm E (suc r)   = Adm E r
Adm E (lim n r) = Adm E r
Adm E (fst r)   = Adm E r
Adm E (bra {g = g} η r) = Bel E (lcl g) η × Adm E r

AdmC : Ents → ∀ {a c} → Cp a c → Set
AdmC E self      = ⊤
AdmC E (suc r)   = AdmC E r
AdmC E (lim n r) = AdmC E r
AdmC E (fst r)   = AdmC E r
AdmC E (bra {g = g} η r) = Bel E (lcl g) η × AdmC E r

adm⊙ : ∀ {E k a b} (p : Cp a b) {q : Cp k a} → AdmC E p → AdmC E q → AdmC E (p ⊙ q)
adm⊙ self      _ y = y
adm⊙ (suc p)   x y = adm⊙ p x y
adm⊙ (lim n p) x y = adm⊙ p x y
adm⊙ (fst p)   x y = adm⊙ p x y
adm⊙ (bra η p) (u , x) y = u , adm⊙ p x y

admTo : ∀ {E k c} (r : k <ᴸ c) → Adm E r → AdmC E (toCp r)
admTo zero      _ = tt
admTo (suc r)   a = admTo r a
admTo (lim n r) a = admTo r a
admTo (fst r)   a = admTo r a
admTo (bra η r) (u , a) = u , admTo r a
```

## §5 路径与键的搬运

`a ≺⟨ A ⟩ b`: 模 `≈` 的字面前驱, 带对一切表的转移. `a ⊑ b`: 路径搬运. `a ⊑ᴷ b`: **节点**搬运: $a$ 的每个 `lcl` 子项模 `≈` 也在 $b$ 里. 后者是新的义务, 它只对 `lcl` 问, 不对 `lim` 问: `L ⊞ (lim f)` 不必是 `L ⊞ (lim f′)` 的子项.

```agda
record _≺⟨_⟩_ (a : LI) (A : Ents → Set) (b : LI) : Set where
  constructor viaᴸ
  field
    {rep} : LI
    eqv   : a ≈ rep
    pth   : rep <ᴸ b
    trf   : ∀ E → A E → Adm E pth
open _≺⟨_⟩_ public

infix 4 _⊑_ _⊑ᴷ_ _⊴_
_⊑_ : LI → LI → Set
a ⊑ b = ∀ {k} (r : k <ᴸ a) → k ≺⟨ (λ E → Adm E r) ⟩ b

record Kv (g : Ordᴵ → LI) (A : Ents → Set) (b : LI) : Set where
  constructor viaᴷ
  field
    {krep} : Ordᴵ → LI
    keqv   : lcl g ≈ lcl krep
    kpth   : Cp (lcl krep) b
    ktrf   : ∀ E → A E → AdmC E kpth
open Kv public

_⊑ᴷ_ : LI → LI → Set
a ⊑ᴷ b = ∀ {g} (p : Cp (lcl g) a) → Kv g (λ E → AdmC E p) b

_⊴_ : LI → LI → Set
a ⊴ b = (a ⊑ b) × (a ⊑ᴷ b)

≈-move : ∀ {a b} → a ≈ b → a ⊑ b
≈-move (s≈ e) zero = viaᴸ e zero (λ _ _ → tt)
≈-move (s≈ e) (suc r) with ≈-move e r
... | viaᴸ d p t = viaᴸ d (suc p) t
≈-move (l≈ h) (lim n r) with ≈-move (h n) r
... | viaᴸ d p t = viaᴸ d (lim n p) t
≈-move (o≈ h) (fst r) with ≈-move (h one one (≅ᴵ-refl one)) r
... | viaᴸ d p t = viaᴸ d (fst p) t
≈-move (o≈ h) (bra η r) with ≈-move (h η η (≅ᴵ-refl η)) r
... | viaᴸ d p t = viaᴸ d (bra η p) (λ E u → Bel-resp {E} (o≈ h) (proj₁ u) , t E (proj₂ u))

≈-moveᴷ : ∀ {a b} → a ≈ b → a ⊑ᴷ b
≈-moveᴷ (o≈ h) self = viaᴷ (o≈ h) self (λ _ _ → tt)
≈-moveᴷ (s≈ e) (suc r) with ≈-moveᴷ e r
... | viaᴷ d p t = viaᴷ d (suc p) t
≈-moveᴷ (l≈ h) (lim n r) with ≈-moveᴷ (h n) r
... | viaᴷ d p t = viaᴷ d (lim n p) t
≈-moveᴷ (o≈ h) (fst r) with ≈-moveᴷ (h one one (≅ᴵ-refl one)) r
... | viaᴷ d p t = viaᴷ d (fst p) t
≈-moveᴷ (o≈ h) (bra η r) with ≈-moveᴷ (h η η (≅ᴵ-refl η)) r
... | viaᴷ d p t = viaᴷ d (bra η p) (λ E u → Bel-resp {E} (o≈ h) (proj₁ u) , t E (proj₂ u))

≈-⊴ : ∀ {a b} → a ≈ b → a ⊴ b
≈-⊴ e = ≈-move e , ≈-moveᴷ e
```

## §6 合法性

`WF`: 单调不看表. 与 [UniformLvBase](UniformLvBase.lagda.md) 同形, 把 `⊑` 换成 `⊴`.

```agda
WF : LI → Set
WF zero    = ⊤
WF base    = ⊤
WF (suc k) = WF k
WF (lim f) = (∀ n → f n ⊴ f (suc n)) × (∀ n → WF (f n))
WF (lcl g) = (∀ {η η′} → η ⊑ᴵ η′ → g η ⊴ g η′) × (∀ {η} → one ⊑ᴵ η → g one ⊴ g η) × (∀ {η} → η ≅ᴵ zero → g η ⊴ g one) × (∀ η → WF (g η))

stepsᴸ : ∀ {f : ℕ → LI} → (∀ n → f n ⊴ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ f m
stepsᴸ s zero r = proj₁ (s _) r
stepsᴸ {f} s (suc {n} {m} q) r with stepsᴸ s q r
... | viaᴸ d p t with proj₁ (s _) p
...   | viaᴸ d′ p′ t′ = viaᴸ (≈-trans d d′) p′ (λ E u → t′ E (t E u))

stepsᴷ : ∀ {f : ℕ → LI} → (∀ n → f n ⊴ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ᴷ f m
stepsᴷ s zero r = proj₂ (s _) r
stepsᴷ {f} s (suc {n} {m} q) r with stepsᴷ s q r
... | viaᴷ d p t with proj₂ (s _) p
...   | viaᴷ d′ p′ t′ = viaᴷ (≈-trans d d′) p′ (λ E u → t′ E (t E u))
```

## §7 路径的三歧

与 [UniformLvBase](UniformLvBase.lagda.md) §4 同形. `lcl` 处读 `bel-dec`.

```agda
data Tri {a b c c′ : LI} (p : a <ᴸ c) (q : b <ᴸ c′) : Set where
  tlt : a ≺⟨ (λ E → Adm E p) ⟩ b → Tri p q
  tgt : b ≺⟨ (λ E → Adm E q) ⟩ a → Tri p q
  teq : a ≈ b → Tri p q

shL : ∀ {a a′ b c₁ c₂ c₃} {p : a <ᴸ c₁} {p′ : a′ <ᴸ c₂} {q : b <ᴸ c₃} → a ≈ a′ → (∀ E → Adm E p → Adm E p′) → Tri p′ q → Tri p q
shL e t (tlt (viaᴸ d s u)) = tlt (viaᴸ (≈-trans e d) s (λ E x → u E (t E x)))
shL e t (tgt (viaᴸ d s u)) with ≈-move (≈-sym e) s
... | viaᴸ d′ s′ u′ = tgt (viaᴸ (≈-trans d d′) s′ (λ E x → u′ E (u E x)))
shL e t (teq d) = teq (≈-trans e d)

shR : ∀ {a b b′ c₁ c₂ c₃} {p : a <ᴸ c₁} {q : b <ᴸ c₂} {q′ : b′ <ᴸ c₃} → b ≈ b′ → (∀ E → Adm E q → Adm E q′) → Tri p q′ → Tri p q
shR e t (tgt (viaᴸ d s u)) = tgt (viaᴸ (≈-trans e d) s (λ E x → u E (t E x)))
shR e t (tlt (viaᴸ d s u)) with ≈-move (≈-sym e) s
... | viaᴸ d′ s′ u′ = tlt (viaᴸ (≈-trans d d′) s′ (λ E x → u′ E (u E x)))
shR e t (teq d) = teq (≈-trans d (≈-sym e))

rdx : ∀ {a b c₁ c₂ c₃ c₄} {p : a <ᴸ c₁} {p′ : a <ᴸ c₂} {q : b <ᴸ c₃} {q′ : b <ᴸ c₄} → (∀ E → Adm E p → Adm E p′) → (∀ E → Adm E q → Adm E q′) → Tri p′ q′ → Tri p q
rdx f g (tlt (viaᴸ d s u)) = tlt (viaᴸ d s (λ E x → u E (f E x)))
rdx f g (tgt (viaᴸ d s u)) = tgt (viaᴸ d s (λ E x → u E (g E x)))
rdx f g (teq d) = teq d

<-dec : ∀ {c} → WF c → c ≈ c → ∀ {a b} (p : a <ᴸ c) (q : b <ᴸ c) (E : Ents) → OkE E → Adm E p → Adm E q → Tri p q
<-dec {suc k} w (s≈ e) zero zero E z _ _ = teq e
<-dec {suc k} w (s≈ e) zero (suc q) E z _ _ with ≈-move e q
... | viaᴸ d s t = tgt (viaᴸ d s t)
<-dec {suc k} w (s≈ e) (suc p) zero E z _ _ with ≈-move e p
... | viaᴸ d s t = tlt (viaᴸ d s t)
<-dec {suc k} w (s≈ e) (suc p) (suc q) E z ap aq = rdx {p′ = p} {q′ = q} (λ _ x → x) (λ _ x → x) (<-dec w e p q E z ap aq)
<-dec {lim f} (st , w) (l≈ e) (lim n p) (lim m q) E z ap aq with <ᴺ-dec n m
... | injᵃ n<m with stepsᴸ st n<m p
...   | viaᴸ d p′ t = shL d (λ E′ x → t E′ x) (rdx (λ _ x → x) (λ _ x → x) (<-dec (w m) (e m) p′ q E z (t E ap) aq))
<-dec {lim f} (st , w) (l≈ e) (lim n p) (lim m q) E z ap aq | injᵇ m<n with stepsᴸ st m<n q
...   | viaᴸ d q′ t = shR d (λ E′ x → t E′ x) (rdx (λ _ x → x) (λ _ x → x) (<-dec (w n) (e n) p q′ E z ap (t E aq)))
<-dec {lim f} (st , w) (l≈ e) (lim n p) (lim _ q) E z ap aq | injᶜ refl = rdx {p′ = p} {q′ = q} (λ _ x → x) (λ _ x → x) (<-dec (w n) (e n) p q E z ap aq)
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (fst p) (fst q) E z ap aq = rdx {p′ = p} {q′ = q} (λ _ x → x) (λ _ x → x) (<-dec (w one) (e one one (≅ᴵ-refl one)) p q E z ap aq)
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (fst p) (bra y q) E z ap (ly , aq) with bel-zero {E} z ly
... | injᵃ (via d s) with proj₁ (up₁ (s⊑ d s)) p
...   | viaᴸ d′ p′ t = shL d′ (λ E′ x → t E′ x) (rdx (λ _ x → x) (λ _ x → proj₂ x) (<-dec (w y) (e y y (≅ᴵ-refl y)) p′ q E z (t E ap) aq))
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (fst p) (bra y q) E z ap (ly , aq) | injᵇ (via d ())
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (fst p) (bra y q) E z ap (ly , aq) | injᶜ d with proj₁ (dn₀ (≅ᴵ-sym d)) q
...   | viaᴸ d′ q′ t = shR d′ (λ E′ x → t E′ (proj₂ x)) (rdx (λ _ x → x) (λ _ x → x) (<-dec (w one) (e one one (≅ᴵ-refl one)) p q′ E z ap (t E aq)))
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (fst q) E z (lx , ap) aq with bel-zero {E} z lx
... | injᵃ (via d s) with proj₁ (up₁ (s⊑ d s)) q
...   | viaᴸ d′ q′ t = shR d′ (λ E′ u → t E′ u) (rdx (λ _ u → proj₂ u) (λ _ u → u) (<-dec (w x) (e x x (≅ᴵ-refl x)) p q′ E z ap (t E aq)))
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (fst q) E z (lx , ap) aq | injᵇ (via d ())
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (fst q) E z (lx , ap) aq | injᶜ d with proj₁ (dn₀ (≅ᴵ-sym d)) p
...   | viaᴸ d′ p′ t = shL d′ (λ E′ u → t E′ (proj₂ u)) (rdx (λ _ u → u) (λ _ u → u) (<-dec (w one) (e one one (≅ᴵ-refl one)) p′ q E z (t E ap) aq))
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (bra y q) E z (lx , ap) (ly , aq) with bel-dec {E} (o≈ e) lx ly
... | injᵃ r with proj₁ (dir (≺→⊑ᴵ r)) p
...   | viaᴸ d′ p′ t = shL d′ (λ E′ u → t E′ (proj₂ u)) (rdx (λ _ u → u) (λ _ u → proj₂ u) (<-dec (w y) (e y y (≅ᴵ-refl y)) p′ q E z (t E ap) aq))
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (bra y q) E z (lx , ap) (ly , aq) | injᵇ r with proj₁ (dir (≺→⊑ᴵ r)) q
...   | viaᴸ d′ q′ t = shR d′ (λ E′ u → t E′ (proj₂ u)) (rdx (λ _ u → proj₂ u) (λ _ u → u) (<-dec (w x) (e x x (≅ᴵ-refl x)) p q′ E z ap (t E aq)))
<-dec {lcl g} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (bra y q) E z (lx , ap) (ly , aq) | injᶜ d with proj₁ (dir (≅→⊑ᴵ d)) p
...   | viaᴸ d′ p′ t = shL d′ (λ E′ u → t E′ (proj₂ u)) (rdx (λ _ u → u) (λ _ u → proj₂ u) (<-dec (w y) (e y y (≅ᴵ-refl y)) p′ q E z (t E ap) aq))
```

## §8 键的判定: 只读证据

**定理 `kdec`.** 给两个键的位置, 它们在同一张表里的证据, 与层号的 `WF`: 两个节点模 `≈` 相同或不相同. 对 $c$ 结构递归, 与 `<-dec` 同一个骨架: 比较两个分支用 `bel-dec`, 然后把小分支的键搬到大分支 (`⊑ᴷ`). 节点与它下面的节点不同是 `irr`. 没有全局判定, 没有对原始层号的测试. 与 `¬tri`, `dec-A→WLPO`, `no-uniform` 都不矛盾: 输入是字面证据.

```agda
Dec′ : Set → Set
Dec′ A = A ⊎ (A → ⊥)

decL : ∀ {a a′ b} → a ≈ a′ → Dec′ (a′ ≈ b) → Dec′ (a ≈ b)
decL e (inj₁ d) = inj₁ (≈-trans e d)
decL e (inj₂ n) = inj₂ (λ d → n (≈-trans (≈-sym e) d))

decR : ∀ {a b b′} → b ≈ b′ → Dec′ (a ≈ b′) → Dec′ (a ≈ b)
decR e (inj₁ d) = inj₁ (≈-trans d (≈-sym e))
decR e (inj₂ n) = inj₂ (λ d → n (≈-trans d e))

kdec : ∀ {c} → WF c → c ≈ c → ∀ {g g′} (p : Cp (lcl g) c) (q : Cp (lcl g′) c) (E : Ents) → OkE E → AdmC E p → AdmC E q → Dec′ (lcl g ≈ lcl g′)
kdec {lcl g₀} wf e self self E z _ _ = inj₁ e
kdec {lcl g₀} wf e self (fst q) E z _ _ = inj₂ (irr (lcl g₀) (st-lcl one q))
kdec {lcl g₀} wf e self (bra y q) E z _ _ = inj₂ (irr (lcl g₀) (st-lcl y q))
kdec {lcl g₀} wf e (fst p) self E z _ _ = inj₂ (λ d → irr (lcl g₀) (st-lcl one p) (≈-sym d))
kdec {lcl g₀} wf e (bra x p) self E z _ _ = inj₂ (λ d → irr (lcl g₀) (st-lcl x p) (≈-sym d))
kdec {suc k} w (s≈ e) (suc p) (suc q) E z ap aq = kdec w e p q E z ap aq
kdec {lim f} (st , w) (l≈ e) (lim n p) (lim m q) E z ap aq with <ᴺ-dec n m
... | injᵃ n<m with stepsᴷ st n<m p
...   | viaᴷ d p′ t = decL d (kdec (w m) (e m) p′ q E z (t E ap) aq)
kdec {lim f} (st , w) (l≈ e) (lim n p) (lim m q) E z ap aq | injᵇ m<n with stepsᴷ st m<n q
...   | viaᴷ d q′ t = decR d (kdec (w n) (e n) p q′ E z ap (t E aq))
kdec {lim f} (st , w) (l≈ e) (lim n p) (lim _ q) E z ap aq | injᶜ refl = kdec (w n) (e n) p q E z ap aq
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (fst p) (fst q) E z ap aq = kdec (w one) (e one one (≅ᴵ-refl one)) p q E z ap aq
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (fst p) (bra y q) E z ap (ly , aq) with bel-zero {E} z ly
... | injᵃ (via d s) with proj₂ (up₁ (s⊑ d s)) p
...   | viaᴷ d′ p′ t = decL d′ (kdec (w y) (e y y (≅ᴵ-refl y)) p′ q E z (t E ap) aq)
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (fst p) (bra y q) E z ap (ly , aq) | injᵇ (via d ())
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (fst p) (bra y q) E z ap (ly , aq) | injᶜ d with proj₂ (dn₀ (≅ᴵ-sym d)) q
...   | viaᴷ d′ q′ t = decR d′ (kdec (w one) (e one one (≅ᴵ-refl one)) p q′ E z ap (t E aq))
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (fst q) E z (lx , ap) aq with bel-zero {E} z lx
... | injᵃ (via d s) with proj₂ (up₁ (s⊑ d s)) q
...   | viaᴷ d′ q′ t = decR d′ (kdec (w x) (e x x (≅ᴵ-refl x)) p q′ E z ap (t E aq))
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (fst q) E z (lx , ap) aq | injᵇ (via d ())
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (fst q) E z (lx , ap) aq | injᶜ d with proj₂ (dn₀ (≅ᴵ-sym d)) p
...   | viaᴷ d′ p′ t = decL d′ (kdec (w one) (e one one (≅ᴵ-refl one)) p′ q E z (t E ap) aq)
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (bra y q) E z (lx , ap) (ly , aq) with bel-dec {E} (o≈ e) lx ly
... | injᵃ r with proj₂ (dir (≺→⊑ᴵ r)) p
...   | viaᴷ d′ p′ t = decL d′ (kdec (w y) (e y y (≅ᴵ-refl y)) p′ q E z (t E ap) aq)
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (bra y q) E z (lx , ap) (ly , aq) | injᵇ r with proj₂ (dir (≺→⊑ᴵ r)) q
...   | viaᴷ d′ q′ t = decR d′ (kdec (w x) (e x x (≅ᴵ-refl x)) p q′ E z ap (t E aq))
kdec {lcl g₀} (dir , up₁ , dn₀ , w) (o≈ e) (bra x p) (bra y q) E z (lx , ap) (ly , aq) | injᶜ d with proj₂ (dir (≅→⊑ᴵ d)) p
...   | viaᴷ d′ p′ t = decL d′ (kdec (w y) (e y y (≅ᴵ-refl y)) p′ q E z (t E ap) aq)
```

## §9 不看语法的层号函数

与 [UniformLvBase](UniformLvBase.lagda.md) §5 同形. `times L = lcl (L ⊞_)`, **没有 `ht`**. `⊞` 不产生新节点, 所以节点搬运是免费的: 剥掉 `suc`, `lim` 回到 $L$ (`stripK`), 再放进目标 (`inLK`), 对任何 $a,b$ 成立, 不要 $a\sqsubseteq b$.

```agda
infixl 6 _⊞_
_⊞_ : LI → Ordᴵ → LI
L ⊞ zero    = L
L ⊞ suc a   = suc (L ⊞ a)
L ⊞ lim f s = lim (λ n → L ⊞ f n)

times : LI → LI
times L = lcl (L ⊞_)

≈⊞ : ∀ {L L′ a b} → L ≈ L′ → a ≅ᴵ b → (L ⊞ a) ≈ (L′ ⊞ b)
≈⊞ e z≅     = e
≈⊞ e (s≅ d) = s≈ (≈⊞ e d)
≈⊞ e (l≅ h) = l≈ (λ n → ≈⊞ e (h n))

≈times : ∀ {L} → L ≈ L → times L ≈ times L
≈times e = o≈ (λ η η′ d → ≈⊞ e d)

stripK : ∀ L a {g} (p : Cp (lcl g) (L ⊞ a)) → Σ (Cp (lcl g) L) λ p′ → ∀ E → AdmC E p → AdmC E p′
stripK L zero p = p , (λ _ x → x)
stripK L (suc a) (suc p) = stripK L a p
stripK L (lim f s) (lim n p) = stripK L (f n) p

inLK : ∀ L a {g} (p : Cp (lcl g) L) → Σ (Cp (lcl g) (L ⊞ a)) λ p′ → ∀ E → AdmC E p → AdmC E p′
inLK L zero p = p , (λ _ x → x)
inLK L (suc a) p with inLK L a p
... | p′ , t = suc p′ , t
inLK L (lim f s) p with inLK L (f 0) p
... | p′ , t = lim 0 p′ , t

module Mono (L : LI) (self′ : L ≈ L) where
  inL : ∀ a → L ⊑ (L ⊞ a)
  inL zero      r = ≈-move self′ r
  inL (suc a)   r with inL a r
  ... | viaᴸ d p t = viaᴸ d (suc p) t
  inL (lim f s) r with inL (f 0) r
  ... | viaᴸ d p t = viaᴸ d (lim 0 p) t

  lit⊞ : ∀ {a b} → a <ᴵ b → (L ⊞ a) <ᴸ (L ⊞ b)
  lit⊞ zero      = zero
  lit⊞ (suc q)   = suc (lit⊞ q)
  lit⊞ (lim n q) = lim n (lit⊞ q)

  adm⊞ : ∀ {a b} (q : a <ᴵ b) E → Adm E (lit⊞ q)
  adm⊞ zero      E = tt
  adm⊞ (suc q)   E = adm⊞ q E
  adm⊞ (lim n q) E = adm⊞ q E

  up⊞ : ∀ {a b} → a <ᴵ b → (L ⊞ a) ⊑ (L ⊞ b)
  up⊞ zero      r = viaᴸ (eqv (≈-move (≈⊞ self′ (≅ᴵ-refl _)) r)) (suc (pth (≈-move (≈⊞ self′ (≅ᴵ-refl _)) r))) (trf (≈-move (≈⊞ self′ (≅ᴵ-refl _)) r))
  up⊞ (suc q)   r with up⊞ q r
  ... | viaᴸ d p t = viaᴸ d (suc p) t
  up⊞ (lim n q) r with up⊞ q r
  ... | viaᴸ d p t = viaᴸ d (lim n p) t

  mono⊞ : ∀ {a b} → a ⊑ᴵ b → (L ⊞ a) ⊑ (L ⊞ b)
  mono⊞ {b = b} z⊑ r = inL b r
  mono⊞ (s⊑ e q) zero = viaᴸ (≈⊞ self′ e) (lit⊞ q) (λ E _ → adm⊞ q E)
  mono⊞ (s⊑ e q) (suc r) with ≈-move (≈⊞ self′ e) r
  ... | viaᴸ d p t with up⊞ q p
  ...   | viaᴸ d′ p′ t′ = viaᴸ (≈-trans d d′) p′ (λ E u → t′ E (t E u))
  mono⊞ (l⊑ h) (lim n r) = mono⊞ (h n) r

  monoK⊞ : ∀ a b → (L ⊞ a) ⊑ᴷ (L ⊞ b)
  monoK⊞ a b p with stripK L a p
  ... | p₀ , t₀ with inLK L b p₀
  ...   | p₁ , t₁ = viaᴷ (selfAt self′ p₀) p₁ (λ E u → t₁ E (t₀ E u))

  mono⊴ : ∀ {a b} → a ⊑ᴵ b → (L ⊞ a) ⊴ (L ⊞ b)
  mono⊴ {a} {b} e = mono⊞ e , monoK⊞ a b

  WF-⊞ : WF L → ∀ a → WF (L ⊞ a)
  WF-⊞ w zero      = w
  WF-⊞ w (suc a)   = WF-⊞ w a
  WF-⊞ w (lim f s) = (λ n → mono⊴ (s n)) , (λ n → WF-⊞ w (f n))

  WF-times : WF L → WF (times L)
  WF-times w = mono⊴ , mono⊴ , (λ e → ⊴-of e) , WF-⊞ w
    where
    ⊴-of : ∀ {η} → η ≅ᴵ zero → (L ⊞ η) ⊴ (L ⊞ one)
    ⊴-of e = mono⊴ (⊑ᴵ-trans (≅→⊑ᴵ e) z⊑)

  step-times : L ⊴ times L
  step-times = (λ r → step-p r) , (λ r → step-k r)
    where
    step-p : L ⊑ times L
    step-p r with ≈-move self′ r
    ... | viaᴸ d p t = viaᴸ d (fst (suc p)) t
    step-k : L ⊑ᴷ times L
    step-k r with ≈-moveᴷ self′ r
    ... | viaᴷ d p t = viaᴷ d (fst (suc p)) t

self⊞ : ∀ {L} → L ≈ L → ∀ a → (L ⊞ a) ≈ (L ⊞ a)
self⊞ e zero      = e
self⊞ e (suc a)   = s≈ (self⊞ e a)
self⊞ e (lim f s) = l≈ (λ n → self⊞ e (f n))

Ω·_ : ℕ → LI
Ω· zero        = zero
Ω· suc zero    = base
Ω· suc (suc m) = times (Ω· suc m)

Ω·ω : LI
Ω·ω = lim Ω·_

selfΩ : ∀ m → (Ω· m) ≈ (Ω· m)
selfΩ zero          = z≈
selfΩ (suc zero)    = b≈
selfΩ (suc (suc m)) = ≈times (selfΩ (suc m))

WFΩ : ∀ m → WF (Ω· m)
WFΩ zero          = tt
WFΩ (suc zero)    = tt
WFΩ (suc (suc m)) = Mono.WF-times _ (selfΩ (suc m)) (WFΩ (suc m))

stepΩ : ∀ m → (Ω· m) ⊴ (Ω· suc m)
stepΩ zero          = (λ ()) , (λ ())
stepΩ (suc zero)    = (λ ()) , (λ ())
stepΩ (suc (suc m)) = Mono.step-times _ (selfΩ (suc (suc m)))

WFΩ·ω : WF Ω·ω
WFΩ·ω = stepΩ , WFΩ

selfΩ·ω : Ω·ω ≈ Ω·ω
selfΩ·ω = l≈ selfΩ
```
