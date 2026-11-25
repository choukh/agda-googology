# YiIntr：Carry⁺ 证据进树的归纳—递归骨架

这是独立的平行定义探针，不导入旧 LF，也不把旧证书当新证书。
`lc k c w b t p g` 内置下界的 Lgl、Nested；t、g 的结果仍是同一
内置证据的 LF。k 也取该 LF，所以比原 Carry⁺ 只要求 Reg k 更强。
`Gd` 的坐标合法性增为 Lgl 与 Nested，因此 LF 及 Raw 的 Ω 分支
均只接收带这两项证据的坐标。Raw.lc 本身仍是原始语法，
其下界证据由 Nested 检查，不冒称所有 Raw 都能无证据读回。

根位置改为只涉及部分的 `p : Reach (suc k) t`。
Reach 是相等或有限子树路径的归纳表示，覆盖后继、ℕ支、第一支、
带证据的 Ω 支，不包含 lc.k。没有引用待造结点，亦无 LF 的异层打包相等。
拟对应原 Parts 的含义与充分性见 YiIntrPosition；它是加强条件。

只保留检查类型所需的 Raw／位置／合法性定义，不复制比较与闭包证明。
新增 Nested／NestedLow／NestedKid 及 LglLow 必须进同一块：Gd 现在读取它们。
代码到块末为第一阶段的完整编译对象。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIntrCore where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module G (P : Set) (L : P → Set)
  (Gl : (r : P) → L r → L r → Set)
  (K : Set) (B : K → Set) where
  data R : Set where
    zero : R
    suc  : R → R
    lim  : (ℕ → R) → R
    lc   : (r : P) (c : L r) (t : R)
           (g : (η : L r) → Gl r c η → R) → R
    em   : (i : K) → B i → R
    top  : R

data LF : Set
data Reach : LF → LF → Set
Pre : LF → Set
Low : (x : LF) → Pre x → Set
GdL : (x : LF) (r : Pre x) → Low x r → Low x r → Set
Kid : LF → Set
KidR : (x : LF) → Kid x → Set
Raw : LF → Set
Gd : (k : LF) → Raw k → Raw k → Set
Cp : (y : LF) → Raw y → Raw y → Set
Dn : (y : LF) → Raw y → Raw y → Set
DnK : (y : LF) (i i′ : Kid y) → KidR y i → KidR y i′ → Set
DnT : (y : LF) → Raw y → Set
DnLm : (f : ℕ → LF) (n m : ℕ) → n ≡ m →
  Raw (f n) → Raw (f m) → Set
DnBr : (k : LF) (c : Raw k)
  (g : (η : Raw k) → Gd k c η → LF)
  (x x′ : Σ (Raw k) λ η → Gd k c η) → x ≡ x′ →
  Raw (g (proj₁ x) (proj₂ x)) → Raw (g (proj₁ x′) (proj₂ x′)) → Set
Lgl : (y : LF) → Raw y → Set
LglK : (y : LF) (i : Kid y) → KidR y i → Set
LglLow : (y : LF) (r : Pre y) → Low y r → Set
Nested : (y : LF) → Raw y → Set
NestedLow : (y : LF) (r : Pre y) → Low y r → Set
NestedKid : (y : LF) (i : Kid y) → KidR y i → Set

data LF where
  zero : LF
  suc  : LF → LF
  lim  : (ℕ → LF) → LF
  lc   : (k : LF) (c : Raw k) (w : Lgl k c) (b : Nested k c)
         (t : LF) (p : Reach (suc k) t)
         (g : (η : Raw k) → Gd k c η → LF) → LF

data Reach where
  here : ∀ {a} → Reach a a
  via-suc : ∀ {a x} → Reach a x → Reach a (suc x)
  via-lim : ∀ {a f} n → Reach a (f n) → Reach a (lim f)
  via-first : ∀ {a k c w b t p g} → Reach a t →
    Reach a (lc k c w b t p g)
  via-branch : ∀ {a k c w b t p g} η e → Reach a (g η e) →
    Reach a (lc k c w b t p g)

Raw x = G.R (Pre x) (Low x) (GdL x) (Kid x) (KidR x)

Pre zero = ⊥
Pre (suc k) = ⊤ ⊎ Pre k
Pre (lim f) = Σ ℕ λ n → Pre (f n)
Pre (lc k c w b t p g) = (⊤ ⊎ Pre k) ⊎
  (Pre t ⊎ Σ (Raw k) λ η → Σ (Gd k c η) λ e → Pre (g η e))

Low (suc k) (inj₁ _) = Raw k
Low (suc k) (inj₂ r) = Low k r
Low (lim f) (n , r) = Low (f n) r
Low (lc k c w b t p g) (inj₁ (inj₁ _)) = Raw k
Low (lc k c w b t p g) (inj₁ (inj₂ r)) = Low k r
Low (lc k c w b t p g) (inj₂ (inj₁ r)) = Low t r
Low (lc k c w b t p g) (inj₂ (inj₂ (η , e , r))) = Low (g η e) r

GdL (suc k) (inj₁ _) a d = Gd k a d
GdL (suc k) (inj₂ r) a d = GdL k r a d
GdL (lim f) (n , r) a d = GdL (f n) r a d
GdL (lc k c w b t p g) (inj₁ (inj₁ _)) a d = Gd k a d
GdL (lc k c w b t p g) (inj₁ (inj₂ r)) a d = GdL k r a d
GdL (lc k c w b t p g) (inj₂ (inj₁ r)) a d = GdL t r a d
GdL (lc k c w b t p g) (inj₂ (inj₂ (η , e , r))) a d = GdL (g η e) r a d

Kid zero = ⊥
Kid (suc k) = ⊤
Kid (lim f) = ℕ
Kid (lc k c w b t p g) = ⊤ ⊎ (⊤ ⊎ Σ (Raw k) λ η → Gd k c η)

KidR (suc k) _ = Raw k
KidR (lim f) n = Raw (f n)
KidR (lc k c w b t p g) (inj₁ _) = Raw k
KidR (lc k c w b t p g) (inj₂ (inj₁ _)) = Raw t
KidR (lc k c w b t p g) (inj₂ (inj₂ (η , e))) = Raw (g η e)

Cp y a d = (a ≡ d) ⊎ Dn y a d

Dn y a G.zero = ⊥
Dn y a (G.suc d) = Cp y a d
Dn y a (G.lim f) = Σ ℕ λ n → Cp y a (f n)
Dn y a (G.lc r c t g) = Cp y a t
Dn y a G.top = DnT y a
Dn y G.zero (G.em i T) = ⊥
Dn y G.top (G.em i T) = ⊥
Dn y (G.suc _) (G.em i T) = ⊥
Dn y (G.lim _) (G.em i T) = ⊥
Dn y (G.lc _ _ _ _) (G.em i T) = ⊥
Dn y (G.em i′ a) (G.em i T) = DnK y i′ i a T

DnK (suc k) _ _ a d = Dn k a d
DnK (lim f) n m a d = Σ (n ≡ m) λ q → DnLm f n m q a d
DnK (lc k c w b t p g) (inj₁ _) (inj₁ _) a d = Dn k a d
DnK (lc k c w b t p g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) a d = Dn t a d
DnK (lc k c w b t p g) (inj₂ (inj₂ x)) (inj₂ (inj₂ x′)) a d =
  Σ (x ≡ x′) λ q → DnBr k c g x x′ q a d
DnK (lc k c w b t p g) (inj₁ _) (inj₂ _) a d = ⊥
DnK (lc k c w b t p g) (inj₂ _) (inj₁ _) a d = ⊥
DnK (lc k c w b t p g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) a d = ⊥
DnK (lc k c w b t p g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) a d = ⊥

DnLm f n .n refl a d = Dn (f n) a d

DnT zero a = ⊥
DnT (suc k) (G.em _ a) = Cp k a G.top
DnT (suc k) G.zero = ⊥
DnT (suc k) (G.suc _) = ⊥
DnT (suc k) (G.lim _) = ⊥
DnT (suc k) (G.lc _ _ _ _) = ⊥
DnT (suc k) G.top = ⊥
DnT (lim f) a = ⊥
DnT (lc k c w b t p g) (G.em (inj₂ (inj₁ _)) a) = Cp t a G.top
DnT (lc k c w b t p g) (G.em (inj₁ _) a) = ⊥
DnT (lc k c w b t p g) (G.em (inj₂ (inj₂ _)) a) = ⊥
DnT (lc k c w b t p g) G.zero = ⊥
DnT (lc k c w b t p g) (G.suc _) = ⊥
DnT (lc k c w b t p g) (G.lim _) = ⊥
DnT (lc k c w b t p g) (G.lc _ _ _ _) = ⊥
DnT (lc k c w b t p g) G.top = ⊥

DnBr k c g (η , e) .(η , e) refl a d = Dn (g η e) a d

Gd k c η = Cp k c η × (Lgl k η × Nested k η)

Lgl y G.zero = ⊤
Lgl y (G.suc a) = Lgl y a
Lgl y (G.lim f) =
  (∀ n → Cp y (f n) (f (suc n))) × (∀ n → Lgl y (f n))
Lgl y (G.lc r c t g) =
  (∀ η e → Cp y t (g η e)) ×
  (∀ η e η′ e′ → GdL y r η η′ → Cp y (g η e) (g η′ e′)) ×
  (∀ η e e′ → g η e ≡ g η e′) ×
  Lgl y t × (∀ η e → Lgl y (g η e))
Lgl y (G.em i T) = LglK y i T
Lgl y G.top = ⊤

LglK (suc k) _ T = Lgl k T
LglK (lim f) n T = Lgl (f n) T
LglK (lc k c w b t p g) (inj₁ _) T = Lgl k T
LglK (lc k c w b t p g) (inj₂ (inj₁ _)) T = Lgl t T
LglK (lc k c w b t p g) (inj₂ (inj₂ (η , e))) T = Lgl (g η e) T

LglLow (suc k) (inj₁ _) d = Lgl k d
LglLow (suc k) (inj₂ r) d = LglLow k r d
LglLow (lim f) (n , r) d = LglLow (f n) r d
LglLow (lc k c w b t p g) (inj₁ (inj₁ _)) d = Lgl k d
LglLow (lc k c w b t p g) (inj₁ (inj₂ r)) d = LglLow k r d
LglLow (lc k c w b t p g) (inj₂ (inj₁ r)) d = LglLow t r d
LglLow (lc k c w b t p g) (inj₂ (inj₂ (η , e , r))) d =
  LglLow (g η e) r d

Nested y G.zero = ⊤
Nested y (G.suc a) = Nested y a
Nested y (G.lim f) = ∀ n → Nested y (f n)
Nested y (G.lc r c t g) =
  LglLow y r c × NestedLow y r c × Nested y t ×
  (∀ η e → Nested y (g η e))
Nested y (G.em i a) = NestedKid y i a
Nested y G.top = ⊤

NestedLow (suc k) (inj₁ _) d = Nested k d
NestedLow (suc k) (inj₂ r) d = NestedLow k r d
NestedLow (lim f) (n , r) d = NestedLow (f n) r d
NestedLow (lc k c w b t p g) (inj₁ (inj₁ _)) d = Nested k d
NestedLow (lc k c w b t p g) (inj₁ (inj₂ r)) d = NestedLow k r d
NestedLow (lc k c w b t p g) (inj₂ (inj₁ r)) d = NestedLow t r d
NestedLow (lc k c w b t p g) (inj₂ (inj₂ (η , e , r))) d =
  NestedLow (g η e) r d

NestedKid (suc k) _ a = Nested k a
NestedKid (lim f) n a = Nested (f n) a
NestedKid (lc k c w b t p g) (inj₁ _) a = Nested k a
NestedKid (lc k c w b t p g) (inj₂ (inj₁ _)) a = Nested t a
NestedKid (lc k c w b t p g) (inj₂ (inj₂ (η , e))) a = Nested (g η e) a
```
