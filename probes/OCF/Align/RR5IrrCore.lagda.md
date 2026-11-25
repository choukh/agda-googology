# RR5：证据进树，但不作数据（无关参数的平行块骨架）

第五次路线审查的最小实验，定义部分。结论与范围写在
[RR5IrrCheck](RR5IrrCheck.lagda.md) 与 `probes/Survey/RR5-SoftStops.md`。

[YiIntrCore](YiIntrCore.lagda.md) 把下界的合法性 `w`、嵌套下界 `b`、根位置路径 `p`
作为普通参数放进结点，于是它们成了树的数据：同一坐标的两份守卫证明给出两棵不同的树
（`YiIntrCheck.tw₃-not-root-irr`）。本篇只改三处：

1. `w`、`b` 标为无关参数（Agda 的 `.( … )`），所以换证明不换树，这是定义性相等；
2. 分支函数的守卫参数标为无关：`g : (η : Raw k) → .(Gd k c η) → LF`，Raw 的 `lc` 同样；
3. 不内置根位置路径 `p`，位置证据仍像原块那样放在树外（`Reg`）。

无关参数是 Agda 的语言特性，不需要额外选项，标准库在同样的选项下也用它；
它不给出 `Set` 里相等证明的唯一性，与 K 无关。其余定义逐行平行 `YiIntrCore`
（因而平行 `LevelFixCore`）：`Kid` 仍带相关的守卫证明，没有借机简化；
Raw 的 `Lgl.lc` 保留 "分支不依赖守卫证明" 一项，它现在恒由 `refl` 满足，
留着只为让旧块上按五元组拆 `Lgl` 的证明可以原样搬过来。

本篇只有定义，供检查器验正性、归纳—递归与停机。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RR5IrrCore where

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
           (g : (η : L r) → .(Gl r c η) → R) → R
    em   : (i : K) → B i → R
    top  : R

data LF : Set
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
  (g : (η : Raw k) → .(Gd k c η) → LF)
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
  lc   : (k : LF) (c : Raw k) .(w : Lgl k c) .(b : Nested k c)
         (t : LF) (g : (η : Raw k) → .(Gd k c η) → LF) → LF

Raw x = G.R (Pre x) (Low x) (GdL x) (Kid x) (KidR x)

Pre zero = ⊥
Pre (suc k) = ⊤ ⊎ Pre k
Pre (lim f) = Σ ℕ λ n → Pre (f n)
Pre (lc k c w b t g) = (⊤ ⊎ Pre k) ⊎
  (Pre t ⊎ Σ (Raw k) λ η → Σ (Gd k c η) λ e → Pre (g η e))

Low (suc k) (inj₁ _) = Raw k
Low (suc k) (inj₂ r) = Low k r
Low (lim f) (n , r) = Low (f n) r
Low (lc k c w b t g) (inj₁ (inj₁ _)) = Raw k
Low (lc k c w b t g) (inj₁ (inj₂ r)) = Low k r
Low (lc k c w b t g) (inj₂ (inj₁ r)) = Low t r
Low (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) = Low (g η e) r

GdL (suc k) (inj₁ _) a d = Gd k a d
GdL (suc k) (inj₂ r) a d = GdL k r a d
GdL (lim f) (n , r) a d = GdL (f n) r a d
GdL (lc k c w b t g) (inj₁ (inj₁ _)) a d = Gd k a d
GdL (lc k c w b t g) (inj₁ (inj₂ r)) a d = GdL k r a d
GdL (lc k c w b t g) (inj₂ (inj₁ r)) a d = GdL t r a d
GdL (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) a d = GdL (g η e) r a d

Kid zero = ⊥
Kid (suc k) = ⊤
Kid (lim f) = ℕ
Kid (lc k c w b t g) = ⊤ ⊎ (⊤ ⊎ Σ (Raw k) λ η → Gd k c η)

KidR (suc k) _ = Raw k
KidR (lim f) n = Raw (f n)
KidR (lc k c w b t g) (inj₁ _) = Raw k
KidR (lc k c w b t g) (inj₂ (inj₁ _)) = Raw t
KidR (lc k c w b t g) (inj₂ (inj₂ (η , e))) = Raw (g η e)

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
DnK (lc k c w b t g) (inj₁ _) (inj₁ _) a d = Dn k a d
DnK (lc k c w b t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) a d = Dn t a d
DnK (lc k c w b t g) (inj₂ (inj₂ x)) (inj₂ (inj₂ x′)) a d =
  Σ (x ≡ x′) λ q → DnBr k c g x x′ q a d
DnK (lc k c w b t g) (inj₁ _) (inj₂ _) a d = ⊥
DnK (lc k c w b t g) (inj₂ _) (inj₁ _) a d = ⊥
DnK (lc k c w b t g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) a d = ⊥
DnK (lc k c w b t g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) a d = ⊥

DnLm f n .n refl a d = Dn (f n) a d

DnT zero a = ⊥
DnT (suc k) (G.em _ a) = Cp k a G.top
DnT (suc k) G.zero = ⊥
DnT (suc k) (G.suc _) = ⊥
DnT (suc k) (G.lim _) = ⊥
DnT (suc k) (G.lc _ _ _ _) = ⊥
DnT (suc k) G.top = ⊥
DnT (lim f) a = ⊥
DnT (lc k c w b t g) (G.em (inj₂ (inj₁ _)) a) = Cp t a G.top
DnT (lc k c w b t g) (G.em (inj₁ _) a) = ⊥
DnT (lc k c w b t g) (G.em (inj₂ (inj₂ _)) a) = ⊥
DnT (lc k c w b t g) G.zero = ⊥
DnT (lc k c w b t g) (G.suc _) = ⊥
DnT (lc k c w b t g) (G.lim _) = ⊥
DnT (lc k c w b t g) (G.lc _ _ _ _) = ⊥
DnT (lc k c w b t g) G.top = ⊥

DnBr k c g (η , e) .(η , e) refl a d = Dn (g η e) a d

Gd k c η = Cp k c η × (Lgl k η × Nested k η)

Lgl y G.zero = ⊤
Lgl y (G.suc a) = Lgl y a
Lgl y (G.lim f) =
  (∀ n → Cp y (f n) (f (suc n))) × (∀ n → Lgl y (f n))
Lgl y (G.lc r c t g) =
  (∀ η (e : GdL y r c η) → Cp y t (g η e)) ×
  (∀ η (e : GdL y r c η) η′ (e′ : GdL y r c η′) →
     GdL y r η η′ → Cp y (g η e) (g η′ e′)) ×
  (∀ η (e e′ : GdL y r c η) → g η e ≡ g η e′) ×
  Lgl y t × (∀ η (e : GdL y r c η) → Lgl y (g η e))
Lgl y (G.em i T) = LglK y i T
Lgl y G.top = ⊤

LglK (suc k) _ T = Lgl k T
LglK (lim f) n T = Lgl (f n) T
LglK (lc k c w b t g) (inj₁ _) T = Lgl k T
LglK (lc k c w b t g) (inj₂ (inj₁ _)) T = Lgl t T
LglK (lc k c w b t g) (inj₂ (inj₂ (η , e))) T = Lgl (g η e) T

LglLow (suc k) (inj₁ _) d = Lgl k d
LglLow (suc k) (inj₂ r) d = LglLow k r d
LglLow (lim f) (n , r) d = LglLow (f n) r d
LglLow (lc k c w b t g) (inj₁ (inj₁ _)) d = Lgl k d
LglLow (lc k c w b t g) (inj₁ (inj₂ r)) d = LglLow k r d
LglLow (lc k c w b t g) (inj₂ (inj₁ r)) d = LglLow t r d
LglLow (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) d =
  LglLow (g η e) r d

Nested y G.zero = ⊤
Nested y (G.suc a) = Nested y a
Nested y (G.lim f) = ∀ n → Nested y (f n)
Nested y (G.lc r c t g) =
  LglLow y r c × NestedLow y r c × Nested y t ×
  (∀ η (e : GdL y r c η) → Nested y (g η e))
Nested y (G.em i a) = NestedKid y i a
Nested y G.top = ⊤

NestedLow (suc k) (inj₁ _) d = Nested k d
NestedLow (suc k) (inj₂ r) d = NestedLow k r d
NestedLow (lim f) (n , r) d = NestedLow (f n) r d
NestedLow (lc k c w b t g) (inj₁ (inj₁ _)) d = Nested k d
NestedLow (lc k c w b t g) (inj₁ (inj₂ r)) d = NestedLow k r d
NestedLow (lc k c w b t g) (inj₂ (inj₁ r)) d = NestedLow t r d
NestedLow (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) d =
  NestedLow (g η e) r d

NestedKid (suc k) _ a = Nested k a
NestedKid (lim f) n a = Nested (f n) a
NestedKid (lc k c w b t g) (inj₁ _) a = Nested k a
NestedKid (lc k c w b t g) (inj₂ (inj₁ _)) a = Nested t a
NestedKid (lc k c w b t g) (inj₂ (inj₂ (η , e))) a = Nested (g η e) a
```
