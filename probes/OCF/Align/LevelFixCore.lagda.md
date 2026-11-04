# 层号一次性封闭: 块 (定义)

> 不含记号. 结论写在 [LevelFix](LevelFix.lagda.md). 一个归纳-递归块: `LF` 是唯一的层号类型, `Raw k` 是第 $k$ 层的值 (低于 $\Omega_{k+1}$), 由 `k` 递归算出. 块里**没有证明**, 只有 `Set` 值的函数. 比较的上界是节点自己的 `k`.

- 节点 `lc k c t g`: 共尾度是 $\Omega_{k+1}$, 下界 `c`, 第一支 `t`, 分支 $g$ 只在 $c$ 之上的合法值上. `c` 是原始的值, 不带证据, 所以 $\Omega$ 总有定义. 这是 [LvIRGuardProbe](LvIRGuardProbe.lagda.md) 那个 "节点带下界" 的形状, 这里的下标回到层号自己.
- `Raw x`: 节点在 `x` 之下的某个位置 `r : Pre x`, 分支在 `Low x r`. `em`: 把低层的值形式地放上来, 所以 `up` 读回时一步消掉它, 不需要函数外延. `top`: $\Omega_x$ 自己, 形式地放在第 $x$ 层, `up` 把它展开. 这样极限层的 $\Omega$ 不必写出跨孩子的步进.
- 守卫 `Gd k c η`: $c$ 字面地是 $\eta$ 的第一位置, 且 $\eta$ 合法 (`Lgl`). **关系都是同层的字面相等 (`≡`) 与第一位置. 不穿过分支.** 这是 `no-WFˢ-Ω⁺` 逼出的 `Fg` 的字面形式.

**检查器实测 (`text` 块是报错原文, 临时文件不进仓库).** 字面比较两个不同层的值要 `LF` 上的相等, 正性拒绝. 下面这版 (`P1`) 用 `Elt` 把 `(j , c)` 包起来再比:

```text
P1: data Elt where el : (j : LF) → Raw j → Elt
    CpX e y b = (e ≡ peel y b) ⊎ DnX e y b
error: [NotStrictlyPositive]
LF is not strictly positive, because it occurs
in the type of the constructor el
in the definition of Elt, which occurs
                        in the second argument of _≡_
                        ...
                        in the definition of Gd, which occurs
                                               to the left of an arrow
                                               in the type of the constructor lc
```

所以这里只比同一个 `Raw y` 里的值, `≡` 的类型参数里没有 `LF` 这个名字. **代价: `em` 的两个不同孩子之间没有关系 (`DnK` 对不同的 $n$ 是 $\bot$).** 这个报错是检查器的事实, 不是数学否定. 后果写在 [LevelFix](LevelFix.lagda.md) 的 "第一个障碍".

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelFixCore where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## §1 值的形状

```agda
module G (P : Set) (L : P → Set) (Gl : (r : P) → L r → L r → Set) (K : Set) (B : K → Set) where
  data R : Set where
    zero : R
    suc  : R → R
    lim  : (ℕ → R) → R
    lc   : (r : P) (c : L r) (t : R) (g : (η : L r) → Gl r c η → R) → R
    em   : (i : K) → B i → R
    top  : R
```

## §2 块

```agda
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
DnLm : (f : ℕ → LF) (n m : ℕ) → n ≡ m → Raw (f n) → Raw (f m) → Set
DnBr : (k : LF) (c : Raw k) (g : (η : Raw k) → Gd k c η → LF) (x x′ : Σ (Raw k) λ η → Gd k c η) → x ≡ x′ →
       Raw (g (proj₁ x) (proj₂ x)) → Raw (g (proj₁ x′) (proj₂ x′)) → Set
Lgl : (y : LF) → Raw y → Set
LglK : (y : LF) (i : Kid y) → KidR y i → Set

data LF where
  zero : LF
  suc  : LF → LF
  lim  : (ℕ → LF) → LF
  lc   : (k : LF) (c : Raw k) (t : LF) (g : (η : Raw k) → Gd k c η → LF) → LF

Raw x = G.R (Pre x) (Low x) (GdL x) (Kid x) (KidR x)

Pre zero = ⊥
Pre (suc k) = ⊤ ⊎ Pre k
Pre (lim f) = Σ ℕ λ n → Pre (f n)
Pre (lc k c t g) = (⊤ ⊎ Pre k) ⊎ (Pre t ⊎ Σ (Raw k) λ η → Σ (Gd k c η) λ e → Pre (g η e))

Low (suc k) (inj₁ _) = Raw k
Low (suc k) (inj₂ r) = Low k r
Low (lim f) (n , r) = Low (f n) r
Low (lc k c t g) (inj₁ (inj₁ _)) = Raw k
Low (lc k c t g) (inj₁ (inj₂ r)) = Low k r
Low (lc k c t g) (inj₂ (inj₁ r)) = Low t r
Low (lc k c t g) (inj₂ (inj₂ (η , e , r))) = Low (g η e) r

GdL (suc k) (inj₁ _) a b = Gd k a b
GdL (suc k) (inj₂ r) a b = GdL k r a b
GdL (lim f) (n , r) a b = GdL (f n) r a b
GdL (lc k c t g) (inj₁ (inj₁ _)) a b = Gd k a b
GdL (lc k c t g) (inj₁ (inj₂ r)) a b = GdL k r a b
GdL (lc k c t g) (inj₂ (inj₁ r)) a b = GdL t r a b
GdL (lc k c t g) (inj₂ (inj₂ (η , e , r))) a b = GdL (g η e) r a b

Kid zero = ⊥
Kid (suc k) = ⊤
Kid (lim f) = ℕ
Kid (lc k c t g) = ⊤ ⊎ (⊤ ⊎ Σ (Raw k) λ η → Gd k c η)

KidR (suc k) _ = Raw k
KidR (lim f) n = Raw (f n)
KidR (lc k c t g) (inj₁ _) = Raw k
KidR (lc k c t g) (inj₂ (inj₁ _)) = Raw t
KidR (lc k c t g) (inj₂ (inj₂ (η , e))) = Raw (g η e)

Cp y a b = (a ≡ b) ⊎ Dn y a b

Dn y a G.zero = ⊥
Dn y a (G.suc b) = Cp y a b
Dn y a (G.lim f) = Σ ℕ λ n → Cp y a (f n)
Dn y a (G.lc r c t g) = Cp y a t
Dn y a G.top = DnT y a
Dn y G.zero (G.em i T) = ⊥
Dn y G.top (G.em i T) = ⊥
Dn y (G.suc _) (G.em i T) = ⊥
Dn y (G.lim _) (G.em i T) = ⊥
Dn y (G.lc _ _ _ _) (G.em i T) = ⊥
Dn y (G.em i′ a) (G.em i T) = DnK y i′ i a T

DnK (suc k) _ _ a b = Dn k a b
DnK (lim f) n m a b = Σ (n ≡ m) λ p → DnLm f n m p a b
DnK (lc k c t g) (inj₁ _) (inj₁ _) a b = Dn k a b
DnK (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) a b = Dn t a b
DnK (lc k c t g) (inj₂ (inj₂ x)) (inj₂ (inj₂ x′)) a b = Σ (x ≡ x′) λ p → DnBr k c g x x′ p a b
DnK (lc k c t g) (inj₁ _) (inj₂ _) a b = ⊥
DnK (lc k c t g) (inj₂ _) (inj₁ _) a b = ⊥
DnK (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) a b = ⊥
DnK (lc k c t g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) a b = ⊥

DnLm f n .n refl a b = Dn (f n) a b

DnT zero a = ⊥
DnT (suc k) (G.em _ a) = Cp k a G.top
DnT (suc k) G.zero = ⊥
DnT (suc k) (G.suc _) = ⊥
DnT (suc k) (G.lim _) = ⊥
DnT (suc k) (G.lc _ _ _ _) = ⊥
DnT (suc k) G.top = ⊥
DnT (lim f) a = ⊥
DnT (lc k c t g) (G.em (inj₂ (inj₁ _)) a) = Cp t a G.top
DnT (lc k c t g) (G.em (inj₁ _) a) = ⊥
DnT (lc k c t g) (G.em (inj₂ (inj₂ _)) a) = ⊥
DnT (lc k c t g) G.zero = ⊥
DnT (lc k c t g) (G.suc _) = ⊥
DnT (lc k c t g) (G.lim _) = ⊥
DnT (lc k c t g) (G.lc _ _ _ _) = ⊥
DnT (lc k c t g) G.top = ⊥

DnBr k c g (η , e) .(η , e) refl a b = Dn (g η e) a b

Gd k c η = Cp k c η × Lgl k η

Lgl y G.zero = ⊤
Lgl y (G.suc a) = Lgl y a
Lgl y (G.lim f) = (∀ n → Cp y (f n) (f (suc n))) × (∀ n → Lgl y (f n))
Lgl y (G.lc r c t g) =
  (∀ η e → Cp y t (g η e)) ×
  (∀ η e η′ e′ → GdL y r η η′ → Cp y (g η e) (g η′ e′)) ×
  (∀ η e e′ → g η e ≡ g η e′) ×
  Lgl y t × (∀ η e → Lgl y (g η e))
Lgl y (G.em i T) = LglK y i T
Lgl y G.top = ⊤

LglK (suc k) _ T = Lgl k T
LglK (lim f) n T = Lgl (f n) T
LglK (lc k c t g) (inj₁ _) T = Lgl k T
LglK (lc k c t g) (inj₂ (inj₁ _)) T = Lgl t T
LglK (lc k c t g) (inj₂ (inj₂ (η , e))) T = Lgl (g η e) T
```

## §3 同层的第一位置: 传递, 比较

块外, 对 `Raw y` 的结构递归. `cmpC`: 字面上界之下的两个第一位置可比, 上界的合法性给极限的步进. 没有比较两个分支, 没有世界.

```agda
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import Data.Empty using (⊥-elim)

Cp-tr : ∀ y {a b d} → Cp y a b → Cp y b d → Cp y a d
Dn-cp : ∀ y {a b} d → Cp y a b → Dn y b d → Dn y a d
Dn-tr : ∀ y {a b d} → Dn y a b → Dn y b d → Dn y a d
DnK-tr : ∀ y i₁ i₂ i₃ {a b d} → DnK y i₁ i₂ a b → DnK y i₂ i₃ b d → DnK y i₁ i₃ a d

Cp-tr y (inj₁ refl) q = q
Cp-tr y (inj₂ p) (inj₁ refl) = inj₂ p
Cp-tr y (inj₂ p) (inj₂ q) = inj₂ (Dn-tr y p q)

Dn-tr y {d = d} p q = Dn-cp y d (inj₂ p) q

Dn-cp y (G.suc d) p q = Cp-tr y p q
Dn-cp y (G.lim f) p (n , q) = n , Cp-tr y p q
Dn-cp y (G.lc r c t g) p q = Cp-tr y p q
Dn-cp y (G.em i T) (inj₁ refl) q = q
Dn-cp y {a = G.em i₁ _} {G.em i₂ _} (G.em i T) (inj₂ p) q = DnK-tr y i₁ i₂ i p q

Dn-cp y G.top (inj₁ refl) q = q
Dn-cp (suc k) {G.em _ _} {G.em _ _} G.top (inj₂ p) q = Cp-tr k (inj₂ p) q
Dn-cp (lc k c t g) {G.em (inj₂ (inj₁ _)) _} {G.em (inj₂ (inj₁ _)) _} G.top (inj₂ p) q = Cp-tr t (inj₂ p) q

DnK-tr (suc k) _ _ _ p q = Dn-tr k p q
DnK-tr (lim f) n .n m (refl , p) (refl , q) = refl , Dn-tr (f n) p q
DnK-tr (lc k c t g) (inj₁ _) (inj₁ _) (inj₁ _) p q = Dn-tr k p q
DnK-tr (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) p q = Dn-tr t p q
DnK-tr (lc k c t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) (inj₂ (inj₂ .(η , e))) (refl , p) (refl , q) = refl , Dn-tr (g η e) p q

Cp-suc : ∀ y {x d} → Cp y (G.suc x) d → Dn y x d
Dn-suc : ∀ y {x} d → Dn y (G.suc x) d → Dn y x d
Cp-suc y (inj₁ refl) = inj₁ refl
Cp-suc y {d = d} (inj₂ p) = Dn-suc y d p
Dn-suc y (G.suc b) (inj₁ refl) = inj₂ (inj₁ refl)
Dn-suc y (G.suc b) (inj₂ p) = inj₂ (Dn-suc y b p)
Dn-suc y (G.lim f) (n , p) = n , inj₂ (Cp-suc y p)
Dn-suc y (G.lc r c t g) p = inj₂ (Cp-suc y p)
Dn-suc y (G.em i T) ()
Dn-suc (suc k) G.top ()
Dn-suc (lc k c t g) G.top ()

lgl-cp : ∀ y {a b} → Cp y a b → Lgl y b → Lgl y a
lgl-dn : ∀ y {a} b → Dn y a b → Lgl y b → Lgl y a
lgl-k : ∀ y i₁ i₂ {a b} → DnK y i₁ i₂ a b → LglK y i₂ b → LglK y i₁ a
lgl-cp y (inj₁ refl) w = w
lgl-cp y {b = b} (inj₂ p) w = lgl-dn y b p w
lgl-dn y (G.suc b) p w = lgl-cp y p w
lgl-dn y (G.lim f) (n , p) (st , w) = lgl-cp y p (w n)
lgl-dn y (G.lc r c t g) p (tg , dir , irr , lt , lg) = lgl-cp y p lt
lgl-dn y {a = G.em i₁ _} (G.em i T) p w = lgl-k y i₁ i p w
lgl-dn (suc k) {G.em _ _} G.top p w = lgl-cp k p tt
lgl-dn (lc k c t g) {G.em (inj₂ (inj₁ _)) _} G.top p w = lgl-cp t p tt
lgl-k (suc k) _ _ {b = b} p w = lgl-dn k b p w
lgl-k (lim f) n .n {b = b} (refl , p) w = lgl-dn (f n) b p w
lgl-k (lc k c t g) (inj₁ _) (inj₁ _) {b = b} p w = lgl-dn k b p w
lgl-k (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {b = b} p w = lgl-dn t b p w
lgl-k (lc k c t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) {b = b} (refl , p) w = lgl-dn (g η e) b p w

stepsC : ∀ y {f : ℕ → Raw y} → (∀ n → Cp y (f n) (f (suc n))) → ∀ {n m} → n <ᴺ m → Cp y (f n) (f m)
stepsC y s zero = s _
stepsC y s (suc q) = Cp-tr y (stepsC y s q) (s _)

liftS : ∀ k {a b} → Cp k a b → Cp (suc k) (G.em tt a) (G.em tt b)
liftS k (inj₁ refl) = inj₁ refl
liftS k (inj₂ p) = inj₂ p

mapS : ∀ {A B C D : Set} → (A → C) → (B → D) → A ⊎ B → C ⊎ D
mapS f g (inj₁ x) = inj₁ (f x)
mapS f g (inj₂ x) = inj₂ (g x)

cmpC : ∀ y {a b} X → Cp y a X → Cp y b X → Lgl y X → (Cp y a b) ⊎ (Cp y b a)
cmpD : ∀ y {a b} X → Dn y a X → Dn y b X → Lgl y X → (Cp y a b) ⊎ (Cp y b a)
cmpK : ∀ y i₁ i₂ i {a b T} → DnK y i₁ i a T → DnK y i₂ i b T → LglK y i T →
       (Cp y (G.em i₁ a) (G.em i₂ b)) ⊎ (Cp y (G.em i₂ b) (G.em i₁ a))

cmpC y X (inj₁ refl) q w = inj₂ q
cmpC y X (inj₂ p) (inj₁ refl) w = inj₁ (inj₂ p)
cmpC y X (inj₂ p) (inj₂ q) w = cmpD y X p q w

cmpD y (G.suc X) p q w = cmpC y X p q w
cmpD y (G.lim f) (n , p) (m , q) (st , w) with <ᴺ-dec n m
... | injᵃ n<m = cmpC y (f m) (Cp-tr y p (stepsC y st n<m)) q (w m)
... | injᵇ m<n = cmpC y (f n) p (Cp-tr y q (stepsC y st m<n)) (w n)
... | injᶜ refl = cmpC y (f n) p q (w n)
cmpD y (G.lc r c t g) p q (tg , dir , irr , lt , lg) = cmpC y t p q lt
cmpD y {a = G.em i₁ _} {G.em i₂ _} (G.em i T) p q w = cmpK y i₁ i₂ i p q w
cmpD (suc k) {G.em _ _} {G.em _ _} G.top p q w = mapS (liftS k) (liftS k) (cmpC k G.top p q tt)
cmpD (lc k c t g) {G.em (inj₂ (inj₁ _)) _} {G.em (inj₂ (inj₁ _)) _} G.top p q w = mapS lif lif (cmpC t G.top p q tt)
  where
  lif : ∀ {a b} → Cp t a b → Cp (lc k c t g) (G.em (inj₂ (inj₁ tt)) a) (G.em (inj₂ (inj₁ tt)) b)
  lif (inj₁ refl) = inj₁ refl
  lif (inj₂ d) = inj₂ d


cmpK (suc k) _ _ _ {T = T} p q w = mapS (liftS k) (liftS k) (cmpD k T p q w)
cmpK (lim f) n .m m {T = T} (refl , p) (refl , q) w = mapS lifL lifL (cmpD (f m) T p q w)
  where
  lifL : ∀ {a b} → Cp (f m) a b → Cp (lim f) (G.em m a) (G.em m b)
  lifL (inj₁ refl) = inj₁ refl
  lifL (inj₂ d) = inj₂ (refl , d)
cmpK (lc k c t g) (inj₁ _) (inj₁ _) (inj₁ _) {T = T} p q w = mapS lif lif (cmpD k T p q w)
  where
  lif : ∀ {a b} → Cp k a b → Cp (lc k c t g) (G.em (inj₁ tt) a) (G.em (inj₁ tt) b)
  lif (inj₁ refl) = inj₁ refl
  lif (inj₂ d) = inj₂ d
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {T = T} p q w = mapS lif lif (cmpD t T p q w)
  where
  lif : ∀ {a b} → Cp t a b → Cp (lc k c t g) (G.em (inj₂ (inj₁ tt)) a) (G.em (inj₂ (inj₁ tt)) b)
  lif (inj₁ refl) = inj₁ refl
  lif (inj₂ d) = inj₂ d
cmpK (lc k c t g) (inj₁ _) (inj₂ (inj₁ _)) (inj₁ _) p () w
cmpK (lc k c t g) (inj₁ _) (inj₂ (inj₂ _)) (inj₁ _) p () w
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₁ _) (inj₁ _) () q w
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₁ _) () q w
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) (inj₁ _) () q w
cmpK (lc k c t g) (inj₂ (inj₂ _)) (inj₁ _) (inj₁ _) () q w
cmpK (lc k c t g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) (inj₁ _) () q w
cmpK (lc k c t g) (inj₂ (inj₂ _)) (inj₂ (inj₂ _)) (inj₁ _) () q w
cmpK (lc k c t g) (inj₁ _) (inj₁ _) (inj₂ (inj₁ _)) () q w
cmpK (lc k c t g) (inj₁ _) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) () q w
cmpK (lc k c t g) (inj₁ _) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) () q w
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₁ _) (inj₂ (inj₁ _)) p () w
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) p () w
cmpK (lc k c t g) (inj₂ (inj₂ _)) (inj₁ _) (inj₂ (inj₁ _)) () q w
cmpK (lc k c t g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) () q w
cmpK (lc k c t g) (inj₂ (inj₂ _)) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) () q w
cmpK (lc k c t g) (inj₁ _) (inj₁ _) (inj₂ (inj₂ _)) () q w
cmpK (lc k c t g) (inj₁ _) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) () q w
cmpK (lc k c t g) (inj₁ _) (inj₂ (inj₂ _)) (inj₂ (inj₂ _)) () q w
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₁ _) (inj₂ (inj₂ _)) () q w
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) () q w
cmpK (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) (inj₂ (inj₂ _)) () q w
cmpK (lc k c t g) (inj₂ (inj₂ _)) (inj₁ _) (inj₂ (inj₂ _)) p () w
cmpK (lc k c t g) (inj₂ (inj₂ _)) (inj₂ (inj₁ _)) (inj₂ (inj₂ _)) p () w
cmpK (lc k c t g) (inj₂ (inj₂ .(η , e))) (inj₂ (inj₂ .(η , e))) (inj₂ (inj₂ (η , e))) {T = T} (refl , p) (refl , q) w = mapS lif lif (cmpD (g η e) T p q w)
  where
  lif : ∀ {a b} → Cp (g η e) a b → Cp (lc k c t g) (G.em (inj₂ (inj₂ (η , e))) a) (G.em (inj₂ (inj₂ (η , e))) b)
  lif (inj₁ refl) = inj₁ refl
  lif (inj₂ d) = inj₂ (refl , d)
```
