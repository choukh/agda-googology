# 作用域化的块: 层号, 树, 不摊平的加法, 读回, 塔

非验收文件, 成品候选. 判决: 定义 (第 1 层), 没有定理. 树的下标是作用域 (从本层的根往下的一条孩子路径); 结点的位置是当前作用域的根, `into` 进孩子, `up` 回外层.
与第十二次审查的原型的差别: 层号的三种极限合成一个 `sup` (种类 `one`, `nat`, `raw k`); Ω 结点层号 (`raw k`) 的根也是结点位置; `top` 不是构造子, 是定义出来的树;
洞是叶子; 加法的左加数总在根作用域. 不说明值. 折叠在 [YiScopeFold](YiScopeFold.lagda.md), 合法性在 [YiScopeLegal](YiScopeLegal.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiScopeCore where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

## 1 块

`G.T` 是一层的树族, 下标是作用域. `hole v` 是根作用域之外的东西 `v` (只在根上, 作最左的底).
层号: `sup one g` 是后继 (`g tt` 的后继), `sup nat g` 是 ℕ 极限, `sup (raw k) g` 是 Ω 结点层号 (旧块的 `lc k g`).
后继层号与 Ω 结点层号的根是结点位置, 分支下标分别是 `Raw (g tt)` 与 `Raw k`.

```agda
module G (X Sc : Set) (rt : Sc) (Root Dom Kid : Sc → Set) (sub : (s : Sc) → Kid s → Sc) where
  data T : Sc → Set where
    zero : ∀ {s} → T s
    suc  : ∀ {s} → T s → T s
    lim  : ∀ {s} → (ℕ → T s) → T s
    nd   : ∀ {s} → Root s → (Dom s → T s) → T s
    into : ∀ {s} (c : Kid s) → T (sub s c) → T s
    up   : ∀ {s s′} (c : Kid s) → sub s c ≡ s′ → T s → T s′
    hole : X → T rt

data Sort : Set
data Level : Set
Ar : Sort → Set
Path Below : Level → Set
Root Dom Kid : (K : Level) → Path K → Set
sub : (K : Level) (s : Path K) → Kid K s → Path K
Tr : Set → (K : Level) → Path K → Set
Raw : Level → Set

data Sort where
  one nat : Sort
  raw : Level → Sort

data Level where
  zero : Level
  sup  : (S : Sort) → (Ar S → Level) → Level

Ar one = ⊤
Ar nat = ℕ
Ar (raw k) = Raw k

Path K = ⊤ ⊎ Below K

Below zero = ⊥
Below (sup S g) = Σ (Ar S) (λ c → Path (g c))

pattern root = inj₁ tt
pattern down c p = inj₂ (c , p)

Root zero _ = ⊥
Root (sup S g) (down c p) = Root (g c) p
Root (sup one g) root = ⊤
Root (sup nat g) root = ⊥
Root (sup (raw k) g) root = ⊤

Dom zero _ = ⊥
Dom (sup S g) (down c p) = Dom (g c) p
Dom (sup one g) root = Raw (g tt)
Dom (sup nat g) root = ⊥
Dom (sup (raw k) g) root = Raw k

Kid zero _ = ⊥
Kid (sup S g) root = Ar S
Kid (sup S g) (down c p) = Kid (g c) p

sub zero p ()
sub (sup S g) root c = down c root
sub (sup S g) (down d p) c = down d (sub (g d) p c)

Tr X K = G.T X (Path K) root (Root K) (Dom K) (Kid K) (sub K)

Raw K = Tr ⊥ K root

domE : ∀ {ℓ} (P : Set → Set ℓ) K p → Root K p → (∀ j → P (Raw j)) → P (Dom K p)
domE P zero (inj₁ _) ()
domE P zero (inj₂ ())
domE P (sup S g) (down c p) r f = domE P (g c) p r f
domE P (sup one g) root r f = f (g tt)
domE P (sup nat g) root ()
domE P (sup (raw k) g) root r f = f k
```

## 2 换根与加法

`un` 把孩子层的树 (洞里是外层的东西) 接到外层的孩子作用域下, 洞换成 `up`; `lift` 把根上的树沿 `up` 送进作用域 `p`.
加法的左加数总在根作用域, 右加数是闭树: 不打开 `into`, 左加数原样到达右加数的底 (`up` 的外层那棵树的底, 或零处的 `lift`).
作用域 `p` 里两棵树相加时, 左加数先用 `wrap` (沿 `into` 包回根作用域; `re` 是 `un` 的反向) 送到根上. `sucS K p y` 是 `y · ω`.

```agda
acc : ∀ {V : Set} → (ℕ → V → V) → V → ℕ → V
acc step start zero = start
acc step start (suc n) = step n (acc step start n)

un : ∀ {X Y} S g c → (X → Tr Y (sup S g) root) → ∀ p → Tr X (g c) p → Tr Y (sup S g) (down c p)
un S g c h p G.zero = G.zero
un S g c h p (G.suc a) = G.suc (un S g c h p a)
un S g c h p (G.lim f) = G.lim (λ n → un S g c h p (f n))
un S g c h p (G.nd r b) = G.nd r (λ η → un S g c h p (b η))
un S g c h p (G.into d t) = G.into d (un S g c h (sub (g c) p d) t)
un S g c h p (G.up {s} d refl y) = G.up d refl (un S g c h s y)
un S g c h p (G.hole v) = G.up c refl (h v)

lift : ∀ {Y} K p → Tr Y K root → Tr Y K p
lift K root t = t
lift zero (inj₂ ()) t
lift (sup S g) (down c p) t = un S g c (λ v → v) p (lift (g c) p (G.hole t))

plus : ∀ {X K s} → Tr X K root → Tr ⊥ K s → Tr X K s
plus {K = K} {s} x G.zero = lift K s x
plus x (G.suc a) = G.suc (plus x a)
plus x (G.lim f) = G.lim (λ n → plus x (f n))
plus x (G.nd r h) = G.nd r (λ η → plus x (h η))
plus x (G.into c t) = G.into c (plus x t)
plus x (G.up c e y) = G.up c e (plus x y)
plus x (G.hole ())

re : ∀ {X} S g c p → Tr X (sup S g) (down c p) → Tr (Tr X (sup S g) root) (g c) p
re S g c p G.zero = G.zero
re S g c p (G.suc a) = G.suc (re S g c p a)
re S g c p (G.lim f) = G.lim (λ n → re S g c p (f n))
re S g c p (G.nd r b) = G.nd r (λ η → re S g c p (b η))
re S g c p (G.into d t) = G.into d (re S g c (sub (g c) p d) t)
re S g c p (G.up {s = root} c′ refl y) = G.hole y
re S g c p (G.up {s = down c′ p′} d refl y) = G.up d refl (re S g c′ p′ y)

wrap : ∀ {X} K p → Tr X K p → Tr X K root
wrap K root z = z
wrap zero (inj₂ ()) z
wrap (sup S g) (down c p) z = G.into c (un S g c (λ v → v) root (wrap (g c) p (re S g c p z)))

sucS : ∀ K p → Tr ⊥ K p → Tr ⊥ K p
sucS K p y = G.lim (acc (λ _ z → plus (wrap K p z) y) y)
```

## 3 `top`

`top K x` 是 `x` 加上这一层的 Ω, 写成树: 零层是后继; 后继层是根结点, 分支 `η` 是 `x + η`; ℕ 极限层逐项接上各孩子的 `top` (`ct`);
Ω 结点层号是根结点, 分支沿下标的结构累加各孩子的 `top` (`Kf`; 分支要对下标单调, 而不同孩子的 `top` 互不为第一位置).
`Kf` 走过下标树时 `into` 与 `up` 不改变结果; 孩子的下标取当前子树包回根作用域的样子. `tpD` 是结点的分支下标层的 `top`, 结点的第一位置经过它.

```agda
top : ∀ K → Raw K → Raw K
ct : ∀ S g (c : Ar S) → Raw (sup S g) → Raw (sup S g)
tpD : ∀ K p → Root K p → Dom K p
Kf : ∀ {K} k {p} → (Raw k → Raw K → Raw K) → Raw K → Tr ⊥ k p → Raw K

top zero x = G.suc x
top (sup one g) x = G.nd tt (λ η → plus {s = root} x (G.into tt (un one g tt ⊥-elim root η)))
top (sup nat g) x = G.lim (acc (λ n z → ct nat g (suc n) z) (ct nat g 0 x))
top (sup (raw k) g) x = G.nd tt (Kf k (ct (raw k) g) x)

ct S g c z = plus {s = root} z (G.into c (un S g c ⊥-elim root (top (g c) G.zero)))

tpD zero (inj₁ _) ()
tpD zero (inj₂ ())
tpD (sup S g) (down c p) r = tpD (g c) p r
tpD (sup one g) root r = top (g tt) G.zero
tpD (sup nat g) root ()
tpD (sup (raw k) g) root r = top k G.zero

Kf k {p} T x G.zero = T (wrap k p G.zero) x
Kf k {p} T x (G.suc a) = G.lim (acc (λ _ z → T (wrap k p (G.suc a)) z) (Kf k T x a))
Kf k T x (G.lim f) = G.lim (λ n → Kf k T x (f n))
Kf k {p} T x (G.nd r h) = G.suc (Kf k T x (h (tpD k p r)))
Kf k T x (G.into c t) = Kf k T x t
Kf k T x (G.up c e y) = Kf k T x y
Kf k T x (G.hole ())
```

## 4 读回与塔

树读成层号: 结点读成 Ω 结点层号, `into` 与 `up` 不改变读回. `Ω̂ K` 是 `top K` 的读回的直接写法.

```agda
sucᴸ : Level → Level
sucᴸ k = sup one (λ _ → k)

rb : ∀ K p → Tr ⊥ K p → Level
rb K p G.zero = zero
rb K p (G.suc a) = sucᴸ (rb K p a)
rb K p (G.lim f) = sup nat (λ n → rb K p (f n))
rb K p (G.nd r h) = domE (λ D → (D → Level) → Level) K p r (λ j → sup (raw j)) (λ η → rb K p (h η))
rb K p (G.into c t) = rb K (sub K p c) t
rb K p (G.up {s} c e y) = rb K s y
rb K p (G.hole ())

Ω̂ : Level → Level
Ω̂ zero = sucᴸ zero
Ω̂ (sup one g) = sup (raw (g tt)) (rb (g tt) root)
Ω̂ (sup nat g) = sup nat (λ n → Ω̂ (g n))
Ω̂ (sup (raw k) g) = sup (raw k) (λ η → Ω̂ (g η))

tw : ℕ → Level
tw zero = zero
tw (suc n) = Ω̂ (tw n)

Λ : Level
Λ = sup nat tw
```
