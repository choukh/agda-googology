# YiUni：任意结点层上保留结点的分支族 (累加推广到带结点的下标)

**非验收文件。判决：定义与编译定理，无前提。** `KfG m k T` 把 `YiNextBase.Kf` 推广到任意层 `k` 的下标：结点下标取它的 `top` 支，嵌入进孩子层；对第一位置单调、合法 (`KfG-br`)。
坐标先归一 `nrmG` (ℕ 极限取部分和，结点取 `top` 支)，总是合法。于是任意 `Uni` 的折叠都给出满足 `Kb-br` 的族 `KbG` (`KbG-br`)，结点层 `k` 不限于 0。
只说这个字段可以填；值没有判定，结点下标被它的 `top` 支代替是值上的代价 (判断)。与 [YiUniNegKeep](YiUniNegKeep.lagda.md) 对照：不累加则不单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniKeepGen where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (Br; Ext; psum; psum-lgl; plus-weak; plus-lgl; acc-ind)
open import OCF.Lean.YiUniIf using (Uni)
```

## 1 归一与累加

```agda
tp-lg : ∀ k r → Lay.lg (Lo k r) (Lay.tp (Lo k r))
tp-lg (suc k) (inj₁ _) = tt
tp-lg (suc k) (inj₂ r) = tp-lg k r
tp-lg (lim f) (n , r) = tp-lg (f n) r
tp-lg (lc j g) (η , _ , r) = tp-lg (g η) r

nrmG : ∀ k → Raw k → Raw k
nrmG k G.zero = G.zero
nrmG k (G.suc a) = G.suc (nrmG k a)
nrmG k (G.lim f) = G.lim (psum k (λ n → nrmG k (f n)))
nrmG k (G.lc r h) = nrmG k (h (Lay.tp (Lo k r)))
nrmG (suc k) (G.em i a) = G.em i (nrmG k a)
nrmG (lim f) (G.em n a) = G.em n (nrmG (f n) a)
nrmG (lc j g) (G.em (η , l) a) = G.em (η , l) (nrmG (g η) a)
nrmG k G.top = G.top

nrmG-lgl : ∀ k η → Lgl k (nrmG k η)
nrmG-lgl k G.zero = tt
nrmG-lgl k (G.suc a) = nrmG-lgl k a
nrmG-lgl k (G.lim f) = psum-lgl k _ (λ n → nrmG-lgl k (f n))
nrmG-lgl k (G.lc r h) = nrmG-lgl k (h (Lay.tp (Lo k r)))
nrmG-lgl (suc k) (G.em i a) = nrmG-lgl k a
nrmG-lgl (lim f) (G.em n a) = nrmG-lgl (f n) a
nrmG-lgl (lc j g) (G.em (η , l) a) = nrmG-lgl (g η) a
nrmG-lgl k G.top = tt

KfG : ∀ m k → (Raw k → Raw m) → Raw k → Raw m
KfG m k T G.zero = T G.zero
KfG m k T (G.suc a) = G.lim (acc (λ _ z → plus m z (T (G.suc a))) (KfG m k T a))
KfG m k T (G.lim f) = G.lim (λ n → KfG m k T (f n))
KfG m k T (G.lc r h) = KfG m k T (h (Lay.tp (Lo k r)))
KfG m (suc k) T (G.em i a) = KfG m k (λ b → T (G.em i b)) a
KfG m (lim f) T (G.em n a) = KfG m (f n) (λ b → T (G.em n b)) a
KfG m (lc j g) T (G.em (η , l) a) = KfG m (g η) (λ b → T (G.em (η , l) b)) a
KfG m k T G.top = T G.top
```

## 2 单调与合法

```agda
KfG-cp : ∀ m k T {a b} → Cp k a b → Cp m (KfG m k T a) (KfG m k T b)
KfG-dn : ∀ m k T {a} b → Dn k a b → Cp m (KfG m k T a) (KfG m k T b)
KfG-cp m k T (inj₁ refl) = inj₁ refl
KfG-cp m k T (inj₂ p) = KfG-dn m k T _ p
KfG-dn m k T (G.suc d) p = inj₂ (0 , KfG-cp m k T p)
KfG-dn m k T (G.lim f) (n , p) = inj₂ (n , KfG-cp m k T p)
KfG-dn m k T (G.lc r h) p = KfG-cp m k T p
KfG-dn m (suc k) T {G.em _ a} (G.em _ d) (refl , p) = KfG-dn m k _ d p
KfG-dn m (lim f) T {G.em n a} (G.em _ d) (refl , p) = KfG-dn m (f n) _ d p
KfG-dn m (lc j g) T {G.em (η , l) a} (G.em _ d) (refl , p) = KfG-dn m (g η) _ d p

KfG-lgl : ∀ m k T → (∀ η → Lgl k η → Lgl m (T η)) → ∀ η → Lgl k η → Lgl m (KfG m k T η)
KfG-lgl m k T h G.zero l = h G.zero l
KfG-lgl m k T h (G.suc a) l = (λ n → plus-weak m _ _) ,
  acc-ind (Lgl m) _ (λ _ z lz → plus-lgl m z _ lz (h (G.suc a) l)) _ (KfG-lgl m k T h a l)
KfG-lgl m k T h (G.lim f) (st , lf) = (λ n → KfG-cp m k T (st n)) , (λ n → KfG-lgl m k T h (f n) (lf n))
KfG-lgl m k T h (G.lc r g) (lg , mo) = KfG-lgl m k T h (g _) (lg _ (tp-lg k r))
KfG-lgl m (suc k) T h (G.em i a) l = KfG-lgl m k _ (λ b lb → h (G.em i b) lb) a l
KfG-lgl m (lim f) T h (G.em n a) l = KfG-lgl m (f n) _ (λ b lb → h (G.em n b) lb) a l
KfG-lgl m (lc j g) T h (G.em (η , lη) a) l = KfG-lgl m (g η) _ (λ b lb → h (G.em (η , lη) b) lb) a l
KfG-lgl m k T h G.top l = h G.top l

KfG-br : ∀ m k T → (∀ η → Lgl k η → Lgl m (T η)) → Br (layer k) m (KfG m k T)
KfG-br m k T h = KfG-lgl m k T h , λ η η′ l e l′ → KfG-cp m k T e
```

## 3 任意 `Uni` 的折叠给出满足 `Kb-br` 的族

```agda
module _ (U : Uni) where
  open Uni U

  KbG : ∀ m {k g} → Bd (lc k g) → Ext m (lc k g) → Raw k → Raw m
  KbG m {k} V x = KfG m k (λ η →
    Ψ m (bC V (nrmG k η) (nrmG-lgl k η)) (λ r → x (nrmG k η , nrmG-lgl k η , r)) G.top)

  KbG-br : ∀ m {k g} (V : Bd (lc k g)) x → Br (layer k) m (KbG m V x)
  KbG-br m {k} V x = KfG-br m k _ (λ η _ → Ψ-lgl m (bC V (nrmG k η) (nrmG-lgl k η)) _ G.top tt)
```
