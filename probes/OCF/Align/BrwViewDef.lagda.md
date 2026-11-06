# 布劳威尔树的 View (一): 记录

> 不含记号. 入口 [BrwView](BrwView.lagda.md). 作者 2026-11-05 对纲领 1 的解释: 中间层若不直接用布劳威尔树, 就要有布劳威尔树的 View. 这里把它写成**一个**定义, 对一切层、一切高度通用.
>
> - `Sig`: 目标布劳威尔树的签名. 下标 `Ix` (第 1 层是带合法性的世界, 第 0 层与高度是 `⊤`), 值的类型 `B`, 值前序 `_≼_` (可以跨下标), 四种构造子 `bz`, `bs`, `bl`, `bΩ`, $\mathbb N$-极限相邻项的步进 `Stp` (取目标树自己合法性里的那一条), $\Omega$-极限的**种类** `Kd` (第 0 层没有, 高度一种, 第 1 层两种: 按坐标、按世界), 种类的坐标 `Cd`, 坐标的合法性 `LgC`, 分支所在的下标 `tg`.
> - `View i v`: 值为 $v$ 的对象的一种读法. 四种: 零; 后继 ($v\approx y+1$); $\mathbb N$-极限 ($v\approx\lim_n f\,n$, 相邻项 `Stp`); $\Omega$-极限 ($v\approx\sup_c g\,c$). 各部分 $y$, $f\,n$, $g\,c$ 都是**同一个类型族** `X` 的对象, 带合法性 (合法坐标上). 值一致就是这四条 $\approx$ (互相 $\preccurlyeq$).
> - `BrwView`: 每个合法对象都有一个 View.
>
> `View` 按值 (而不是按对象) 加下标: 两个对象值字面相同时, 一个 View 两处都能用, 不用搬运. 实例里正是靠这一点 (见 [BrwViewZero](BrwViewZero.lagda.md)).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwViewDef where

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_)
```

## §1 签名

```agda
record Sig : Set₁ where
  field
    Ix  : Set
    B   : Ix → Set
    _≼_ : ∀ {i j} → B i → B j → Set
    Stp : ∀ {i} → B i → B i → Set
    Kd  : Ix → Set
    Cd  : ∀ {i} → Kd i → Set
    LgC : ∀ {i} {k : Kd i} → Cd k → Set
    tg  : ∀ {i} {k : Kd i} → Cd k → Ix
    bz  : ∀ {i} → B i
    bs  : ∀ {i} → B i → B i
    bl  : ∀ {i} → (ℕ → B i) → B i
    bΩ  : ∀ {i} (k : Kd i) → ((c : Cd k) → B (tg c)) → B i

  infix 4 _≈_
  _≈_ : ∀ {i j} → B i → B j → Set
  a ≈ b = (a ≼ b) × (b ≼ a)
```

## §2 View 与记录

```agda
module _ (S : Sig) (X : Sig.Ix S → Set) (val : ∀ {i} → X i → Sig.B S i) (Lgl : ∀ {i} → X i → Set) where
  open Sig S

  data View (i : Ix) (v : B i) : Set where
    vz : v ≈ bz {i} → View i v
    vs : (y : X i) → Lgl y → v ≈ bs (val y) → View i v
    vl : (f : ℕ → X i) → (∀ n → Lgl (f n)) → (∀ n → Stp (val (f n)) (val (f (suc n)))) →
         v ≈ bl (λ n → val (f n)) → View i v
    vΩ : (k : Kd i) (g : (c : Cd k) → X (tg c)) → (∀ c → LgC c → Lgl (g c)) →
         v ≈ bΩ k (λ c → val (g c)) → View i v

  record BrwView : Set where
    field
      view : ∀ {i} (x : X i) → Lgl x → View i (val x)
```

**读法.** `vs y _ e`: $x$ 是 $y$ 的后继, $e$ 说 `val x` 与 `bs (val y)` 互相 $\preccurlyeq$. 其余同. 记录里**没有**部分良基 (沿 View 递归要的东西): 部分不是对象的字面子项 (第 0 层的部分是前缀与部分和), 良基要另证. 这一点在入口里记作未做.
