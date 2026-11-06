# 带类型折叠的 sup 层: 接口

> 不含记号. 入口 [TySup](TySup.lagda.md). 构造一路 TySup, 否定一路 NegTySup 共用. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.
>
> **这一篇做什么.** [Fab3Typed](Fab3Typed.lagda.md) 的带类型折叠 `Ψ : Wd (step T) → HB (step T) → HB T` 每次只坍缩顶上那一个种类, 所以只能沿后继层的塔逐层折到底. 在 `sup` 层没有顶种类: 一个高度里同时有各层的种类. 要按**目标层**决定每个种类是留还是坍缩. 本篇把这件事要的东西写成一个记录 `TySupIf`:
>
> - 层号 `C`, 层号之间的字面第一位置 `_⊑_` 与严格的 `_⊏_` (种类在层号里的位置), 层号的合法 `LgC`;
> - 以层号为下标的种类结构 `L : C → KS`, 每个种类的层号 `lv` 与位置 `pos`, 坐标就是那一层的值 (`toE`);
> - 每层的地板 `top X : HB (L X)` (读法 $\Omega_X$);
> - **决定** `dec`: 目标层 $t$ 与种类 $\kappa$ 的层号 $i$ 比较, 结果是三种之一: 留 (`keep`, 带 $t$ 层里的种类与坐标的回读), 同层 (`same`, 用当前界坍缩), 在上 (`above`, 先在第 $i$ 层坍缩, 再从 $i$ 折到 $t$).
>
> **律带字面公共上界.** `dec` 的两个下标 ($t$ 与 $\kappa$ 的层号) 都带在同一个层号 $X$ 之下的字面证据: $t$ 带 `t ⊑ X`, $\kappa$ 是 `L X` 的种类, 自带位置 `pos X κ : lv X κ ⊏ X`; 另带 `LgC X`. 接口里没有对裸下标的比较律 (`Survey/StallDiagnosis.md`, `NegTySupSel` 的提醒).
>
> **接口定稿 2026-11-05 21:37 (首次编译通过).** 定稿后只增不改.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TySupIf where

open import Data.Empty using (⊥)
open import OCF.Align.HtTowerTy using (KS; K; E; HB)
```

## §1 可达性

层号上的严格关系 `_⊏_` 良基, 写成可达性. 折叠对它递归 ("在上" 的情形从第 $i$ 层再折到 $t$, $i\sqsubset X$).

```agda
data AccR {C : Set} (_⊏_ : C → C → Set) (X : C) : Set where
  acc : (∀ i → i ⊏ X → AccR _⊏_ i) → AccR _⊏_ X
```

## §2 决定的三种结果

`Dc L _⊏_ _⊑_ X t κ`: 在层号 $X$ 的种类结构里, 种类 $\kappa$ 对目标层 $t$:

- `keep κ′ fr`: $\kappa$ 的层号严格低于 $t$, 在 `L t` 里是种类 $\kappa'$; `fr` 把 $\kappa'$ 的坐标读回 $\kappa$ 的坐标 (实例里是恒等, 类型逐构造子对上).
- `same to`: $\kappa$ 的层号就是 $t$; `to` 把第 $t$ 层的值当作 $\kappa$ 的坐标 (回灌, 实例里是恒等).
- `above i pi q to`: $\kappa$ 的层号 $i$ 严格在 $X$ 之下 (`pi`), $t$ 在 $i$ 之下 (`q`); `to` 把第 $i$ 层的值当作坐标.

```agda
data Dc {C : Set} (L : C → KS) (_⊏_ _⊑_ : C → C → Set) (X t : C) (κ : K (L X)) : Set where
  keep  : (κ′ : K (L t)) → (E (L t) κ′ → E (L X) κ) → Dc L _⊏_ _⊑_ X t κ
  same  : (HB (L t) → E (L X) κ) → Dc L _⊏_ _⊑_ X t κ
  above : (i : C) → i ⊏ X → t ⊑ i → (HB (L i) → E (L X) κ) → Dc L _⊏_ _⊑_ X t κ
```

## §3 记录

```agda
record TySupIf : Set₁ where
  field
    C     : Set
    _⊑_   : C → C → Set
    _⊏_   : C → C → Set
    LgC   : C → Set
    ⊏→⊑   : ∀ {i X} → i ⊏ X → i ⊑ X
    lgC↓  : ∀ {i X} → i ⊏ X → LgC X → LgC i
    wf    : ∀ X → AccR _⊏_ X
    L     : C → KS
    lv    : ∀ X → K (L X) → C
    pos   : ∀ X κ → lv X κ ⊏ X
    toE   : ∀ X κ → HB (L (lv X κ)) → E (L X) κ
    top   : ∀ X → HB (L X)
    z     : C
    z⊑    : ∀ X → z ⊑ X
    noK   : K (L z) → ⊥
    -- 决定: 两个下标 (t 与 κ 的层号) 都在 X 之下, 带字面证据; X 合法
    dec   : ∀ X t → t ⊑ X → LgC X → (κ : K (L X)) → Dc L _⊏_ _⊑_ X t κ
```
