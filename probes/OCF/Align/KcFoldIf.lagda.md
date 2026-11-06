# 种类塔上的一级折叠: 接口 (带外层世界的层, 可入判定, 下降, 带世界的折叠, 外层世界长高的律)

> **接口定稿 2026-11-05 15:44 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 本路 (前缀 `KcFold`) 是 [LvKt](LvKt.lagda.md) 的续作的**构造**一路: 给出 `LvKtIf.FoldTower` 的有内容的实例. 否定一路 (前缀 `NegKcFold`) 导入本文件, 不另造接口. 本篇只放类型, 记录与只由构造子组成的定义, 不放证明. 导入 [LvKtIf](LvKtIf.lagda.md) (不改它), [LvKtCode](LvKtCode.lagda.md), [HtTowerTy](HtTowerTy.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **对象.**
>
> - **带外层世界的层 `LvW a c`** (`LvOmLev.LvM.Lv` 推广到一般种类结构 `K`, 外层世界 $a$ 取 `Wd K`): `hz` ↦ `S₀`; `hs c` ↦ `step (LvW a c)`; `hl f` ↦ `sup ℕ (n ↦ step (LvW a (f n)))`; `hΩ κ g` ↦ `sup (Σ x. Bd K κ x a) ((x,e) ↦ step (LvW a (g x)))`. 与 `LvOm` 同形 (极限处每一支取后继); $\Omega$-结点只取在 $a$ 里可入的分支, 种类带证据 $(x, e)$.
> - **可入判定 `BDecK K`** (照 `StallDxBdec.bdec`, `LvOmLev.dec⊲`): 坐标 $x$ 与外层世界 $a$ 都在同一个合法世界 $W$ 之下 (`Bd K κ x W`, `a ≤w W`), 则 `Dec (Bd K κ x a)`.
> - **下降 `DnK S`**: `HB S → Ht` 与它保合法 (`LvRdIf.Dn` 推广到一切种类结构). `DnTower`: 对每站每个合法层号 $b$, 第 $b$ 级 `Lev b` 的下降; `DnLim`: 极限站.
> - **数据树的层 `LayK K = HB (step K)`** 与层号映射 `lyK c = hs (up c)` (`LvOmLev.Ly` 的推广: 层号 $c$ 的读回层是 $1+c$).
> - **带世界的槽与折叠 `FoldAtKW`** (`LvKtIf.FoldAtK` 的只增版本): 槽类型 `HB (LvW a (tgt k))`, 读回类型 `HB (LvW a (tgt c))`; 回灌输出仍在 `Ht`. `FoldAllKW`, `FoldTowerW`, `FoldLimKW` 同 `LvKtIf`.
> - **桥 `ForgetK K`**: 带世界的层到接口的层 `HB (LvW a c) → HB (Lev c)` (保合法). 有了它, `FoldAllKW` 给出 `FoldAllK` 的读回.
> - **外层世界长高的律** `GrowW K` (层随外层世界变大而嵌入) 与 **世界塔** `WTower` (每站一个合法外层世界, 后一站的 `inj₁ tt` 分量在前一站的世界之上). 对照 `NegLvKtCopy.code-botK`: 塔若每站取码的基世界 `w0`, 码只走 $\Omega$-结点的底支; `WTower` 要的是不取 `w0` 的、随站长高的外层世界.
>
> **律的定义域 (逐条).** 律里出现的每一对下标都带字面公共上界:
>
> - `FoldAtKW.rtW`, `lrtW`, `HW`, `lgHW`: 每条只出现**一个**码 $c$, 带字面的界 $b$ 与外层世界 $a$ (`Codes.pth c : tgt c ⊲[ a ] b`). 不比较两个码, 两个坐标, 两站的层号. 没有更新律.
> - `BDecK`: 一对 $(x, a)$, 公共上界是合法世界 $W$, 证据 `Bd K κ x W` 与 `a ≤w W` 都在前提里. **不对裸坐标判定** (对照 `NegLvRdLay.decAcc-sep`, `decAcc→WLPO`).
> - `GrowW.embW`: 一对外层世界 $(a, a')$, 证据 `a ≤w a′` 在前提里 ($a'$ 是公共上界), $a'$ 合法.
> - `WTower.grow`: 一对 $(a_s, a_{s+1}(\mathrm{inj_1\,tt}))$, 同在 `Wd (Kc s)`, 证据是 `≤w` 本身 (公共上界是后者).
> - `ForgetK`, `DnK`, `DnTower`, `DnLim`: 每条只有一个高度, 没有成对的下标.
> - 码的相等: 只在同一 $(a,b)$ 之下判 (`Codes.code-≟`).
>
> **`no-retract` 与壁垒 (检查).** `LvW a c` 的种类以 `Σ x. Bd K κ x a` 为下标, 坐标是 `K` 的坐标或更低的 `HB (LvW a c′)`, 没有一个种类以 `HB (LvW a c)` 自身为坐标. `BDecK` 是带公共上界的判定 (壁垒定理要的是无界的三歧, 这里不要). [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** 记录只要求输出合法; 恒取 $0$ 的折叠是 `FoldAtKW` 的实例 (同 `LvKtVal.foldTrivK`). 所以接口不决定值. `DnK` 的常数实例也合法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KcFoldIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.LvKtCode
open import OCF.Align.LvKtIf
```

## §1 带外层世界的层

```agda
LvW : ∀ {K : KS} → Wd K → HB K → KS
LvW a hz = S₀
LvW a (hs c) = step (LvW a c)
LvW a (hl f) = sup ℕ (λ n → step (LvW a (f n)))
LvW {K} a (hΩ κ g) = sup (Σ (E K κ) (λ x → Bd K κ x a)) (λ p → step (LvW a (g (proj₁ p))))
```

## §2 公共上界之下的可入判定

```agda
BDecK : KS → Set
BDecK K = ∀ {κ x a W} → Bd K κ x W → _≤w_ K a W → LgW K W → Dec (Bd K κ x a)

BDecTower : Set
BDecTower = ∀ s → BDecK (Kc s)
```

## §3 下降与数据树的层

```agda
DnK : KS → Set
DnK S = Σ (HB S → Ht) (λ d → ∀ x → LgB x → LgB (d x))

DnTower : Set
DnTower = ∀ s (b : HB (Kc s)) → LgB b → DnK (Lev b)

DnLim : Set
DnLim = ∀ (b : HB KΛc) → LgB b → DnK (Lev b)

LayK : KS → Set
LayK K = HB (step K)

lyK : ∀ {K : KS} → HB K → LayK K
lyK c = hs (up c)
```

## §4 带世界的槽与折叠 (只增)

```agda
module _ {K : KS} (ck : CdK K) where
  open Codes ck

  WbKW : Wd K → HB K → Set
  WbKW a b = (k : Code a b) → HB (LvW a (tgt k))

  LgWbKW : ∀ {a b} → WbKW a b → Set
  LgWbKW w = ∀ k → LgB (w k)

record FoldAtKW (K : KS) (ck : CdK K) (Cov : HB K → Set) : Set where
  open Codes ck
  field
    rtW  : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → Cov (tgt c) → (w : WbKW ck a b) → LgWbKW ck w → HB (LvW a (tgt c))
    lrtW : ∀ {a b} (la : LgW K a) (lb : LgB b) c (cv : Cov (tgt c)) w (lw : LgWbKW ck w) → LgB (rtW la lb c cv w lw)
    HW   : ∀ {a b} → LgW K a → LgB b → (c : Code a b) → Cov (tgt c) → (w : WbKW ck a b) → LgWbKW ck w → Ht
    lgHW : ∀ {a b} (la : LgW K a) (lb : LgB b) c (cv : Cov (tgt c)) w (lw : LgWbKW ck w) → LgB (HW la lb c cv w lw)

FoldAllKW : (K : KS) → CdK K → Set
FoldAllKW K ck = FoldAtKW K ck (λ _ → ⊤)

FoldTowerW : Set
FoldTowerW = ∀ s → FoldAllKW (Kc s) (ckc s)

FoldLimKW : Set
FoldLimKW = FoldAllKW KΛc ckΛ
```

## §5 桥: 带世界的层到接口的层

```agda
ForgetK : KS → Set
ForgetK K = ∀ (a : Wd K) → LgW K a → (c : HB K) →
  Σ (HB (LvW a c) → HB (Lev c)) (λ φ → ∀ x → LgB x → LgB (φ x))
```

## §6 外层世界长高的律

```agda
record GrowW (K : KS) : Set where
  field
    embW   : ∀ {a a′} (c : HB K) → _≤w_ K a a′ → LgW K a′ → HB (LvW a c) → HB (LvW a′ c)
    lgEmbW : ∀ {a a′} (c : HB K) (q : _≤w_ K a a′) (la′ : LgW K a′) x → LgB x → LgB (embW c q la′ x)

record WTower : Set where
  field
    aW   : ∀ s → Wd (Kc s)
    laW  : ∀ s → LgW (Kc s) (aW s)
    grow : ∀ s → _≤w_ (Kc s) (aW s) (aW (suc s) (inj₁ tt))
```
