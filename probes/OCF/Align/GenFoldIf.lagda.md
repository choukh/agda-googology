# 对一般种类结构的数据树与折叠: 接口

> **接口定稿 2026-11-05 16:59 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: 2026-11-05 只增 §6 `LgDn` (合法向下封闭; 丢掉高度分量与读回经 `nw` 时要, 原 `HtTowerFTree.lgW≤` 的推广), 不改已有定义; 2026-11-05 只增 §7 `FbLgAt`, `FbLg` (A-回灌的顶坐标合法; 回灌的第一格 `sum (tpA w) z` 要它才能用 `rsLg`), 不改已有定义; 2026-11-05 只增 §8 `FbBdAt`, `FbBd` (把 A-回灌绑到种类 κ 上: 读出的 `A` 值经 `toE` 回到 κ 的坐标, 在原世界里在 κ 的界之下, 升界后 $v$ 在 κ 的界之下; 回应否定一路 `fba-swap`: `FBA` 的字段里不出现 κ), 不改已有定义.
>
> 不含记号. 本路 (前缀 `GenFold`) 是 [DnFold](DnFold.lagda.md) 接手清单第 2 条的**构造**一路: 把两种种类的数据树与折叠 ([HtTowerFTree](HtTowerFTree.lagda.md), [HtTowerFFold](HtTowerFFold.lagda.md), 对 `Ht = HB (step S₀)` 专门写) 推广到以种类结构 $K$ 为参数, 层在 `HB (step K)` (`KcFoldIf.LayK K`), 世界在 `Wd (step K)`, 给出 `DnFoldIf.EvSysK K` 的实例. 否定一路 (前缀 `NegGenFold`) 导入本文件, 不另造接口. 本篇只放类型, 记录与只由构造子组成的定义 (数据树与它的结点种类是类型), 不放证明与折叠. 导入 [HtTowerTy](HtTowerTy.lagda.md), [HtTowerFTree](HtTowerFTree.lagda.md) (只用 `Ht`), [KcFoldIf](KcFoldIf.lagda.md) (只用 `LayK`), [DnFoldIf](DnFoldIf.lagda.md) (只用 `EvSysK`), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **对象.**
>
> - **结点种类 `StH W k L`, 第一层判据 `NZ`, `NZ₁`, 可达 `AccY`** (§1): 与 `HtTowerFTree` 的同名对象同形, 对一切种类结构 `S` 一条定义.
> - **闭包结点的许可 `ZK K L κ`** (§2): 层 $L$ 的数据里能不能有种类 $\kappa$ 的闭包结点. 旧种类 (`inj₁`) 要 $L\neq0$ (`NZ`), 新种类 (`inj₂`) 要 $L\ge2$ (`NZ₁`). 这就是 `HtTowerFTree` 的 `nκ` 用 `NZ`, `nμ` 用 `NZ₁` 的推广: 对 `step K` 的两类种类按构造子分, 不按 $K$ 内部分.
> - **数据树 `DG₊ S Kd V Z`, `DataG.D S Z L W`, `DK K = DataG.D (step K) (ZK K)`** (§2): `HtTowerFTree.D₊` 的七个构造子 (`n0`, `n1`, `_⨾_`, `nl`, `ni`, `nw`), 加**一个对一切种类的闭包结点** `nc κ z u`: 种类 $\kappa$ 取遍层的种类结构的一切种类, 分支 `u` 对一切更大的合法世界 $W'$ (与 `nμ` 同形); 分支所在的坐标是 $W'$ 里 $\kappa$ 的顶坐标 `top κ W′ : E κ` (§3 `TopG`), 坐标类型就是该种类的坐标类型. 两种种类时, `nc κA` 与 `nκ`, `nc κH` 与 `nμ` 逐结点互译 (构造文件).
> - **每种类的结构 `TopG`, `FBA`, `GenK K`** (§3): 顶坐标 (每个种类在每个世界里的界本身, 同 `NegKcFoldDec.TopK` 的前两个字段); `FBA S κ`: 种类 $\kappa$ 的 **A-回灌** (界读成 `A`, 能把界升到给定的 `A` 值, 升高后的世界更大且合法); `GenK K`: 顶坐标, 基世界, 一个**底种类** `aK` (坐标读成 `A`, 单调), 与每个种类的可选 A-回灌 `fbA κ : FBA K κ ⊎ ⊤`.
> - **折叠的类型 `FoldTy.RunTy`** (§4): 与 `HtTowerFFold.Run` 同形, 层与世界换成 `HB (step K)`, `Wd (step K)`; 状态 `St` 记 `Df` 与第 0, 1 层自当前世界以来的输出.
> - **到接口的钩子 `EvGenTy K = GenK K → EvSysK K`** (§5) 与塔上的下降的类型 `DnGenTy` (对一切 $x$ 的 `GenK (Lev x)` 给出 `DnTower`).
>
> **律的定义域 (逐条).** 律里出现的每一对下标都带字面公共上界, 或者根本不比较两个下标:
>
> - `TopG.topBd`: 一个种类, 一个世界; 不比较.
> - `FBA.rs≤`: 一个世界 $w$, 一个 `A` 值 $v$, 前提 `tpA w ⊲ v` 是 `A` 上的字面第一位置 (`A` 的 `⊲` 不带世界, 是字面的); `rsLg`, `tp-rs` 同. 不比较两个种类, 不判定种类相等.
> - `GenK.frE-mono`: 两个坐标 $e,e'$ 都在同一个世界 $w$ 的 `aK`-界之下 (`Bd K aK e w`, `Bd K aK e′ w`), 这就是公共上界; `frE-lg` 只有一个坐标.
> - `GenK.fbA`: 是对每个种类给出的数据 (函数), 不是律, 不判定 "两个种类是否相同". 实例对种类结构的构造子递归给出 (`step` 的新种类给 `inj₂ tt`, 并的分量在下标能判定时提升, 否则给 `inj₂ tt`).
> - 折叠里唯一的比较是 `cmpB` (目标与结点的层, 公共上界是最高层 $\Lambda$, 同 `HtTowerFFold.rkT`).
>
> **为什么不撞 `HtTowerNStage.no-wmatch`.** 那里否定的是: 逐分量拼接的并 `U′` 里两个种类 $(0,\mathrm{new})$, $(1,\text{左}(0,\mathrm{new}))$ 在 `L′ 2` 里是同一个种类, 一个世界映射不能同时保两个界. 本接口**没有种类结构之间的世界映射**: 数据树的种类就是层的种类结构 `step K` 的种类 (恒等), 世界就是 `Wd (step K)` (恒等), 新种类坐标 `HB K` 里的 $\Omega$-结点的种类就是 `step K` 的旧种类 `inj₁ κ` (定义相等, `Bd (step K) (inj₁ κ) c w = Bd K κ c (proj₁ w)`). 没有两个种类被认成同一个. 回灌升高的是**一个种类在一个世界里的界** (`FBA.rsA`, 或新种类的界 `(proj₁ w , v)`), 不搬到别的结构. 代价 (构造文件, 判断): 并的世界是逐分量的积, 升高分量 $i$ 的界要对下标 $i$ 判定 "是不是这个分量" (函数更新); 下标是坐标 (`A`, `HB _`) 时判定不了, 这些种类只能有损地回灌 (`fbA κ = inj₂ tt`). 这是本路的第一个障碍, 不是 `no-wmatch`.
>
> **`no-retract` 与壁垒 (检查).** 闭包结点的分支对一切更大的世界, 不判定坐标在不在某个界之下; `fbA` 不判定种类相等; 折叠只在公共上界之下比较层. [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** `EvGenTy` 的类型被常数求值满足 (`evH = λ _ _ _ → hz`); `FBA` 被 "不升高" 满足 (`tpA w = azero`, `rsA w v = w` 时 `rs≤` 成立, 但 `tp-rs` 不成立; 所以 `tp-rs` 是唯一说 "升高真的看见 $v$" 的律, 它也不说大小). 接口不决定值 (手册 §3.3, §3.7).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GenFoldIf where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht)
open import OCF.Align.LvKtIf using (Kc)
open import OCF.Align.KcFoldIf using (LayK; DnTower)
open import OCF.Align.DnFoldIf using (EvSysK)
```

## §1 结点种类, 第一层判据, 可达 (对一切种类结构)

```agda
module _ {S : KS} where
  data StH (W : Wd S) (k : HB S) : HB S → Set where
    ss : ∀ {b} → k ⊲[ W ] b → StH W k (hs b)
    sl : ∀ {f} n → k ⊲[ W ] f n → StH W k (hl f)
    sL : ∀ {κ g c} → Bd S κ c W → k ⊲[ W ] g c → StH W k (hΩ κ g)

  NZ : HB S → Set
  NZ hz = ⊥
  NZ (hs _) = ⊤
  NZ (hl _) = ⊤
  NZ (hΩ _ _) = ⊤

  NZ₁ : HB S → Set
  NZ₁ hz = ⊥
  NZ₁ (hs b) = NZ b
  NZ₁ (hl _) = ⊤
  NZ₁ (hΩ _ _) = ⊤

  data AccY (L : HB S) : Set where
    acc : (∀ {W k} → StH W k L → AccY k) → AccY L
```

## §2 数据树: 一个对一切种类的闭包结点

```agda
module _ (S : KS) (Kd : Wd S → HB S → Set) (V : ∀ {W k} → Kd W k → Wd S → Set) (Z : K S → Set) where
  infixl 6 _⨾_
  data DG₊ : Wd S → Set where
    n0  : ∀ {W} → DG₊ W
    n1  : ∀ {W} → DG₊ W
    _⨾_ : ∀ {W} → DG₊ W → DG₊ W → DG₊ W
    nl  : ∀ {W} → (ℕ → DG₊ W) → DG₊ W
    ni  : ∀ {W k} (r : Kd W k) → (∀ {W′} → _≤w_ S W W′ → LgW S W′ → V r W′ → DG₊ W′) → DG₊ W
    nc  : ∀ {W} (κ : K S) → Z κ → (∀ {W′} → _≤w_ S W W′ → LgW S W′ → DG₊ W′) → DG₊ W
    nw  : ∀ {W₀ W} → _≤w_ S W₀ W → DG₊ W₀ → DG₊ W

module DataG (S : KS) (Z : HB S → K S → Set) where
  D  : HB S → Wd S → Set
  Vs : ∀ L {W k} → StH W k L → Wd S → Set
  Vc : ∀ b {W a} → a ⊲[ W ] b → Wd S → Set
  D L = DG₊ S (λ W k → StH W k L) (λ R → Vs L R) (Z L)
  Vs (hs b) (ss P) u = Vc b P u
  Vs (hl f) (sl n P) u = Vc (f n) P u
  Vs (hΩ κ g) (sL e P) u = Vc (g _) P u
  Vc a hself u = D a u
  Vc (hs b) (hsuc P) u = Vc b P u
  Vc (hl f) (hlim n P) u = Vc (f n) P u
  Vc (hΩ κ g) (hLim e P) u = Vc (g _) P u

-- 层在 HB (step K): 旧种类要 L ≠ 0, 新种类要 L ≥ 2
ZK : (T : KS) → HB (step T) → K (step T) → Set
ZK T L (inj₁ _) = NZ L
ZK T L (inj₂ _) = NZ₁ L

DK : (T : KS) → LayK T → Wd (step T) → Set
DK T = DataG.D (step T) (ZK T)
```

## §3 每种类的结构

```agda
record TopG (S : KS) : Set where
  field
    top   : (κ : K S) → Wd S → E S κ
    topBd : ∀ κ w → Bd S κ (top κ w) w
open TopG public

record FBA (S : KS) (κ : K S) : Set where
  field
    tpA   : Wd S → A
    rsA   : Wd S → A → Wd S
    rs≤   : ∀ {w v} → tpA w ⊲ v → _≤w_ S w (rsA w v)
    rsLg  : ∀ {w v} → LgW S w → Lg v → LgW S (rsA w v)
    tp-rs : ∀ {w v} → v ⊲ tpA (rsA w v)
open FBA public

record GenK (T : KS) : Set where
  field
    tpK      : TopG T
    w₀       : Wd T
    lw₀      : LgW T w₀
    aK       : K T
    frE      : E T aK → A
    frE-lg   : ∀ {e} → LgE T aK e → Lg (frE e)
    frE-mono : ∀ {w e e′} → LgW T w → Bd T aK e w → Bd T aK e′ w → Pr T aK w e e′ → frE e ⊲ frE e′
    fbA      : (κ : K T) → FBA T κ ⊎ ⊤
open GenK public
```

## §4 折叠的类型

```agda
module FoldTy (T : KS) (Λ : HB (step T)) where
  open DataG (step T) (ZK T)

  L₀ : KS
  L₀ = step T

  LW : HB L₀ → Wd L₀ → Set
  LW L W = L ⊲[ W ] Λ

  record Tg (W : Wd L₀) (t : HB L₀) (m : Wd L₀) : Set where
    constructor tg
    field
      wm : _≤w_ L₀ W m
      tm : t ⊲[ m ] Λ
      lm : LgW L₀ m

  record Df (W : Wd L₀) : Set where
    constructor df
    field
      yc : ∀ {t m} → Tg W t m → D t m

  record St (W : Wd L₀) : Set where
    constructor st
    field
      d  : Df W
      z  : D hz W
      z₁ : D (hs hz) W

  Ig : HB L₀ → Wd L₀ → Set
  Ig ly W = ∀ {W′} → _≤w_ L₀ W W′ → LgW L₀ W′ → D ly W′ → St W′ → Df W′

  RunTy : Set
  RunTy = ∀ {ly W₀ W} → AccY ly → D ly W₀ → _≤w_ L₀ W₀ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Df W
```

## §5 到接口的钩子与塔上的下降

```agda
EvGenTy : KS → Set₁
EvGenTy T = GenK T → EvSysK T

-- 对一切 x 的 GenK (Lev x) 给出塔上的下降 (层号是后继 hs x 时, Lev (hs x) = step (Lev x), 输入就是层)
DnGenTy : Set₁
DnGenTy = (∀ {S : KS} (x : HB S) → GenK (Lev x)) → DnTower

-- 第 1 站的种类结构 (决定性实验的对象)
K₁ : KS
K₁ = Kc 1
```

**定稿时刻.** 2026-11-05 16:59 (首次编译通过).

## §6 只增: 合法向下封闭

```agda
record LgDn (T : KS) : Set where
  field
    lgDn : ∀ {u v} → _≤w_ T u v → LgW T v → LgW T u
open LgDn public
```

`LgDn.lgDn` 的定义域: 两个世界 $u\le v$, 一个方向; 不比较下标.

## §7 只增: A-回灌的顶坐标合法

```agda
FbLgAt : ∀ {T : KS} {κ : K T} → FBA T κ ⊎ ⊤ → Set
FbLgAt {T} (inj₁ F) = ∀ {w} → LgW T w → Lg (tpA F w)
FbLgAt (inj₂ _) = ⊤

FbLg : ∀ {T : KS} → GenK T → Set
FbLg {T} G = ∀ κ → FbLgAt {T} {κ} (fbA G κ)
```

定义域: 一个种类, 一个世界; 不比较.

## §8 只增: A-回灌绑到种类上

`FBA S κ` 的字段不提 κ (否定一路 `NegGenFold` 的 `fba-swap`). 这里补上: 有一个 `A → E κ` 的读法 `toE`, 原世界的读数在 κ 的界之下 (`tp-bd`), 升界之后 $v$ 在 **κ 的**界之下 (`rs-bd`).

```agda
record FBABd (S : KS) (κ : K S) (F : FBA S κ) : Set where
  field
    toE   : A → E S κ
    tp-bd : ∀ {w} → Bd S κ (toE (tpA F w)) w
    rs-bd : ∀ {w v} → Bd S κ (toE v) (rsA F w v)
open FBABd public

FbBdAt : ∀ {T : KS} {κ : K T} → FBA T κ ⊎ ⊤ → Set
FbBdAt {T} {κ} (inj₁ F) = FBABd T κ F
FbBdAt (inj₂ _) = ⊤

FbBd : ∀ {T : KS} → GenK T → Set
FbBd {T} G = ∀ κ → FbBdAt {T} {κ} (fbA G κ)
```

定义域: 一个种类, 一个世界, 一个 `A` 值; 不比较两个下标.
