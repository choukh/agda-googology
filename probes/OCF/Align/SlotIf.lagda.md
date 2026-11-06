# 高度坐标的共享槽: 接口

> **接口定稿 2026-11-05 20:03 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项"; 本轮作者选定 (原话): "高度坐标的共享槽小实验". 本路 (前缀 `Slot`) 是构造一路; 否定一路 (前缀 `NegSlot`) 导入本文件, 不另造接口. 本篇只放类型与记录, 不放证明. 导入 [HtTowerTy](HtTowerTy.lagda.md), [GenFoldIf](GenFoldIf.lagda.md) (`TopG`, `K₁`), [GenFoldInst](GenFoldInst.lagda.md) (`genKc`), [RsOwnIf](RsOwnIf.lagda.md) (`RsK`), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **问题.** [RsOwn](RsOwn.lagda.md) 的形状 1: 世界带 "一切底拷贝同界" 证据时, 底拷贝 (坐标都是 `A`) 可以一起升, 不判定下标. 对坐标是高度, 坐标类型随下标变的一族种类 (`K₁` 的 `κH c`, 坐标 `HB (Lev c)`), "同界" 无从说起: 界不在同一个类型里. 设想: 世界证据带一个**共享槽** (一个公共的种类结构 $Q$ 的一个种类 $\kappa_0$, 它的坐标类型与世界类型是公共的) 与一族**搬运** (每个成员的坐标与 $\kappa_0$ 的坐标互译, 每个成员所在的世界投影到 $Q$ 的世界), 让一起升经共享槽进行.
>
> ## 对象
>
> - **`Dg J X` (§1, 对角解码).** 一族类型 $X_j$ 之间的映射 $\mathrm{dc}\,j\,j' : X_j\to X_{j'}$, 对角上是恒等 ($\mathrm{dc}\,j\,j\,x\equiv x$). 任何对一切成员一致的升界族 (`RsFam`, 满足 `rs-top`) 都给出一个 (构造文件 `SlotGen.rsFam→Dg`): 这是共享槽的**必要**条件的最小形式.
> - **`Slot T tp J κJ Q tq κ₀` (§2).** 种类结构 $T$ 里一族种类 $\kappa_j$ ($j:J$, $J$ 可以含函数) 经共享槽 $(Q,\kappa_0)$:
>   - 坐标的搬运 `cE j`, 读回 `cE⁻ j`, 读回是左逆 (`cE⁻-cE`; 共享后读回不丢).
>   - 世界的读 `wpr j : Wd T → Wd Q` (成员 $j$ 所在的那份共享世界), 写 `wset ω` (把**一切**成员所在的共享世界都置成 $\omega$; 不判定下标).
>   - `Al P w`: 世界 $w$ 里每一份共享世界满足 $P$ (`al-pr` 读出其中第 $j$ 份).
>   - 律: 第一位置沿搬运两个方向都保 (`pr→`, `pr←`), 合法两个方向都保 (`lgE→`, `lgE←`, `lgπ`), 顶坐标沿搬运 (`top-cp`), 写后每份都是 $\omega$ (`al-set`), 每份都 $\le\omega$ 时世界变大 (`set-≤`), 写出的世界是 "比 $w$ 大且每份都 $\ge\omega$" 的世界里最小的 (`set-least`), 合法 (`set-lg`).
> - **`ShW S w` (§2, 世界证据).** 存在 $\omega$, 世界 $w$ 里每一份共享世界 $\equiv\omega$. 它是 [RsOwnSW](RsOwnSW.lagda.md) 的 `Uf` 的推广: `Uf` 的公共值是 `A` 的元素, 这里是 $Q$ 的世界.
> - **`RsFam T tp J κJ` (§3).** 对一切成员的 `RsK` (接口 [RsOwnIf](RsOwnIf.lagda.md) §1, 即 `KLv` 的 `rs≤`, `rsLg`, `rs-top`).
> - **`κHc c` (§4).** `K₁` 的种类 `(inj₂ (hs c) , inj₂ tt)`, 坐标 `HB (Lev c)` ($c$ : `H₀`, 可以含函数); 原卡点的 `κH f` 就是 `κHc (jx f)`. 否定一路对它写结论时用这个名字.
>
> ## 律的定义域 (逐条)
>
> - `cE⁻-cE`, `lgE→`, `lgE←`, `lgπ`, `top-cp`: 一个成员 $j$, 一个值或一个世界. 不比较两个下标.
> - `pr→`, `pr←`: 一个成员 $j$, 同一个世界里一对坐标的第一位置; 公共上界是这一对的后一个.
> - `al-pr`: 一个成员, 一个世界. `al-map`: 一个世界上两个谓词.
> - `al-set`, `set-≤`, `set-least`, `set-lg`: 对一切成员说话, 但只经 `Al`, 而 `Al` 里每一份都与**同一个字面的** $\omega$ 比 (公共上界或公共下界就是 $\omega$); 两个成员 $j, j'$ 从不直接比较.
> - `Dg.dc-d`: 一个下标 (对角). 非对角的 $\mathrm{dc}\,j\,j'$ 没有律.
> - `ShW`: 一个世界上的证据, 公共值是字面的 $\omega$.
>
> **`no-retract` 与壁垒 (检查).** 接口不要求任何下标类型上的三歧或判定. `Slot` 要每个成员的坐标类型是 $\kappa_0$ 的坐标类型的收缩 (`cE⁻-cE`); 若 $Q$ 是 $T$ 的某个成员自己所在的级, 这可能撞 `HtTowerNeg.no-retract` (构造文件 `SlotKH` 对 `κHc` 写出这一条). [判断] 接口本身不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** `Slot` 不说共享槽以外的界 (例如 `step` 的高度界) 怎样变, 只由 `set-≤`, `set-least` 约束; `ShW` 可以被 "一族为空" ($J$ 空) 空真地满足, 所以用它时给基世界的证据与一个非空的成员族 (构造文件). `Dg` 不说非对角的映射是否保序.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SlotIf where

open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀)
open import OCF.Align.GenFoldIf using (TopG; top; tpK; K₁)
open import OCF.Align.GenFoldInst using (genKc)
open import OCF.Align.RsOwnIf using (RsK)
```

## §1 对角解码

```agda
record Dg (J : Set) (X : J → Set) : Set where
  field
    dc   : ∀ j j′ → X j → X j′
    dc-d : ∀ j x → dc j j x ≡ x
open Dg public
```

## §2 共享槽

```agda
record Slot (T : KS) (tp : TopG T) (J : Set) (κJ : J → K T) (Q : KS) (tq : TopG Q) (κ₀ : K Q) : Set₁ where
  field
    -- 坐标的搬运与读回 (一个成员)
    cE     : ∀ j → E T (κJ j) → E Q κ₀
    cE⁻    : ∀ j → E Q κ₀ → E T (κJ j)
    cE⁻-cE : ∀ j e → cE⁻ j (cE j e) ≡ e
    -- 世界的读 (一个成员)
    wpr    : J → Wd T → Wd Q
    lgπ    : ∀ j {w} → LgW T w → LgW Q (wpr j w)
    pr→    : ∀ j {w e e′} → Pr T (κJ j) w e e′ → Pr Q κ₀ (wpr j w) (cE j e) (cE j e′)
    pr←    : ∀ j {w x x′} → Pr Q κ₀ (wpr j w) x x′ → Pr T (κJ j) w (cE⁻ j x) (cE⁻ j x′)
    lgE→   : ∀ j {e} → LgE T (κJ j) e → LgE Q κ₀ (cE j e)
    lgE←   : ∀ j {x} → LgE Q κ₀ x → LgE T (κJ j) (cE⁻ j x)
    top-cp : ∀ j w → cE j (top tp (κJ j) w) ≡ top tq κ₀ (wpr j w)
    -- 一切成员 (经同一个字面的 ω)
    Al     : (Wd Q → Set) → Wd T → Set
    al-map : ∀ {P R : Wd Q → Set} → (∀ {x} → P x → R x) → ∀ {w} → Al P w → Al R w
    al-pr  : ∀ j {P w} → Al P w → P (wpr j w)
    wset   : Wd Q → Wd T → Wd T
    al-set : ∀ ω w → Al (λ x → x ≡ ω) (wset ω w)
    set-≤  : ∀ {ω w} → Al (λ x → _≤w_ Q x ω) w → _≤w_ T w (wset ω w)
    set-least : ∀ {ω w w′} → _≤w_ T w w′ → Al (λ x → _≤w_ Q ω x) w′ → _≤w_ T (wset ω w) w′
    set-lg : ∀ {ω w} → LgW T w → LgW Q ω → LgW T (wset ω w)
open Slot public

-- 世界证据: 每一份共享世界都是同一个 ω
ShW : ∀ {T tp J κJ Q tq κ₀} → Slot T tp J κJ Q tq κ₀ → Wd T → Set
ShW {Q = Q} S w = Σ (Wd Q) (λ ω → Al S (λ x → x ≡ ω) w)
```

## §3 一族种类的一致升界

```agda
RsFam : (T : KS) → TopG T → (J : Set) → (J → K T) → Set
RsFam T tp J κJ = ∀ j → RsK T tp (κJ j)
```

## §4 原卡点的一族: `K₁` 里坐标是 `HB (Lev c)` 的种类

```agda
tp₁ : TopG K₁
tp₁ = tpK (genKc 1)

κHc : H₀ → K K₁
κHc c = inj₂ (hs c) , inj₂ tt
```
