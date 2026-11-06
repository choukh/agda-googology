# 一次封闭层号上带证据的回灌: 接口

> **接口定稿 2026-11-05 20:06 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: 2026-11-05 只改文字, 不改代码: 文件头 "盲" 一段关于 `AK` 的那句 ("被常数 `fr` 满足当且仅当 `Pr` 只在相等时成立") 有误, 更正为: **`AK` 被常数 `fr = λ _ → azero` 满足, 对一切 $Q$, $\kappa$** (`fr-mono` 用 `A` 的 `⊲` 的自反; 否定一路 `NegSLFbBlind.akConst`). 所以 `AK` 不说读回读了什么; 构造文件的 `fr` 是 `frE⊥`.

> 不含记号. 目标 (作者原话): "写出 ψ₀Λ 的候选闭项"; 本轮作者选定 (原话): "SL 上写带证据的回灌". 本路 (前缀 `SLFb`) 是构造一路; 否定一路 (前缀 `NegSLFb`) 导入本文件, 不另造接口. 本篇只放类型, 记录与只由构造子组成的定义, 不放证明. 导入 [HtTowerTy](HtTowerTy.lagda.md), [GenFoldIf](GenFoldIf.lagda.md) (`TopG`), [KindLvIf](KindLvIf.lagda.md) (`KLv`, `LvFb`), [LFReTy](LFReTy.lagda.md) (`LH`, `Lv`, `FL`, `SL`, `νL`, `ofHB`), [RsOwnIf](RsOwnIf.lagda.md) (`RsK`, `RsInv`), 都不改. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **问题 (C6 在 `SL` 上).** `SL = sup LH FL` 的世界是以层号 `LH` 为下标的积. 第 $n\ge2$ 站的层号 `ofHB (tw n)` 含函数分支 (`lΩ lz g`); 把新种类 `νL k₀` 的界升到 $v$ 而 "别处不升" 要对含函数的层号判等 (`NegGenFoldUpd.upd₁-sep` 一族; 否定一路 `NegSLFbSep.updP-sep` 对单个 `lΩ` 下标). 本接口把两条出口写成记录:
>
> ## 对象
>
> - **站下标的子结构 `SNᵢ ix` (§1).** 给一列层号 `ix : ℕ → LH` (构造文件取站 `ofHB (tw n)`), `SNᵢ ix = sup ℕ (FL ∘ ix)`: 种类 $(n,\kappa)$ 就是 `SL` 的种类 $(ix\,n,\kappa)$ (`jN`, 坐标类型定义相等), 世界是 `SL` 的世界限制到站下标上 (`resN`, 界定义相等). **证据是站号 $n$ 本身**: 两个站号的相等在 $\mathbb N$ 上判定, 对角上是 `refl`; 层号 `ix n` 可以含函数, 不被比较.
> - **可读成 `A` 的种类 `AK Q` (§2).** 坐标经 `fr` 读成 `A`, 在同一世界的界之下单调 (同 `GenK` 的 `aK`/`frE` 三个字段). 构造文件用它把第 1 层的数据读进某一层的值 (级回灌的读回).
> - **第 0 级的回灌件 `KC Q tp κ` (§2).** 坐标上 "加一个 `A`" (`ad`, 结果以原坐标为第一位置, 合法) 与精确升界 `RsK Q tp κ` (`RsOwnIf` §1: `rs≤` 的前提是旧顶 $\lhd v$, `rs-top` 是精确 `≡`). 构造文件由它造级层为 $0$ 的 `KLv`.
> - **每站头种类有回灌 `HdFb` (§3).** 对一切站号 $n$, 头种类 $(n,\mathrm{new})$ (坐标 `HB (Lv (ix n))`, 是高度) 的 `lv` 给出 `KLv`.
> - **`SL` 本身上的升界形状 (§4, 给否定一路的对象).** `RsSL`: 对一切层号 $k$ 的 `νL k`, 世界不带证据的精确升界 (`RsK`). `RsSLᴾ P`: 世界带证据 $P$ (`RsInv`). `RsSL⊵`: 只要求 $v$ 是新顶的第一位置 (不要求 `≡`; "一起抬高" 的律). `RsEv w* Λ*`: 只对带字面公共上界证据 `h ⊲[ w* ] Λ*` 的层号 `ofHB h` 要求精确升界 (`StallDxBdec.bdec` 的情形).
>
> ## 律的定义域 (逐条)
>
> 律里出现的每一对下标都带字面公共上界, 或者根本不比较两个下标:
>
> - `AK.fr-mono`: 一个种类, 两个坐标 $e,e'$ 都在同一世界 $w$ 的界之下 (`Bd Q κa e w`, `Bd Q κa e′ w`), 公共上界是该界. `fr-lg`: 一个坐标.
> - `KC.ad-fst`: 一对 $(b, \mathrm{ad}\,b\,a)$, 公共上界是后者; `ad-lg`: 一个值. `KC.rk`: 见 `RsK` (`rs≤` 的前提是 $(\mathrm{top}_\kappa w, v)$ 的第一位置, 公共上界 $v$; 结论是两个世界; `rs-top` 是一个种类的坐标类型里的 `≡`).
> - `HdFb`: 对每个站号给数据, 不比较两个站号; 构造文件在 $\mathbb N$ 上做点更新 (`GenFoldInst.upd`), 那是对 $\mathbb N$ 的判定, 不是对层号.
> - `RsSL`, `RsSLᴾ`: 对每个层号 $k$ 给一个升界, 不比较两个层号; 律同 `RsK`/`RsInv`. **接口里没有 "别的分量不动" 一类的律** (没有 `¬ (k ≡ s)` 形式的前提).
> - `RsSL⊵.rs⊵`: 一对 $(v, \mathrm{top}_\kappa(\mathrm{rs}\,w\,v))$, 公共上界是后者, 在升后的世界里.
> - `RsEv`: 每个下标带 `h ⊲[ w* ] Λ*`; 任两个这样的下标有字面公共上界 $\Lambda^*$ (同一世界 $w^*$).
>
> **证据类是否含基世界.** `RsSLᴾ P` 要配 $P$ 的实例; 构造文件或否定文件用到它时, 要写明 $P$ 在 `FabLFReGen` 的基世界 (`w₀ GL`) 上成立与否. `SNᵢ` 没有证据类 (证据在种类的下标里), 它的基世界是 `resN` 下 `SL` 基世界的限制.
>
> **`no-retract` 与壁垒 (检查).** `SNᵢ` 的种类的坐标是 `HB (Lv (ix n))` 或 `Lv (ix n)` 的种类的坐标, 都不是 `HB (SNᵢ ix)`; 最终层在 `HB (step (SNᵢ ix))`. 接口不要求任何下标类型上的三歧或判定 (站号的判定是 $\mathbb N$ 的). [判断] 不触壁垒; 否定一路若找到反例, 以它为准.
>
> **接口不管什么 (盲).** `KC` 被 `ad b a = b` 满足 (`ad-fst` 用自反), 所以 `ad` 的内容在构造文件里看 (那里 `ad b a = b ⊞ toB a`); `HdFb` 不说读回读了什么, 不说级层是哪一层; `AK` 被常数 `fr` 满足当且仅当 `Pr` 只在相等时成立 (一般不满足, 但不是律). 接口不决定值 (手册 §3.3, §3.7).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SLFbIf where

open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (TopG; top)
open import OCF.Align.KindLvIf using (KLv; LvFb)
open import OCF.Align.LFReTy using (LH; Lv; FL; SL; νL; ofHB)
open import OCF.Align.RsOwnIf using (RsK; RsInv)
```

## §1 站下标的子结构

```agda
SNᵢ : (ℕ → LH) → KS
SNᵢ ix = sup ℕ (λ n → FL (ix n))

-- SNᵢ 的种类就是 SL 的种类 (坐标类型定义相等)
jN : ∀ {ix} → K (SNᵢ ix) → K SL
jN {ix} (n , κ) = ix n , κ

-- SL 的世界限制到站下标上 (界定义相等)
resN : ∀ ix → Wd SL → Wd (SNᵢ ix)
resN ix w n = w (ix n)
```

## §2 可读成 `A` 的种类; 第 0 级的回灌件

```agda
record AK (Q : KS) : Set where
  field
    κa      : K Q
    fr      : E Q κa → A
    fr-lg   : ∀ {e} → LgE Q κa e → Lg (fr e)
    fr-mono : ∀ {w e e′} → LgW Q w → Bd Q κa e w → Bd Q κa e′ w → Pr Q κa w e e′ → fr e ⊲ fr e′
open AK public

record KC (Q : KS) (tp : TopG Q) (κ : K Q) : Set where
  field
    ad     : E Q κ → A → E Q κ
    ad-fst : ∀ {w} b a → Pr Q κ w b (ad b a)
    ad-lg  : ∀ {b a} → LgE Q κ b → Lg a → LgE Q κ (ad b a)
    rk     : RsK Q tp κ
open KC public
```

## §3 每站头种类有回灌

```agda
HdFb : (ix : ℕ → LH) (tp : TopG (SNᵢ ix)) (Λ : HB (step (SNᵢ ix))) → LvFb (SNᵢ ix) tp Λ → Set
HdFb ix tp Λ lv = ∀ n → Σ (KLv (SNᵢ ix) tp Λ (n , inj₂ tt)) (λ L → lv (n , inj₂ tt) ≡ inj₁ L)
```

## §4 `SL` 本身上的升界形状 (否定一路的对象)

```agda
-- 世界不带证据, 对一切层号的新种类精确升界
RsSL : TopG SL → Set
RsSL tp = (k : LH) → RsK SL tp (νL k)

-- 世界带证据 P
RsSLᴾ : (Wd SL → Set) → TopG SL → Set
RsSLᴾ P tp = (k : LH) → RsInv SL P tp (νL k)

-- 一起抬高: 只要求 v 是新顶的第一位置
record RsUp (T : KS) (tp : TopG T) (κ : K T) : Set where
  field
    rsu   : Wd T → E T κ → Wd T
    rsu≤  : ∀ {w v} → Pr T κ w (top tp κ w) v → _≤w_ T w (rsu w v)
    rsuLg : ∀ {w v} → LgW T w → LgE T κ v → LgW T (rsu w v)
    rs⊵   : ∀ {w v} → Pr T κ (rsu w v) v (top tp κ (rsu w v))
open RsUp public

RsSL⊵ : TopG SL → Set
RsSL⊵ tp = (k : LH) → RsUp SL tp (νL k)

-- 只对带字面公共上界证据的层号 (StallDxBdec.bdec 的情形)
RsEv : TopG SL → Wd SL → HB SL → Set
RsEv tp w* Λ* = (h : HB SL) → h ⊲[ w* ] Λ* → RsK SL tp (νL (ofHB h))
```
