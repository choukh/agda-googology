# 树的语言 (接口): 判据记录

> **接口定稿 2026-11-05 20:27 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 入口 [TreeLang](TreeLang.lagda.md). 构造一路 `TreeLang*` 与否定一路 `NegTreeLang*` 共用本篇. 本篇只放类型与记录 (候选定义的形状, 判据, 律的定义域), 不放证明. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **做什么.** 今天得到的树侧判据都是否定性的 ("不能怎样"). 本篇把它们整理成三种候选定义上的判据记录, 让下一步的定义可以**由判据推出**, 而不是先猜再验:
>
> 1. **层的生成规则** `LvRule S B` (§2): 对层号 $c$ 给一个种类结构 `L c`, 每个种类有一个级 `lv c κ` (底, 或某个层号 $y$), 坐标类型就是它的级给出的类型 (`coord`: 底给 $B$, 级 $y$ 给**候选自己的**第 $y$ 层的值 `HB (L y)`). 判据 `LvCrit` (§3): `base0` (第 0 层有底种类), `feed` (第 $x$ 层的值是第 $x+1$ 层某个种类的坐标), `inherit` (结构子项的级在上面仍有), `sub` (级是严格子项). 可选的字面上界 `LvUpper` (§3): 级 $y$ 只在 `hs y` 是 $c$ 的子项时出现.
> 2. **一次封闭的层号上的生成规则** `LvRuleL` (§4): 层号是 `LFReTy.LH`, 判据 `LvCritL` 多一条 `cof` (层号 `lΩ k g` 的分支取第 $k$ 层的值, 它的种类里要有级 $k$). 字面上界 `LvUpperL` 用 `Pass`.
> 3. **升界操作** `Raise F` (§5): 框架 `RaiseFrame` 给世界 $W$, 成员下标 $J$, 成员的键 `key : J → Key` (同键的成员是拷贝), 读数 `obs`, 以及**律的定义域** `Ev w j j′` (两个成员在世界 $w$ 里带字面公共上界的证据). 律 `set` (升到 $v$; 对 $j$ 的一切同键拷贝) 与 `keep` (不同键的成员不动) **只对带 `Ev` 证据的一对成员陈述**. 裸下标的律就是 `Ev` 恒有居留的特例 (`Bare`), 单列出来, 以便定理说清它推出什么.
>
> **每条判据来自哪里** (档写在括号里; 本篇只给出处, 推导在 [TreeLangLv](TreeLangLv.lagda.md), [TreeLangRaise](TreeLangRaise.lagda.md)):
>
> | 判据 | 出处 | 档 |
> |---|---|---|
> | `coord` (坐标是级给的类型) | `NegKindLvLev.coord-lv` (Lev 满足), `LFReTy.E-lvl` (Lv 满足) | 两个现有形状的共同性质, 定理; 作为对候选的要求是选择 |
> | 级不是自己 | `NegKindLvLev.lv-not-self`, `HtTowerNeg.no-retract`; 对一切满足 `coord` 的候选: `TreeLangLv.no-self` | 定理 |
> | `feed` | 交替路线 "折叠输出回灌作下标" (AGENTS); 级不是自己 (上一行) 说最早只能在 `hs x` | 回灌要求是纲领的最佳实践; "最早" 是定理 |
> | `inherit` | 嵌入 `HtTowerTy.up`, `ι` (低层的值保第一位置, 保合法地进高层) | 嵌入是定理; 要求级随之保留是选择 |
> | `sub` | 结构递归定义 (纲领 2: 检查器保证停机) 只能引用结构子项的层; `NegKindLvLev.lv-sub` | 判断 (另一种定义形式, 如归纳-递归, 不受此限) |
> | `cof` | `LFReTy.Lv` 的 `lΩ` 一行; 层号的分支域字面就是 `HB (Lv k)` | 字面的读法, 选择 |
> | `LvUpper`, `LvUpperL` | 只认字面证据 (AGENTS 交替路线 "字面的公共上界") | 选择 |
> | `Raise` 的 `Ev` | `StallDxBdec.bdec`; 分离子一族 `NegGenFoldUpd.upd₁-sep`, `NegStratTwDeep.updD-sep` (裸下标推出分离子) | 定理 |
>
> **律的定义域 (AGENTS "律带公共上界").** 逐条: `LvCrit.inherit` 的一对层号 $y, c$ 带字面子项证据 $y\prec c$; `feed`, `base0`, `cof` 只含一个层号; `sub`, `LvUpper` 每条只含一个层号与它的一个级, 结论是字面子项关系. `Raise.set`, `Raise.keep` 的每一对成员带 `Ev` 证据. 没有对裸下标的比较律; `Bare` 只是一个被定理引用的条件, 不是律.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLangIf where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerNeg using (_≺ᴮ_; ≺s; ≺l; ≺Ω)
open import OCF.Align.NegKindLvLev using (_⊏_; one; snoc)
open import OCF.Align.LFReTy using (LH; lz; ls; ll; lΩ; Lv)
```

## §1 字面子项

`_⊑ᴮ_`: 结构子项的自反传递闭包 (`HtTowerNeg._≺ᴮ_` 的闭包). 严格的版本用 `NegKindLvLev._⊏_`.

```agda
module _ {S : KS} where
  infix 4 _⊑ᴮ_
  data _⊑ᴮ_ : HB S → HB S → Set where
    rf : ∀ {x} → x ⊑ᴮ x
    sn : ∀ {x y z} → x ⊑ᴮ y → y ≺ᴮ z → x ⊑ᴮ z
```

## §2 候选: 层的生成规则 (层号是 `HB S`)

`Cdᴿ B L ℓ`: 级 $\ell$ 给的坐标类型. 底给 $B$; 级 $y$ 给候选自己的第 $y$ 层的值. 所以 `coord` 是自指的: 候选的坐标就是候选的低层.

```agda
Cdᴿ : ∀ {S : KS} → Set → (HB S → KS) → ⊤ ⊎ HB S → Set
Cdᴿ B L (inj₁ _) = B
Cdᴿ B L (inj₂ y) = HB (L y)

record LvRule (S : KS) (B : Set) : Set₁ where
  field
    L     : HB S → KS
    lv    : ∀ c → K (L c) → ⊤ ⊎ HB S
    coord : ∀ c κ → E (L c) κ ≡ Cdᴿ B L (lv c κ)
open LvRule public

-- 级 ℓ 在第 c 层出现
InLv : ∀ {S B} → LvRule S B → HB S → ⊤ ⊎ HB S → Set
InLv R c ℓ = Σ (K (L R c)) (λ κ → lv R c κ ≡ ℓ)
```

## §3 判据 (层号是 `HB S`)

```agda
-- 级是严格子项 (底不算)
SubLv : ∀ {S : KS} → HB S → ⊤ ⊎ HB S → Set
SubLv c (inj₁ _) = ⊤
SubLv c (inj₂ y) = y ⊏ c

record LvCrit {S : KS} {B : Set} (R : LvRule S B) : Set where
  field
    base0   : InLv R hz (inj₁ tt)
    feed    : ∀ x → InLv R (hs x) (inj₂ x)
    inherit : ∀ {y c} → y ≺ᴮ c → ∀ ℓ → InLv R y ℓ → InLv R c ℓ
    sub     : ∀ c κ → SubLv c (lv R c κ)
open LvCrit public

-- 可选的字面上界: 级 y 只在 hs y 是 c 的子项时出现
UpLv : ∀ {S : KS} → HB S → ⊤ ⊎ HB S → Set
UpLv c (inj₁ _) = ⊤
UpLv c (inj₂ y) = hs y ⊑ᴮ c

LvUpper : ∀ {S B} → LvRule S B → Set
LvUpper R = ∀ c κ → UpLv c (lv R c κ)
```

## §4 候选与判据: 一次封闭的层号 `LH`

`_≺ᴸ_`: `LH` 的直接子项. `lΩ k g` 有两种子项: 分支 $g\,c$, 与分支域的层号 $k$. `Pass y x`: $x$ 字面地越过第 $y+1$ 层 (有子项 `ls y` 或 `lΩ y g`).

```agda
data _≺ᴸ_ : LH → LH → Set where
  ≺ls : ∀ {x} → x ≺ᴸ ls x
  ≺ll : ∀ {f} n → f n ≺ᴸ ll f
  ≺lΩ : ∀ {k g} c → g c ≺ᴸ lΩ k g
  ≺lk : ∀ {k g} → k ≺ᴸ lΩ k g

data Pass (y : LH) : LH → Set where
  pls : Pass y (ls y)
  plΩ : ∀ g → Pass y (lΩ y g)
  pup : ∀ {x z} → Pass y x → x ≺ᴸ z → Pass y z

record LvRuleL : Set₁ where
  field
    Lᴸ     : LH → KS
    lvᴸ    : ∀ x → K (Lᴸ x) → LH
    coordᴸ : ∀ x κ → E (Lᴸ x) κ ≡ HB (Lᴸ (lvᴸ x κ))
open LvRuleL public

InLvL : LvRuleL → LH → LH → Set
InLvL R x y = Σ (K (Lᴸ R x)) (λ κ → lvᴸ R x κ ≡ y)

record LvCritL (R : LvRuleL) : Set where
  field
    feedᴸ    : ∀ x → InLvL R (ls x) x
    inheritᴸ : ∀ {y x} → y ≺ᴸ x → ∀ ℓ → InLvL R y ℓ → InLvL R x ℓ
    cofᴸ     : ∀ k g → InLvL R (lΩ k g) k
open LvCritL public

LvUpperL : LvRuleL → Set
LvUpperL R = ∀ x κ → Pass (lvᴸ R x κ) x
```

## §5 候选与判据: 升界操作

框架: 世界 `W`, 成员 `J`, 键 `key` (同键 = 拷贝, 一起升), 读数 `obs`, 律的定义域 `Ev`. 候选 `Raise F`: 升界 `rs`, 两条律只对带 `Ev` 证据的一对成员.

```agda
record RaiseFrame : Set₁ where
  field
    W   : Set
    J   : Set
    Key : Set
    V   : Set
    key : J → Key
    obs : J → W → V
    Ev  : W → J → J → Set
open RaiseFrame public

record Raise (F : RaiseFrame) : Set where
  field
    rs   : W F → J F → V F → W F
    set  : ∀ {w j j′} v → Ev F w j j′ → key F j′ ≡ key F j → obs F j′ (rs w j v) ≡ v
    keep : ∀ {w j j′} v → Ev F w j j′ → ¬ (key F j′ ≡ key F j) → obs F j′ (rs w j v) ≡ obs F j′ w
open Raise public

-- 裸下标: 律的定义域是一切成员对 (被定理引用的条件, 不是律)
Bare : RaiseFrame → Set
Bare F = ∀ w j j′ → Ev F w j j′
```
