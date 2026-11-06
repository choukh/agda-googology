# 树的语言, 第二对 (接口): 四条正面判据

> **接口定稿 2026-11-05 21:12 (首次编译通过).** 定稿之后只增不改; 若必须改, 在这里写变更记录. 变更记录: (无).
>
> 不含记号. 入口 [TL2](TL2.lagda.md). 构造一路 `TL2*` 与否定一路 `NegTL2*` 共用本篇. 本篇导入上一对的接口 [TreeLangIf](TreeLangIf.lagda.md) (未改), **只增**四条正面判据; 只放类型与记录, 不放证明. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用函数外延, 不用 UIP.
>
> **为什么要这四条.** 上一对的结论 (否定一路 `NegTreeLang`): `LvCrit` + `LvUpper` 定死了级集合, 但被一切 Ω-极限退化的平的候选 `Fl` 满足 (`NegTreeLangFlat.fl-const`); `Raise` 对定义域向下封闭 (`shrink`, `diag-raise`), 没有世界变大的律 (`any-lowers`), 单一读数类型装不下相邻两级 (`raise-adj`). 否定一路列出缺的四条正面判据; 本篇把它们写成记录:
>
> | 判据 | 记录 | 说什么 | 对哪个否定 |
> |---|---|---|---|
> | (i) 顺序一致 | `OrdCrit R` (层号 `HB S`), `OrdCritL R` (层号 `LH`) | 级为 $y$ 的种类, 它的第一位置 `Pr` 与坐标 (沿 `coord` 读成第 $y$ 层的高度) 在投影世界里的 `⊲` 互推; 第 $c$ 层的世界投影到它每个级的世界 (`prj`) | `fl-const` |
> | (ii) 异键对 | `HKey`, `CrossOn`, `Cross F H` | 键读成某个种类结构上的高度; 两个成员的键是同一合法高度在同一合法世界里的字面第一位置时, 这一对**必须**在律的定义域 `Ev` 里 | `shrink`, `diag-raise` |
> | (iii) 升界保序 | `OrdFrame`, `Above`, `Grow`, `RaiseUp` | 世界的序与读数的序; 新值在一切同键读数之上时世界变大 (`Grow`, 照 `RsOwnIf.RsK.rs≤` 的条件形); `RaiseUp`: 升界只对这样的值给出 | `any-lowers` |
> | (iv) 读数随成员变 | `DFrame`, `DRaise`, `constD`, `DOrd`, `DAbove`, `DGrow`, `DCross` | 读数类型 `Vᴰ j` 随成员变; 升界的值是成员上的截面 (每个同键成员取自己的值, 不沿相等证明搬运) | `raise-adj`, `raise-tag` |
>
> **律的定义域 (AGENTS "律带公共上界").** (i) 每条只含一个层号 $c$, 它的一个种类, 一个世界与两个坐标 (同一种类, 同一世界: 公共上界由同一世界给, 与 `cmpK` 相同), 没有两个层号之间的比较. (ii) 是对定义域的**要求**, 前提正是一对键的字面公共上界 (`⊲[ ω ] Lb`, 带合法性). (iii), (iv) 的律与上一对的 `set`, `keep` 一样只对带 `Ev` (`Evᴰ`) 证据的成员对陈述; `Above` 只量化带证据的同键成员. 没有对裸下标的比较律.
>
> **每条判据来自哪里** (档; 推导在 [TL2Ord](TL2Ord.lagda.md), [TL2Raise](TL2Raise.lagda.md)):
>
> | 判据 | 出处 | 类 |
> |---|---|---|
> | (i) `OrdCrit` | `HtTowerTy.step` 的新种类: `Pr⁺ (inj₂ _) w a a′ = a ⊲[ proj₁ w ] a′`; `sup` 取分量 | **读自 `step`** (树侧现有形状, 不是记号). 作为要求是选择; 不要它时 `Fl` 合法 (`NegTreeLangFlat`, 定理) |
> | (i) `prj` | 同上: `step` 的世界第一分量, `sup` 的世界逐分量 | 读自 `step`/`sup`; 写 `ord→` 必须给一个世界, 所以是 (i) 的形式要求 (判断) |
> | (ii) `Cross` | `StallDxBdec.bdec` (共界的两个高度相等可判定); `TreeLangRaise.Pos` | 树逼出的部分: 共界的对在定义域里不会推出分离子 (`bdec`, 定理); "必须含" 是选择 |
> | (iii) `Grow`, `RaiseUp` | `RsOwnIf.RsK.rs≤` (种类结构上升界的条件形增长律); `HtTowerTy.Step._≤⁺_` | 读自 `RsK` (树侧接口); 选择 |
> | (iv) `DRaise` 的截面 | `ColimARaise.raiseA′` 的族增量 (判为相等时取族在该处的值, 不搬运) | 读自树侧已有的出路; 选择. 读数**类型**随成员变是 C6 的跨级族逼出的 (`raise-adj`, 定理) |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TL2If where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (LH)
open import OCF.Align.TreeLangIf
```

## §1 (i) 顺序一致: 第一位置就是坐标高度的 `⊲`

`toH R c κ e`: 级为 $y$ 的种类 $\kappa$ 的坐标, 沿 `coord` 读成候选自己的第 $y$ 层的高度. `OrdCrit R`: 第 $c$ 层的世界投影到第 $y$ 层的世界 (`prj`), 种类 $\kappa$ 的第一位置与投影世界里的 `⊲` 互推. 底种类 (坐标 $B$) 不受约束: $B$ 是参数, 没有高度的序.

```agda
cdEq : ∀ {S : KS} {B : Set} (R : LvRule S B) c κ {y} → lv R c κ ≡ inj₂ y → E (L R c) κ ≡ HB (L R y)
cdEq {B = B} R c κ e = trans (coord R c κ) (cong (Cdᴿ B (L R)) e)

toH : ∀ {S : KS} {B : Set} (R : LvRule S B) c κ {y} → lv R c κ ≡ inj₂ y → E (L R c) κ → HB (L R y)
toH R c κ e = subst (λ X → X) (cdEq R c κ e)

record OrdCrit {S : KS} {B : Set} (R : LvRule S B) : Set where
  field
    prj  : ∀ c κ {y} → lv R c κ ≡ inj₂ y → Wd (L R c) → Wd (L R y)
    ord→ : ∀ c κ {y} (e : lv R c κ ≡ inj₂ y) {w a a′} →
           Pr (L R c) κ w a a′ → toH R c κ e a ⊲[ prj c κ e w ] toH R c κ e a′
    ord← : ∀ c κ {y} (e : lv R c κ ≡ inj₂ y) {w a a′} →
           toH R c κ e a ⊲[ prj c κ e w ] toH R c κ e a′ → Pr (L R c) κ w a a′
open OrdCrit public
```

**层号 `LH`.** 每个种类都有级 (没有底), 所以不必带 `e`.

```agda
toHL : ∀ (R : LvRuleL) x κ → E (Lᴸ R x) κ → HB (Lᴸ R (lvᴸ R x κ))
toHL R x κ = subst (λ X → X) (coordᴸ R x κ)

record OrdCritL (R : LvRuleL) : Set where
  field
    prjᴸ  : ∀ x κ → Wd (Lᴸ R x) → Wd (Lᴸ R (lvᴸ R x κ))
    ordᴸ→ : ∀ x κ {w a a′} → Pr (Lᴸ R x) κ w a a′ → toHL R x κ a ⊲[ prjᴸ x κ w ] toHL R x κ a′
    ordᴸ← : ∀ x κ {w a a′} → toHL R x κ a ⊲[ prjᴸ x κ w ] toHL R x κ a′ → Pr (Lᴸ R x) κ w a a′
open OrdCritL public
```

## §2 (ii) 异键对: 共界的成员对必须在定义域里

`HKey Kt`: 键读成某个种类结构 `Sk` 上的高度 (单射). `CrossOn`: 一切世界里, 键是同一合法高度 `Lb` 在同一合法世界 $\omega$ 里的字面第一位置的两个成员, 在定义域里. 这是向上封闭的要求 (定义域越大越难满足), 与 `TreeLangIf` 的律 (定义域越小越容易满足) 方向相反.

```agda
record HKey (Kt : Set) : Set₁ where
  field
    Sk     : KS
    hk     : Kt → HB Sk
    hk-inj : ∀ {k k′} → hk k ≡ hk k′ → k ≡ k′
open HKey public

CrossOn : ∀ {Wt Jt Kt : Set} → HKey Kt → (Jt → Kt) → (Wt → Jt → Jt → Set) → Set
CrossOn {Wt} {Jt} H ky ev =
  ∀ (w : Wt) {ω : Wd (Sk H)} {Lb : HB (Sk H)} → LgW (Sk H) ω → LgB Lb →
  ∀ (j j′ : Jt) → hk H (ky j) ⊲[ ω ] Lb → hk H (ky j′) ⊲[ ω ] Lb → ev w j j′

Cross : (F : RaiseFrame) → HKey (Key F) → Set
Cross F H = CrossOn H (key F) (Ev F)
```

## §3 (iii) 升界保序

`OrdFrame F`: 世界的序 `_≤W_`, 成员 $j$ 在世界 $w$ 里的读数序 `≤R w j` (读数是高度时, 序要一个世界), 读数随世界单调 (`obs-mono`). `Above O w j v`: $v$ 在一切带证据的同键成员的读数之上. `Grow`: 新值 `Above` 时世界变大 (条件形, 与 `RsK.rs≤` 同形). `RaiseUp`: 升界只对 `Above` 的值给出, 且总是变大.

```agda
record OrdFrame (F : RaiseFrame) : Set₁ where
  field
    _≤W_     : W F → W F → Set
    ≤R       : W F → J F → V F → V F → Set
    obs-mono : ∀ j {w w′} → w ≤W w′ → ≤R w′ j (obs F j w) (obs F j w′)
open OrdFrame public

Above : ∀ {F : RaiseFrame} → OrdFrame F → W F → J F → V F → Set
Above {F} O w j v = ∀ j′ → Ev F w j j′ → key F j′ ≡ key F j → ≤R O w j′ (obs F j′ w) v

Grow : ∀ {F : RaiseFrame} → OrdFrame F → Raise F → Set
Grow {F} O R = ∀ {w j} v → Above O w j v → _≤W_ O w (rs R w j v)

record RaiseUp (F : RaiseFrame) (O : OrdFrame F) : Set where
  field
    rsU   : (w : W F) (j : J F) (v : V F) → Above O w j v → W F
    setU  : ∀ {w j j′ v} (a : Above O w j v) → Ev F w j j′ → key F j′ ≡ key F j → obs F j′ (rsU w j v a) ≡ v
    keepU : ∀ {w j j′ v} (a : Above O w j v) → Ev F w j j′ → ¬ (key F j′ ≡ key F j) → obs F j′ (rsU w j v a) ≡ obs F j′ w
    growU : ∀ {w j v} (a : Above O w j v) → _≤W_ O w (rsU w j v a)
open RaiseUp public
```

## §4 (iv) 读数类型随成员变

`DFrame`: 与 `RaiseFrame` 相同, 只是读数类型 `Vᴰ j` 随成员变. `DRaise`: 升界的值是**成员上的截面** `vs : (j : Jᴰ) → Vᴰ j`; 同键的成员 $j'$ 读到 `vs j′` (它自己的值), 所以律里不出现沿键的相等证明的搬运. `constD`: 读数类型不随成员变的特例. (iii), (ii) 在这一框架上的版本: `DOrd`, `DAbove`, `DGrow`, `DCross`.

```agda
record DFrame : Set₁ where
  field
    Wᴰ   : Set
    Jᴰ   : Set
    Keyᴰ : Set
    keyᴰ : Jᴰ → Keyᴰ
    Vᴰ   : Jᴰ → Set
    obsᴰ : (j : Jᴰ) → Wᴰ → Vᴰ j
    Evᴰ  : Wᴰ → Jᴰ → Jᴰ → Set
open DFrame public

record DRaise (F : DFrame) : Set where
  field
    rsᴰ   : Wᴰ F → Jᴰ F → ((j : Jᴰ F) → Vᴰ F j) → Wᴰ F
    setᴰ  : ∀ {w j j′} vs → Evᴰ F w j j′ → keyᴰ F j′ ≡ keyᴰ F j → obsᴰ F j′ (rsᴰ w j vs) ≡ vs j′
    keepᴰ : ∀ {w j j′} vs → Evᴰ F w j j′ → ¬ (keyᴰ F j′ ≡ keyᴰ F j) → obsᴰ F j′ (rsᴰ w j vs) ≡ obsᴰ F j′ w
open DRaise public

constD : RaiseFrame → DFrame
constD F = record
  { Wᴰ = W F ; Jᴰ = J F ; Keyᴰ = Key F ; keyᴰ = key F ; Vᴰ = λ _ → V F ; obsᴰ = obs F ; Evᴰ = Ev F }

record DOrd (F : DFrame) : Set₁ where
  field
    _≤Wᴰ_     : Wᴰ F → Wᴰ F → Set
    ≤Rᴰ       : Wᴰ F → (j : Jᴰ F) → Vᴰ F j → Vᴰ F j → Set
    obs-monoᴰ : ∀ j {w w′} → w ≤Wᴰ w′ → ≤Rᴰ w′ j (obsᴰ F j w) (obsᴰ F j w′)
open DOrd public

DAbove : ∀ {F : DFrame} → DOrd F → Wᴰ F → Jᴰ F → ((j : Jᴰ F) → Vᴰ F j) → Set
DAbove {F} O w j vs = ∀ j′ → Evᴰ F w j j′ → keyᴰ F j′ ≡ keyᴰ F j → ≤Rᴰ O w j′ (obsᴰ F j′ w) (vs j′)

DGrow : ∀ {F : DFrame} → DOrd F → DRaise F → Set
DGrow {F} O R = ∀ {w j} vs → DAbove O w j vs → _≤Wᴰ_ O w (rsᴰ R w j vs)

DCross : (F : DFrame) → HKey (Keyᴰ F) → Set
DCross F H = CrossOn H (keyᴰ F) (Evᴰ F)
```
