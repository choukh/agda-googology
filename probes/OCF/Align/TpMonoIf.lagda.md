# `T⁺` 对输入单调: 接口

> 接口定稿 2026-11-05 12:11. 此后只增不改. 变更记录: 12:23 增 §5 (一步律归结的三个类型, 只增).
>
> 不含记号. 作者选定原话: "A2: T⁺ 对输入单调". 构造一路前缀 `TpMono`, 否定一路前缀 `NegTpMono`, 共用本文件. 只有类型 (记录, 关系与命题), 没有证明.
>
> 对象是两种种类的折叠 `HtTowerFClosed.T⁺ : (h : Ht) → LgB h → A`. 律对任意 `F : Fn` 写 (`Fn = (h : Ht) → LgB h → A`), `T⁺` 是其中一个 `F`; 这样同一组律可以先在别的 `F` 上检查可满足性, 再问 `T⁺` 是否满足.
>
> **律的定义域** (按 `AGENTS.md` "律带公共上界", 手册 §3.1). 律里每一对输入都带下面三种证据之一, 不出现裸的两个输入:
>
> 1. **(a) 互模拟** `a ≈ b` (`DiagK3Zero._≈_`: 同形, 极限处逐点). 两个输入字面同形, 证据本身就是逐点的对应, 律不要求判定它们相等或比较它们. 这里没有公共上界; 互模拟证据比公共上界强 (同形), 所以不重证 "判等" (判断).
> 2. **(b) 一切世界里的字面第一位置** `a ⊑ b = ∀ {w} → a ⊲[ w ] b`, 严格版 `a ⊏ b = ∀ {w} → a ⊲⁺[ w ] b`. 公共上界就是 $b$ 自己, 证据是对一切世界的路径. 量化一切世界是有意的: 路径过 $\Omega$-分支时坐标要在一切世界的界之下, 所以只能走最小坐标 (`bot`); 走任意世界里有界的坐标就是 "按值单调" 的一般形式, 碰 `MonoPort9Neg.no-all` 那一类 (手册 §3.1, `no-pointwise`, `HtVal`).
> 3. **(c) 左加平移** $b \mapsto a\boxplus b$ (`HtTowerTy._⊞_`). 证据是字面的构造 ($a\boxplus b$ 对 $b$ 逐构造子), 不是值的比较.
>
> 不在定义域里的: 两个输入只在值上可比 (没有上面三种证据), 一个世界里有界的任意坐标, 对一切可数高度的无条件陈述.
>
> `Steps`: (b) 的一步形式 (合法性无关, 后继, ℕ-极限的第 $n$ 项, $\Omega$-极限的最小坐标), 每一步都是严格的. 构造一路证明 `Steps F` 推出 (b) 的两条 (`TpMonoStep`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TpMonoIf where

open import Data.Nat using (ℕ)
open import Data.Product using (proj₂)
open import OCF.Align.CumReadCF using (A; asuc)
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (S₁; Ht; Wd₂)
open import OCF.Align.HtTowerFClosed using (T⁺) public
open import OCF.Align.DiagK3Zero using (_≈_) public
```

## §1 输入上的关系

```agda
-- 以合法高度为输入的闭项族
Fn : Set
Fn = (h : Ht) → LgB h → A

-- (b) 一切世界里的字面第一位置
infix 4 _⊑_ _⊏_
_⊑_ : Ht → Ht → Set
a ⊑ b = ∀ {w : Wd₂} → a ⊲[ w ] b

-- 严格的字面第一位置: 先下降一步, 再是第一位置
data _⊲⁺[_]_ : Ht → Wd₂ → Ht → Set where
  psuc : ∀ {a b w} → a ⊲[ w ] b → a ⊲⁺[ w ] hs b
  plim : ∀ {a f w} n → a ⊲[ w ] f n → a ⊲⁺[ w ] hl f
  pLim : ∀ {a κ g w c} → Bd S₁ κ c w → a ⊲[ w ] g c → a ⊲⁺[ w ] hΩ κ g

_⊏_ : Ht → Ht → Set
a ⊏ b = ∀ {w : Wd₂} → a ⊲⁺[ w ] b
```

## §2 律

```agda
-- 与合法性证明无关 (互相 ≤ 由两个方向各用一次)
LgIrr : Fn → Set
LgIrr F = ∀ a (la la′ : LgB a) → F a la ≤ F a la′

-- (a) 互模拟的输入, 值 ≤ (两个方向各用一次得同值)
SimInv : Fn → Set
SimInv F = ∀ a la b lb → a ≈ b → F a la ≤ F b lb

-- (b) 一切世界里的字面第一位置, 值 ≤
FstMono : Fn → Set
FstMono F = ∀ a la b lb → a ⊑ b → F a la ≤ F b lb

-- (b) 严格版
FstMono< : Fn → Set
FstMono< F = ∀ a la b lb → a ⊏ b → asuc (F a la) ≤ F b lb

-- (c) 左加平移
ShiftMono : Fn → Set
ShiftMono F = ∀ a la b lb → F b lb ≤ F (a ⊞ b) (Lg-⊞ a b la lb)

record Laws (F : Fn) : Set where
  field
    sim   : SimInv F
    fst   : FstMono F
    fst<  : FstMono< F
    shift : ShiftMono F
```

## §3 一步形式

```agda
record Steps (F : Fn) : Set where
  field
    irr  : LgIrr F
    s-hs : ∀ a la → asuc (F a la) ≤ F (hs a) la
    s-hl : ∀ (f : ℕ → Ht) (lf : LgB (hl f)) n → asuc (F (f n) (proj₂ lf n)) ≤ F (hl f) lf
    s-hΩ : ∀ κ (g : E S₁ κ → Ht) (lg : LgB (hΩ κ g)) (lc : LgE S₁ κ (bot S₁ κ)) →
           asuc (F (g (bot S₁ κ)) (proj₂ lg (bot S₁ κ) lc)) ≤ F (hΩ κ g) lg
```

## §4 对 `T⁺` 的实例 (类型)

```agda
Laws⁺ : Set
Laws⁺ = Laws T⁺

Steps⁺ : Set
Steps⁺ = Steps T⁺
```

## §5 一步律的归结 (类型, 12:23 增)

构造一路把 `Steps.s-hs`, `Steps.s-hl` 各归结为关于一次折叠的值不等式 ([TpMonoHs](TpMonoHs.lagda.md), [TpMonoHl](TpMonoHl.lagda.md)); 这里只转出它们的类型, 供否定一路对准. `ChangeHs h lh`: 跨实例 (实例 $1\boxplus h$ 对 $1\boxplus(h+1)$, 同一个世界, 同一次折叠); `MonoStepHs h lh`: 实例 $1\boxplus h$ 之内 (状态、上下文、基变大); `MonoHl f lf n`: 第 $n$ 段 (跨实例与实例之内合一).

```agda
open import OCF.Align.TpMonoHs using (module Hs) public
open import OCF.Align.TpMonoHl using (module Hl) public

ChangeHs : (h : Ht) → LgB h → Set
ChangeHs h lh = Hs.ChangeHs h lh

MonoStepHs : (h : Ht) → LgB h → Set
MonoStepHs h lh = Hs.MonoStepHs h lh

MonoHl : (f : ℕ → Ht) → LgB (hl f) → ℕ → Set
MonoHl f lf n = Hl.N.MonoHl f lf n
```
