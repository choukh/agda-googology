# 相关事件后缀的实际移植

`tp` 保留后缀里的全部事件。这里比较同步的两个后缀：每步事件
种类相同，payload 只要求逐枝 Shape；基底允许 HistLow 忘掉高事件。
同步不等于两事件或两份后缀证明相等，不使用函数外延。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnHistory where

open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.List using (_∷_)
open import OCF.Align.CumReadCF using (Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (tp; tp-suf; evx)
open import OCF.Align.EventReturnCodeIf using (Shape)
open import OCF.Align.EventReturnCodeBuild using (shape-self)
open import OCF.Align.EventReturnValueEvent
open import OCF.Align.EventReturnReplay using (low-replay)

extend : ∀ {H H′ e e′} → EventShape e e′ → HistLow H H′ →
  HistLow (e ∷ H) (e′ ∷ H′)
extend (same-kind _ hself lx ly p) q = forget-left _ lx (forget-right _ ly q)
extend (same-kind _ (hsuc hself) lx ly p) q = low lx ly p q

data Suffix {H H′ : Hist} : ∀ {J J′} → Suf H J → Suf H′ J′ → Set where
  done : Suffix here here
  next : ∀ {J J′ e e′} {p : Suf H J} {q : Suf H′ J′} →
    EventShape e e′ → Suffix p q → Suffix (there e p) (there e′ q)

transplant : ∀ {H H′ J J′ K K′} {p : Suf H J} {q : Suf H′ J′} →
  Suffix p q → HistLow K K′ → HistLow (tp p K) (tp q K′)
transplant done r = r
transplant (next e p) r = extend e (transplant p r)

event-self : ∀ e → EventShape e e
event-self (ev c p x lx) = same-kind c p lx lx (shape-self x)

same-suffix : ∀ {H J} (p : Suf H J) → Suffix p p
same-suffix here = done
same-suffix (there e p) = next (event-self e) (same-suffix p)

-- 原 drp₂ 正是把同一 suffix 接到另一基底。
drop-context : ∀ {H J K K′} (p : Suf H J) → HistLow K K′ →
  HistLow (tp p K) (tp p K′)
drop-context p r = transplant (same-suffix p) r

replay-context : ∀ {H H′ J J′ K K′} {p : Suf H J} {q : Suf H′ J′} →
  Suffix p q → HistLow K K′ →
  Shape (rp (tp p K) hz (hsuc hself)) (rp (tp q K′) hz (hsuc hself))
replay-context s r = low-replay (transplant s r)

observed-suffix : ∀ {a H H′} (la : Lg a) x →
  Suffix {H} {H′} (there (evx {a , H} (la , tt) x) here)
         (there (evx {a , H′} (la , tt) x) here)
observed-suffix la x = next (paired la x) done

-- 任意相关基底：每个原 H₀ 坐标的真实读回事件都可移植。
observed-transplant : ∀ {a H H′ K K′} (la : Lg a) x → HistLow K K′ →
  HistLow (tp (there (evx {a , H} (la , tt) x) here) K)
          (tp (there (evx {a , H′} (la , tt) x) here) K′)
observed-transplant la x r = transplant (observed-suffix la x) r
```

这解决迁回的未来历史对应，不自动解决 CutE/Run 的观察对应：
后者还必须把每个相应前缀处的原回调输出接到同一个数据关系。
特别不能用可删除高事件的 HistLow 代替同步后缀，凭空删去一次回调。
