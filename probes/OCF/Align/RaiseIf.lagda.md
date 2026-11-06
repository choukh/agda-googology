# RaiseIf: "一起升" 的升界算子 (接口)

> **接口定稿 2026-11-05 (主审写, 首次编译通过后定稿).** 定稿之后只增不改; 若必须改, 在这里写变更记录.

> **对纲领与目标.** 这是构造一路 (`RaiseC*`) 与否定一路 (`NegRaise*`) 共用的接口. 问题来自 [NewTwr](NewTwr.lagda.md) 第一个障碍 3 (ii): 世界是逐分量的积, 分量的下标是坐标 (`A`, `HB _`), 判定不了 "是不是这个分量", 所以 "升一份留别份" 推出分离子 (`NegGenFoldUpd.upd₁-sep`, `NegNewTwrFeed.updΛ⁺-sep`). 剩下的是 "一起升": 对每个分量的界 $a$ 统一用同一个算子换成 $R\,a\,v$. 要它 (i) 不降低任何分量 ($a \lhd R\,a\,v$); (ii) 对真正要升的那个分量 (其界 $a$ 已满足 `FBA.rs≤` 的前提 $a\lhd v$) 给出 $v \lhd R\,a\,v$; (iii) 保合法. `A` 与 `HB S` 的第一位置都是自反的 (`self`, `hself`).

**律的定义域 (手册 §3.1).** `R-lo`: 一对 $(a, R\,a\,v)$, 公共上界 $R\,a\,v$ 本身. `R-hi`: 前提 $a\lhd v$ 给出 $(a,v)$ 的字面公共上界 $v$, 结论的一对 $(v, R\,a\,v)$ 的公共上界是 $R\,a\,v$ 本身. `R-lg`: 一个值. 没有裸下标上的比较律. 注意: 对互不可比的 $a, v$ (如 `HtTowerNeg.no-joinA` 的 `alim evA`, `alim odA`), 接口**不**要求 $v\lhd R\,a\,v$; 若要求, 就直接撞 `no-joinA`.

**接口不管什么 (盲).** 不说 $R\,a\,v$ 的大小 (只给两个下界), 不说 $R$ 对 $v$ 单调; $R\,a\,v = a$ 满足 `R-lo`, `R-lg`, 不满足 `R-hi`; $R\,a\,v = v$ 满足 `R-hi`, `R-lg`, 不满足 `R-lo`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RaiseIf where

open import Data.Product using (Σ; _,_; _×_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy
```

## §1 `A` 上的升界算子

```agda
record RaiseA : Set where
  field
    R    : A → A → A
    R-lo : ∀ {a v} → Lg a → Lg v → a ⊲ R a v
    R-hi : ∀ {a v} → Lg a → Lg v → a ⊲ v → v ⊲ R a v
    R-lg : ∀ {a v} → Lg a → Lg v → Lg (R a v)
open RaiseA public
```

## §2 高度 `HB S` 上的升界算子 (第一位置相对于一个合法世界)

```agda
record RaiseB (S : KS) : Set where
  field
    Rᴮ    : HB S → HB S → HB S
    Rᴮ-lo : ∀ {a v w} → LgW S w → LgB a → LgB v → a ⊲[ w ] Rᴮ a v
    Rᴮ-hi : ∀ {a v w} → LgW S w → LgB a → LgB v → a ⊲[ w ] v → v ⊲[ w ] Rᴮ a v
    Rᴮ-lg : ∀ {a v} → LgB a → LgB v → LgB (Rᴮ a v)
open RaiseB public
```

## §3 逐分量的积世界上 "一起升" 的形状 (只是定义, 给两路共用)

一族分量 $W : I \to A$, 一起升成 $i \mapsto R\,(W\,i)\,v$. 逐分量的序与合法:

```agda
module ProdA (I : Set) where
  _≤ᴾ_ : (I → A) → (I → A) → Set
  W ≤ᴾ W′ = ∀ i → W i ⊲ W′ i

  LgP : (I → A) → Set
  LgP W = ∀ i → Lg (W i)

  upAll : RaiseA → (I → A) → A → (I → A)
  upAll ρ W v i = R ρ (W i) v
```
