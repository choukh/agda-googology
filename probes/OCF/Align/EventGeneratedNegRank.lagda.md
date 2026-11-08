# 低历史相容不能同步最高事件的动态层

这里否定的是额外候选桥 `HistLow → 同 rank/Shape rank`，不是共享
`EventGeneratedIf.Generated`：后者正确地要求指定种类的 `ReplayAt`。
反例使用原合法源 Ω₃ᴱ、合法世界及一个合法的 κ₁ 增量。
末节同时核准原 drp₂ 捕获旧历史的方程；不能把迁回当作在新历史重跑源。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedNegRank where

open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.HtTowerTy
open import OCF.Align.CumReadCF using (Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead
open import OCF.Align.EventReturnCodeIf using (Shape)
open import OCF.Align.EventReturnValueEvent using (HistLow; empty; forget-left)
import OCF.Align.EvFoldClosed as Closed
import OCF.Align.EventGeneratedIf as Shared

g : H₁ → Ht
g = Closed.nbᴱ hz (λ _ h → hs h)

module G = Shared.At κ₁ g

high : Ev
high = ev (hs hz) hself (hs hz) tt

before after : Hist
before = high ∷ []
after = []

source-exact : G.source ≡ Closed.Ω₃ᴱ
source-exact = refl

source-legal : LgB G.source
source-legal = Closed.Lg-Ω₃ᴱ

world-before : LgWε (Closed.one , before)
world-before = tt , tt

world-after : LgWε (Closed.one , after)
world-after = tt , tt

low-related : HistLow before after
low-related = forget-left (hs hz) tt empty

rank-before : G.rank before ≡ hs hz
rank-before = refl

rank-after : G.rank after ≡ hz
rank-after = refl

no-rank-equal : G.rank before ≡ G.rank after → ⊥
no-rank-equal ()

no-rank-shape : Shape (G.rank before) (G.rank after) → ⊥
no-rank-shape ()

no-low-equal : (∀ H J → HistLow H J → G.rank H ≡ G.rank J) → ⊥
no-low-equal f = no-rank-equal (f before after low-related)

no-low-shape : (∀ H J → HistLow H J → Shape (G.rank H) (G.rank J)) → ⊥
no-low-shape f = no-rank-shape (f before after low-related)

left-position : G.rank before ⊲[ Closed.one , before ] G.source
left-position = G.position Closed.one before

right-position : G.rank after ⊲[ Closed.one , after ] G.source
right-position = G.position Closed.one after
```

上面没有裸下标比较：两位置各自在原同一源树中，世界明确不同。
新合同并未声称 HistLow 给 κ₁ 的 ReplayAt，故不是其反例。

## 原迁回保留旧基底的实际方程

`enter` 只是提取一个原 κ₀ 闭包在原读回坐标处的子树；其它根返回零。
方程两端仍用原 drp₂、evx、≤x，不替换原算法。

```agda
enter : ∀ {W} → (lW : LgWε W) → D₂ W → (x : H₀) →
        D₂ (proj₁ W , evx lW x ∷ proj₂ W)
enter lW (nε (_ , hsuc hself) z u) x = u (≤x lW x) (proj₁ lW , tt)
enter lW (nε (_ , hself) () u) x
enter lW n0 x = n0
enter lW n1 x = n0
enter lW (_ ⨾ _) x = n0
enter lW (nl _) x = n0
enter lW (ni _ _) x = n0
enter lW (nκ _ _) x = n0
enter lW (nw _ _) x = n0

captured-base : ∀ {a H J} (la : Lg a)
  (u : ∀ {W} → (a , H) ≤ W → LgWε W → D₂ W) (x : H₀) →
  enter {a , J} (la , tt) (drp₂ (nε κ₀ tt u)) x ≡
  drp₂ (u {a , evx {a , J} (la , tt) x ∷ H}
    (C.self , there (evx {a , J} (la , tt) x) here) (la , tt))
captured-base la u x = refl
```

因此需要异型动态层是某种双运行同步策略的义务，不能由本反例升级为
所有迁回策略的必要条件。这里未否定原 drop、Generated 或完整研究路线。
