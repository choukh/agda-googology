# 单向宽位置不提供宽界三分

两个已知合法零层分支都进入同一个 Ω；它们的有限列极限 a、b 却互不为宽位置。
所以不能把两份 Below(_,Ω) 当作 CP 的共同界参数交给 compare。
这检查的是当前原树路径关系，不是给所有位置规定一个全序。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiDispWideAudit where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (CP; CP-tr)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxFork as W
import OCF.Align.YiRTransport as R
open import OCF.Align.YiRCountable using (Small; raw0-small)
open import OCF.Align.YiDispBase
open import OCF.Align.YiDispCountable using (edge-small)

edge-cp-small : ∀ {a b} → Edge a b → Small b → CP a b
edge-cp-small e-suc s = V.suc V.self
edge-cp-small (e-lim n) s = V.lim n V.self
edge-cp-small e-first ()
edge-cp-small (e-branch η e) ()

below-cp-small : ∀ {a b} → Below a b → Small b → CP a b
below-cp-small (one e) s = edge-cp-small e s
below-cp-small (more p e) s = CP-tr (below-cp-small p (edge-small e s)) (edge-cp-small e s)

a-small : Small W.a
a-small = raw0-small (G.lim (λ n → G.suc (W.raw-nat n)))

a-position : Below W.a (Y.tree R.ν)
a-position = cp-edge (V.suc V.self) (e-branch W.ηa W.guard-a)

b-position : Below W.b (Y.tree R.ν)
b-position = cp-edge (V.suc V.self) (e-branch W.ηb W.guard-b)

a-not-b : Below W.a W.b → ⊥
a-not-b p = W.a-not-b (below-cp-small p R.b-small)

b-not-a : Below W.b W.a → ⊥
b-not-a p = W.b-not-a (below-cp-small p a-small)

a-not-equal-b : W.a ≡ W.b → ⊥
a-not-equal-b e = W.a-not-b (subst (CP W.a) e V.self)

ΩWideCompare : Set
ΩWideCompare = ∀ {a b} → Below a (Y.tree R.ν) → Below b (Y.tree R.ν) →
  Below a b ⊎ (a ≡ b ⊎ Below b a)

no-wide-compare : ΩWideCompare → ⊥
no-wide-compare cmp with cmp a-position b-position
... | inj₁ p = a-not-b p
... | inj₂ (inj₁ e) = a-not-equal-b e
... | inj₂ (inj₂ p) = b-not-a p
```

这里只能对给出的单向路径使用 structural。宽位置没有新的判定器，
原 CP 比较的输入仍限于共同合法 CP 界；也未构造 Barrier 要的精确 Ordᴰ 初始段。
没有把本篇不能三分的原树关系与序数值序混同。
