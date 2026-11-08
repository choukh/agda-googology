# 读回层 1+x 不能单独给出全闭包解释

有限级与已有 ω 包的读回层是 1+x，极限处沿分支延续。这个形状
不能不加条件地推广成对任意合法 x 的旧 NdI：合法性允许常零极限，
原数据的 NZ₁ 却在任何极限层都允许 nμ。此时目标 Lev x 只有底种类
的拷贝，装不下 NdI 要求的完整高种类坐标收缩。

以下只否定这个具体接口推广，不否定读回、实际生成域或折叠额外
闭包的算法。常零极限不是严格值递增的列；本仓库不要求后一条件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ReadLayerBoundary where

open import Data.Nat using (ℕ; zero)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (azero)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (D; NZ₁; nμ)
open import OCF.Align.HtTowerNeg using (no-retract)
open import OCF.Align.LvRdEmb using (Emb; lk; cv; vc; cv-vc; ιE)
open import OCF.Align.LvRdPkg using (NdI)

flat : HB S₀
flat = hl (λ _ → hz)

flat-legal : LgB flat
flat-legal = (λ _ → hself) , (λ _ → tt)

layer : HB (step S₀)
layer = hs hz ⊞ up flat

layer-shape : layer ≡ hl (λ _ → hs hz)
layer-shape = refl

layer-legal : LgB layer
layer-legal = (λ _ → hself) , (λ _ → tt)

allowed : NZ₁ layer
allowed = tt

-- 是原数据允许的实际闭项，不把接口前提藏成空类型。
extra : D layer (azero , hz)
extra = nμ allowed (λ _ _ → OCF.Align.HtTowerFTree.n0)

Sparse : KS
Sparse = Lev flat

bottom-copy : Emb S₀ Sparse
bottom-copy = ιE zero

-- 对任意拷贝下标集，底坐标 A 的并装不下完整的 H₀ 坐标收缩。
no-high-copy : ∀ {I : Set} → Emb (step S₀) (sup I (λ _ → S₀)) → ⊥
no-high-copy e with lk e (inj₂ tt) | cv e {inj₂ tt} | vc e {inj₂ tt} | cv-vc e {inj₂ tt}
... | i , tt | back | forth | inverse = no-retract {S₀} tt forth back inverse

no-flat-interpreter : NdI Sparse layer → ⊥
no-flat-interpreter n = no-high-copy (NdI.eM n)

no-all-interpreters :
  (∀ x → LgB {S₀} x → NdI (Lev x) (hs hz ⊞ up x)) → ⊥
no-all-interpreters all = no-flat-interpreter (all flat flat-legal)
```

结论的原因是旧 NdI.eM 的 cv-vc 字段要求高坐标类型成为底坐标
类型的收缩，由已有 no-retract 否定。没有以值估计关闭路线，没有
禁止仅针对可用闭包解释、改变额外闭包读法，或使用实际生成域证书。
这个反例也不反对已有有限级、ω、ω+1 读回包；其精确实例仍保留。
