# 全原LH地板种子的实际实例

两条轨道都从原flL j开始，Typed保留旧Ω。每一对前后坐标在同一
显式合法世界与较后合法树下比较；本篇没有采样访问或run单调结论。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaSeededActual where
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤⇒≤′)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecFl using (flL; Lg-flL)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.GeneralOmegaSeededIf
import OCF.Lean.GeneralOmegaSeededRun as Proof
open import OCF.Lean.GeneralOmegaSampleWorld using (World; legal)

module At (j : LH) where
  open Prototype (Lv j) (flL j) public
  module P = Proof.Run (Lv j) (flL j)
  instance-laws : Laws
  instance-laws = P.laws
  noSum-legal : LgB whole
  noSum-legal = Laws.noSum-legal instance-laws (Lg-flL j)
  sum-legal : LgB accumulated
  sum-legal = Laws.sum-legal instance-laws (Lg-flL j)
  whole-value : whole ≤ᵛ accumulated
  whole-value = P.whole-cover
  coordinates : ∀ n → NoSum n ≤ᵛ Sum n
  coordinates = P.coordinates

  steps : ∀ {n m W} → n ≤′ m → NoSum n ⊲[ W ] NoSum m
  steps ≤′-refl = hself
  steps (≤′-step {n = m} p) = ⊲ᴮ-tr (steps p) (P.noSum-step m)
  common-bound : ∀ (d : Cd) {n m} → n ≤ m →
    LgW (Lv j) (World j d) × LgB (NoSum m) ×
    NoSum n ⊲[ World j d ] NoSum m × NoSum m ⊲[ World j d ] NoSum m
  common-bound d {n} {m} p = legal j d , P.noSum-legal (Lg-flL j) m , steps (≤⇒≤′ p) , hself
```

At的实例包括j=ls lz，此时初始坐标就是原新Ω地板，既非1，也非纯
可数树。whole-value覆盖完整无累加轨道，但目标仍在同一个高层；
真实更高源运行的Visit覆盖须另证，不能由此高层值关系自动推出。
