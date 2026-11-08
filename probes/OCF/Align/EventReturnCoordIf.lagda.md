# 迁回的低坐标关系：允许单边世界包装

原 Plain 只允许两侧一起出现 nw，不能用于一侧已经 drp 的实际调用。
本接口比较原 D₀ 数据的全部基本列，同时允许任一侧多一个 nw。
它不比较两个裸下标，也不把不同树的序数值相同当成输入可替换。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventReturnCoordIf where

open import Data.Nat using (ℕ)
open import OCF.Align.EvFoldTree

data E₀ : ∀ {W W′} → D₀ W → D₀ W′ → Set where
  ez : ∀ {W W′} → E₀ (n0 {W = W}) (n0 {W = W′})
  eo : ∀ {W W′} → E₀ (n1 {W = W}) (n1 {W = W′})
  ea : ∀ {W W′} {a b : D₀ W} {a′ b′ : D₀ W′} →
       E₀ a a′ → E₀ b b′ → E₀ (a ⨾ b) (a′ ⨾ b′)
  el : ∀ {W W′} {f : ℕ → D₀ W} {g : ℕ → D₀ W′} →
       (∀ n → E₀ (f n) (g n)) → E₀ (nl f) (nl g)
  ewL : ∀ {U W V} {x : D₀ U} {y : D₀ V} →
        (p : U ≤ W) → E₀ x y → E₀ (nw p x) y
  ewR : ∀ {U W V} {x : D₀ V} {y : D₀ U} →
        (p : U ≤ W) → E₀ x y → E₀ x (nw p y)
```
