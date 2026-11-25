# 有限孩子处的树基本列展开

不读记号；有限测试：`FinSeq 0`、`FinSeq 1` 各前三项（`fs₀`、`fs₁`、`fs₂`）；等式同时对任意 n 编译。
树的第一项恒为 `next⁺ (Ωt zero)`，后两项保留底层自身折叠与朝第 0 层的折叠，且取部分和。
记号侧的相应前三项在验收文件 `YiTSNote`；这里不把语法展开说成序数值比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTSSeq where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow
open import OCF.Lean.YiTSStep using (module Step)

module FinSeq (n : ℕ) where
  o : Ok (fn (suc n))
  o = proj₂ (Ok-tw 1) (nat (suc n))
  r : Rb (fn (suc n))
  r = rb-no (fn (suc n))
  module F = Step (nat n) o r (B₀ (fn (suc n))) (z≤ (fn n)) (Ωt zero)

  z₁ : Tr (fn n)
  z₁ = proj₁ (next⁺ (Ωt (fn n)))

  z₂ : Tr (fn n)
  z₂ = proj₁ (next⁺ (ψ (fn n) (proj₂ o tt) (proj₂ r tt) (B₀ (fn n)) (fn n) self (Ωt (fn n)) z₁))

  piece₀ : Tr zero
  piece₀ = proj₁ (next⁺ (Ωt zero))

  piece₁ : Tr zero
  piece₁ = proj₁ (next⁺ (ψ (fn n) (proj₂ o tt) (proj₂ r tt) (B₀ (fn n)) zero (z≤ (fn n)) (Ωt zero) z₁))

  piece₂ : Tr zero
  piece₂ = proj₁ (next⁺ (ψ (fn n) (proj₂ o tt) (proj₂ r tt) (B₀ (fn n)) zero (z≤ (fn n)) (Ωt zero) z₂))

  fs₀ : cum (λ k → proj₁ (F.parts k)) 0 ≡ piece₀
  fs₀ = refl

  fs₁ : cum (λ k → proj₁ (F.parts k)) 1 ≡ piece₀ + piece₁
  fs₁ = refl

  fs₂ : cum (λ k → proj₁ (F.parts k)) 2 ≡ (piece₀ + piece₁) + piece₂
  fs₂ = refl
```
