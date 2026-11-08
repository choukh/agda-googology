# 三步延迟的阶段无关接口

本接口只要求树关系保持加法、前后追加及实际两个动作。不要求关系对
全部raw树自反，不提供下标三歧或判等；所有比较都消费已有关系证据。
old与padded是调用者的实际数组，方程防止把它们换成未连接的模型。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedStrideIf where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)

record StrideLaws (S : KS) (R : HB S → HB S → Set)
  (F H : HB S → HB S) (old padded : ℕ → HB S) : Set where
  field
    old-step : ∀ n → old (suc n) ≡ old n ⊞ F (old n)
    pad-zero : padded zero ≡ old zero
    pad-step : ∀ n → padded (suc n) ≡ padded n ⊞ hs (old (suc n))
    append : ∀ {a b} → R a b → ∀ c → R a (b ⊞ c)
    prepend : ∀ c {a b} → R a b → R a (c ⊞ b)
    add : ∀ {a b c d} → R a b → R c d → R (a ⊞ c) (b ⊞ d)
    inflate : ∀ {a b} → R a b → R a (H b)
    action : ∀ {a b} → R a b → R (F a) (H b)
    positive : ∀ b → R (hs hz) (H b)
    initial : R (old zero) (chain H 1)
```

这里未假定任意回调保持裸值序或折叠保持R。运行证明给出old/pad的
全轨道关系；若要序数值结论，还须实例化R并接真实求值定理。
