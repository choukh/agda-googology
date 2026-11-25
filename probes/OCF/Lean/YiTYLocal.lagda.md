# 两条指定链的第 2 项义务
不读记号；编译定理：首步与实际孩子折叠的第 2 项接线；第 2 项值界仍未填。
逐项归纳允许错位；ChainAdvance、CumAdvance 只声明待填类型，不当作居民。
来源：YiTZLocal、YiTQChain；feed 的路径逐字保留，不与 out 作定义相等认定。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTYLocal where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTQChain as Q

-- perf: C-9/S-1，孩子折叠在变量 d 上出生并封装。
opaque
  unfolding T.Source.feed T.Source.g
  source-fold : B.Tr B.zero → B.Tr B.zero
  source-fold d = proj₁ (TB.ψ (T.source-child d) (proj₂ (P.Ok-tw 1) d)
    (MT.rbᶻ (T.source-child d)) (F.B₀ (T.source-child d)) B.zero
    (P.self P.∙ proj₂ (proj₁ (P.Ok-tw 1)) d) (O.Ωt B.zero)
    (proj₁ (O.Ωt (T.source-child d))))
  source-feed : (d : B.Tr B.zero) → T.Source.feed d ≡ source-fold d
  source-feed d = refl

module At (o : P.Ok T.neck) where
  module A = T.At o
  module C = Q.At o
  opaque
    unfolding A.Target.feed A.Target.g
    target-fold : B.Tr B.zero → B.Tr B.zero
    target-fold d = proj₁ (TB.ψ (T.child d) (proj₂ o d)
      (MT.rbᶻ (T.child d)) (F.B₀ (T.child d)) B.zero
      (P.self P.∙ proj₂ (proj₁ o) d) (O.Ωt B.zero)
      (proj₁ (O.Ωt (T.child d))))
    target-feed : (d : B.Tr B.zero) → A.Target.feed d ≡ target-fold d
    target-feed d = refl
  ChainAt : ℕ → ℕ → Set
  ChainAt n m = V.val B.zero (T.Source.chain n) V.≼ V.val B.zero (A.Target.chain m)
  ChainItem : ℕ → Set
  ChainItem n = Σ ℕ (ChainAt n)
  ChainAdvance : ℕ → Set
  ChainAdvance n = ChainItem n → ChainItem (suc n)
  chain-zero : ChainItem 0
  chain-zero = 0 , V.z≼
  chain-one : ChainItem 1
  chain-one = 1 , C.chain-one
  chain-advance-zero : ChainAdvance 0
  chain-advance-zero _ = chain-one
  CumItem : ℕ → Set
  CumItem n = Σ ℕ λ m → V.val B.zero (T.source-cum n) V.≼ V.val B.zero (A.target-cum m)
  CumAdvance : ℕ → Set
  CumAdvance n = CumItem n → CumItem (suc n)
  cum-zero : CumItem 0
  cum-zero = A.first-cover
  LocalSecond : Set
  LocalSecond = V.val B.zero (source-fold (T.Source.chain 1))
    V.≼ V.val B.zero (target-fold (A.Target.chain 1))
  second-from-local : LocalSecond → ChainAt 2 2
  second-from-local p = subst
    (λ y → V.val B.zero (T.Source.chain 2) V.≼ V.val B.zero y)
    (sym (target-feed (A.Target.chain 1)))
    (subst (λ x → V.val B.zero x V.≼ V.val B.zero (target-fold (A.Target.chain 1)))
      (sym (source-feed (T.Source.chain 1))) p)
module Canonical = At T.o-neck
```
