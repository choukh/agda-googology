# 指定两条内链的首步与读回路径
不读记号；编译定理：源链点 1 经第一位置到目标链点 1，适用于指定颈结点的任意 Ok 证书。
带固定底偏移的源读回层沿字面路径进入目标孩子层；不提供 Next、Cover 或 Bound 的居民。
来源：复用 YiTZLocal 的链点等式与 YiRWPath.◃→⊑；有限三层折叠取第 0 支。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTQChain where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTZLocal as T

omega : B.Tr B.zero
omega = proj₁ (O.next⁺ (O.Ωt B.zero))
low-three-step : (o : P.Ok (T.child B.zero)) (w : P._≤_ B.zero (T.child B.zero)) →
  B._⊢_◃_ B.zero omega (proj₁
    (TB.ψ (T.child B.zero) o (MT.rbᶻ (T.child B.zero))
      (F.B₀ (T.child B.zero)) B.zero w (O.Ωt B.zero) (proj₁ (O.Ωt (T.child B.zero)))))
low-three-step o (P.inc tt w) = B.◃l 0
low-three-step o (P.inu ws) = B.◃l 0

shifted-source : B.L
shifted-source = T.two B.⊕ (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero (T.Source.chain 1)))

o-shifted : P.Ok shifted-source
o-shifted = P.Ok⊕ T.two (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero (T.Source.chain 1))) T.o-two
  (P.OkO⊕ T.two B.zero (B.zero B.⊕ B.↑ B.zero (T.Source.chain 1)) tt
    (P.OkO⊕ T.two B.zero (B.↑ B.zero (T.Source.chain 1)) tt
      (P.OkO↑ T.two B.zero tt (P.z≤ T.two) (T.Source.chain 1))))

module At (o : P.Ok T.neck) where
  module A = T.At o
  chain-one-step : B._⊢_◃_ B.zero (T.Source.chain 1) (A.Target.chain 1)
  chain-one-step = subst (λ t → B._⊢_◃_ B.zero t (A.Target.chain 1))
    (sym T.source-chain-one)
    (subst (λ t → B._⊢_◃_ B.zero omega t) (sym A.target-chain-one)
      (low-three-step (proj₂ o B.zero) (P.self P.∙ proj₂ (proj₁ o) B.zero)))
  chain-one : V.val B.zero (T.Source.chain 1) V.≼ V.val B.zero (A.Target.chain 1)
  chain-one = V.◁→≼ (V.val-mono B.zero chain-one-step)
  shifted-path : P._⊑_ shifted-source (T.child (A.Target.chain 1))
  shifted-path = P.inc tt (P.⊕⊑ T.two
    (P.⊕⊑ B.zero (P.⊕⊑ B.zero (P.◃→⊑ B.zero chain-one-step))))
module Canonical = At T.o-neck
```
