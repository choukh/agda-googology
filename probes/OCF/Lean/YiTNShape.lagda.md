# 目标第 1 链点的极限形状
不读记号；编译定理：实际目标第 1 链点是 ℕ 极限，首项为源第 1 链点。
不提供第 2 链点间的值界。
来源：YiTNRow 出口展开、YiTYLocal.target-feed；重构在出生处封装。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTNShape where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTYLocal as Y
import OCF.Lean.YiTQChain as Q
import OCF.Lean.YiTNRow as R
module A = R.Actual B.zero
module Z = A.A
opaque
  tick : B.Tr Z.a → B.Tr Z.a
  tick c = proj₁ (TB.ψ Z.a Z.oa Z.ra Z.bs Z.a P.self (O.Ωt Z.a) (B.suc c))
  line : ℕ → O.Tr⁺ B.zero
  line n = Z.fold (B.suc (O.iter tick B.zero n))
  curve : ℕ → B.Tr B.zero
  curve = O.cum (λ n → proj₁ (line n))
  adj : (n : ℕ) → B._⊢_◃_ B.zero (curve n) (curve (Data.Nat.suc n))
  adj n = O.+-mono _ (proj₂ (line (Data.Nat.suc n)))
  high-row : proj₁ Z.high ≡ B.lim curve adj
  high-row = refl
  first : curve 0 ≡ Q.omega
  first = refl
  chain-shape : T.Canonical.Target.chain 1 ≡ B.lim curve adj
  chain-shape = trans (Y.Canonical.target-feed B.zero)
    (trans (sym A.target-eq) high-row)
```
