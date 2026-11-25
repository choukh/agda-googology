# 偏移源折叠进入目标第 2 链点
不读记号；编译定理：Actual.folded 的值不高于实际目标链第 2 点。
其层号等于 YiTQChain.shifted-source；未与未偏移的源第 2 点比较。
来源：YiTNRow、YiTNShape；先取前驱层极限的首支，再取后继层第 1 支。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTNShift where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTYLocal as Y
import OCF.Lean.YiTQChain as Q
import OCF.Lean.YiTNRow as R
import OCF.Lean.YiTNShape as S
module AtLimit (f : ℕ → B.Tr B.zero)
  (adj : (n : ℕ) → B._⊢_◃_ B.zero (f n) (f (suc n))) where
  d = B.lim f adj
  module A = R.Actual d
  module L = A.A
  c = R.shift (f 0)
  oc = proj₂ L.oa 0
  folded = TB.ψ c oc (MT.rbᶻ c) (F.B₀ c) B.zero
    (P.self P.∙ P.z≤ c) (O.Ωt B.zero) (proj₁ (O.Ωt c))
  shifted-low : V.val B.zero (proj₁ folded) V.≼ V.val B.zero (proj₁ L.low)
  shifted-low = V.◁→≼ (V.val-mono B.zero
    (TB.mono L.a L.oa L.ra L.bs B.zero (P.self P.∙ P.z≤ L.a) (O.Ωt B.zero)
      {x = proj₁ (O.upz {s = B.sL} {h = λ n → R.shift (f n)} 0 (O.Ωt c))}
      {y = proj₁ (O.Ωt L.a)} (B.◃l 0)))
  shifted-to-feed : V.val B.zero (proj₁ folded) V.≼ V.val B.zero (T.Canonical.Target.feed d)
  shifted-to-feed = V.≼-trans shifted-low A.low-to-feed
module Actual = AtLimit S.curve S.adj
shifted-layer : Actual.c ≡ Q.shifted-source
shifted-layer = cong R.shift (trans S.first (sym T.source-chain-one))
shifted-to-two : V.val B.zero (proj₁ Actual.folded)
  V.≼ V.val B.zero (T.Canonical.Target.chain 2)
shifted-to-two = subst
  (λ d → V.val B.zero (proj₁ Actual.folded) V.≼ V.val B.zero (T.Canonical.Target.feed d))
  (sym S.chain-shape) Actual.shifted-to-feed
```
