# 带上下文的路径折叠等式
不读记号；编译定理：沿字面路径嵌入再折到零层，保留沿路径拉回的 Base 与原 β。
来源：YiTYPath.up-zero/fold-emb 的证明，扩展显式 Base 与 β；pull-ok 复用原件。
这不是标准 Ω 树的跨层值单调，也未填 Offset。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOFPath where
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiTYPath as Y
pull-base : ∀ {a b} → P._⊑_ a b → F.Base b → F.Base a
pull-base P.self bs = bs
pull-base (P.inc c v) bs = pull-base v (λ i u → bs i (P.inc c u))
pull-base {b = B.nd s h} (P.inu vs) bs =
  pull-base (vs (O.c₀ s)) (λ i u → bs i (P.inc (O.c₀ s) u))
up-zero : (s : B.Sh) (h : B.Ch s → B.L) (o : P.Ok (B.nd s h))
  (bs : F.Base (B.nd s h)) (β : O.Tr⁺ B.zero) (c : B.Ch s) (y : O.Tr⁺ (h c)) →
  TB.ψ (B.nd s h) o (MT.rbᶻ (B.nd s h)) bs B.zero (P.z≤ (B.nd s h)) β
    (proj₁ (O.upz c y))
  ≡ TB.ψ (h c) (proj₂ o c) (MT.rbᶻ (h c)) (λ i u → bs i (P.inc c u))
    B.zero (P.z≤ (h c)) β (proj₁ y)
up-zero B.sS h o bs β c (y , ny) = refl
up-zero B.sL h o bs β c (y , ny) = refl
up-zero (B.sΩ k) h o bs β c (y , ny) = refl
fold-emb : ∀ {a b} (v : P._⊑_ a b) (o : P.Ok b) (bs : F.Base b) (β : O.Tr⁺ B.zero) (y : O.Tr⁺ a) →
  TB.ψ b o (MT.rbᶻ b) bs B.zero (P.z≤ b) β
    (proj₁ (P.emb b o (P.wk v) y))
  ≡ TB.ψ a (Y.pull-ok v o) (MT.rbᶻ a) (pull-base v bs) B.zero (P.z≤ a) β (proj₁ y)
fold-emb P.self o bs β y = refl
fold-emb {b = B.nd s h} (P.inc c v) o bs β y = trans
  (up-zero s h o bs β c (P.emb (h c) (proj₂ o c) (P.wk v) y))
  (fold-emb v (proj₂ o c) (λ i u → bs i (P.inc c u)) β y)
fold-emb {b = B.nd s h} (P.inu vs) o bs β y = trans
  (up-zero s h o bs β (O.c₀ s) (P.emb (h (O.c₀ s)) (proj₂ o (O.c₀ s)) (P.wk (vs (O.c₀ s))) y))
  (fold-emb (vs (O.c₀ s)) (proj₂ o (O.c₀ s)) (λ i u → bs i (P.inc (O.c₀ s) u)) β y)
```
