# 字面路径下的标准零层折叠
不读记号；编译定理：先沿字面路径嵌入再折到零层，等于在源层直接折叠。
不声称标准 Ω 树的跨层值单调；源 Ok 证书由同一路径读回。
来源：展开 YiRWPath.emb 与 YiTBRow.ψ 的零输入和 inu 行；最小实例为零层到 one。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTYPath where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTZSmall as S

pull-ok : ∀ {a b} → P._⊑_ a b → P.Ok b → P.Ok a
pull-ok P.self o = o
pull-ok (P.inc c v) o = pull-ok v (proj₂ o c)
pull-ok {b = B.nd s h} (P.inu vs) o = pull-ok (vs (O.c₀ s)) (proj₂ o (O.c₀ s))
up-zero : (s : B.Sh) (h : B.Ch s → B.L) (o : P.Ok (B.nd s h)) (c : B.Ch s) (z : O.Tr⁺ (h c)) →
  TB.ψ (B.nd s h) o (MT.rbᶻ (B.nd s h)) (F.B₀ (B.nd s h)) B.zero
    (P.z≤ (B.nd s h)) (O.Ωt B.zero) (proj₁ (O.upz c z))
  ≡ MT.ψ₀ᶻ (h c) (proj₂ o c) (proj₁ z)
up-zero B.sS h o c (z , nz) = refl
up-zero B.sL h o c (z , nz) = refl
up-zero (B.sΩ k) h o c (z , nz) = refl
fold-emb : ∀ {a b} (v : P._⊑_ a b) (o : P.Ok b) (y : O.Tr⁺ a) →
  TB.ψ b o (MT.rbᶻ b) (F.B₀ b) B.zero (P.z≤ b) (O.Ωt B.zero)
    (proj₁ (P.emb b o (P.wk v) y))
  ≡ MT.ψ₀ᶻ a (pull-ok v o) (proj₁ y)
fold-emb P.self o y = refl
fold-emb {b = B.nd s h} (P.inc c v) o y = trans
  (up-zero s h o c (P.emb (h c) (proj₂ o c) (P.wk v) y))
  (fold-emb v (proj₂ o c) y)
fold-emb {b = B.nd s h} (P.inu vs) o y = trans
  (up-zero s h o (O.c₀ s) (P.emb (h (O.c₀ s)) (proj₂ o (O.c₀ s)) (P.wk (vs (O.c₀ s))) y))
  (fold-emb (vs (O.c₀ s)) (proj₂ o (O.c₀ s)) y)
small-path : P._⊑_ B.zero S.one
small-path = P.inc tt P.self
small-check :
  TB.ψ S.one S.o-one (MT.rbᶻ S.one) (F.B₀ S.one) B.zero (P.z≤ S.one) (O.Ωt B.zero)
    (proj₁ (P.emb S.one S.o-one (P.wk small-path) (O.Ωt B.zero)))
  ≡ MT.ψ₀ᶻ B.zero tt (proj₁ (O.Ωt B.zero))
small-check = fold-emb small-path S.o-one (O.Ωt B.zero)
```
