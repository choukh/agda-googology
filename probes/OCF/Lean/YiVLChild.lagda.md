# 内分支的实际孩子折叠
验收文件；实际内链分支精确化成孩子上的零层折叠，保留原表、限制底与起点。
来源：YiE4Inner 的函数等式与 YiTBRow 的 inu 行；地板、源关系复用 YiM2Local/YiVLActual。
只给计算等式和输入关系，不把它们当作零层保持。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVLChild where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
import OCF.Lean.YiAZStart as A
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiM2Local as M
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiVLActual as V
import OCF.Align.EboLeanDef as E

zero-child : ∀ s h (o : P.Ok (B.nd s h)) (r : TB.Rb (B.nd s h))
  (bs : F.Base (B.nd s h)) (β : O.Tr⁺ B.zero) c (y : O.Tr⁺ (h c))
  → TB.ψ (B.nd s h) o r bs B.zero (P.z≤ (B.nd s h)) β (proj₁ (O.upz {s = s} {h = h} c y))
  ≡ TB.ψ (h c) (proj₂ o c) (proj₂ r c) (λ i u → bs i (P.inc c u)) B.zero (P.z≤ (h c)) β (proj₁ y)
zero-child s h o r bs β c y = refl

module Child (q : ℕ) where
  d = A.N.Inner.chain q
  ℓ = A.N.a d
  o : P.Ok ℓ
  o = proj₂ A.N.o d
  r : TB.Rb ℓ
  r = proj₂ A.N.rr d
  bs : F.Base ℓ
  bs i u = A.N.base₁ i (P.inc d u)
  -- perf: S-1/C-10，孩子的实际折叠仍由 YiE4Base 封装。
  opaque
    collapse : O.Tr⁺ B.zero
    collapse = Q.collapse (ℓ , o , r , bs) A.D.β
    collapse-eq : collapse ≡ TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) A.D.β (proj₁ (O.Ωt ℓ))
    collapse-eq = Q.collapse-eq ℓ o r bs A.D.β
  row-eq : A.N.Inner.out d ≡ collapse
  row-eq = trans (cong (λ f → f d) A.N.Inner.out-eq)
    (trans (cong (λ x → TB.ψ A.N.h A.N.o A.N.rr A.N.base₁ B.zero (P.z≤ A.N.h) A.D.β x)
      (cong (λ f → f d) A.N.Inner.g-eq))
      (trans (zero-child (B.sΩ (B.tw 1)) A.N.a A.N.o A.N.rr A.N.base₁ A.D.β d (O.Ωt ℓ))
        (Relation.Binary.PropositionalEquality.sym collapse-eq)))
  floor : ∀ i (u : i P.≤ ℓ) → proj₁ (O.Ωt i) K.⊴ proj₁ (bs i u)
  floor i u = M.shaped-floor i (P.inc d u)
  source : ∀ n → GR.R ℓ (E.fsT M.arg (M.γ n)) (proj₁ (O.Ωt ℓ))
  source n = V.child-source n q

RootΩ : B.L → B.L → Set
RootΩ ℓ k = Σ (B.Tr k → B.L) λ a → ℓ ≡ B.nd (B.sΩ k) a
-- 这里只识别 q=0 的实际孩子根槽位，不外推到其他链点。
opaque
  unfolding A.N.branch A.D.Step.g
  first-shape : RootΩ (Child.ℓ 0) B.zero
  first-shape = _ , refl
```
