# 换基干净对象的实际第 1 孩子
验收文件；固定链点沿三个首孩子到达既有 neck，未宣称值界。
来源：YiC0Local 的指定路径，fold、读回证据改用 YiBSClean；不改层号、折叠或合法性。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBTLocal where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiBSClean as U
import OCF.Lean.YiBSBase as R
import OCF.Lean.YiBSFold as F
import OCF.Lean.YiKSDesc as D
import OCF.Lean.YiC0Local as C
opaque
  c₁ : B.Tr U.one
  c₁ = U.Inner.chain 1
  c₁-eq : c₁ ≡ U.Inner.chain 1
  c₁-eq = refl
ℓ₁ : B.L
ℓ₁ = U.a c₁
child-output : U.Inner.out c₁ ≡ F.ψ₀ ℓ₁ (proj₂ U.o₂ c₁) (proj₂ U.r₂ c₁) (proj₁ (O.Ωt ℓ₁))
child-output = U.out-child c₁
opaque
  unfolding c₁ U.Inner.feed U.Inner.g
  neck-shape : C.first (C.first (C.first ℓ₁)) ≡ C.neck
  neck-shape = refl
  neck-path : D._⊑¹_ C.neck ℓ₁
  neck-path = D.n¹ (D.n¹ (D.n¹ D.r¹))
o-neck : P.Ok C.neck
o-neck = D.ok¹ neck-path (proj₂ U.o₂ c₁)
rb¹ : ∀ {j ℓ} → D._⊑¹_ j ℓ → R.Rb ℓ → R.Rb j
rb¹ D.r¹ r = r
rb¹ (D.n¹ {s = s} p) r = rb¹ p (proj₂ r (O.c₀ s))
r-neck : R.Rb C.neck
r-neck = rb¹ neck-path (proj₂ U.r₂ c₁)
```
