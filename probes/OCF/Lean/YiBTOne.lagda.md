# 换基候选第 1 项的实际回灌与保留分支
验收文件；固定对象的计算与关系入口，不宣称 RowOneAtTwo 或第 1 项值界。
来源：YiC0Next 的变量接线，YiC1Slot 的截段工具只读复用；branch 属于本候选。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBTOne where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiBSFold as BS
import OCF.Lean.YiBSClean as U
import OCF.Lean.YiBTLocal as C
import OCF.Lean.YiBTGoals as G
import OCF.Lean.YiBSAccept as A
import OCF.Lean.YiBSFam as TF
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiC1Slot as Cut
import OCF.Align.EboLeanDef as E
slot : E.T
slot = E.ψ (E.natT 1) (E.ΩTower 2) ∷ []
w₁ : P._≤_ U.one C.ℓ₁
w₁ = P.self P.∙ proj₂ (proj₁ U.o₂) C.c₁
opaque
  child-feed : O.Tr⁺ U.one
  child-feed = BS.ψ C.ℓ₁ (proj₂ U.o₂ C.c₁) (proj₂ U.r₂ C.c₁) (F.B₀ C.ℓ₁)
    U.one w₁ (O.Ωt U.one) (proj₁ (O.Ωt C.ℓ₁))
  child-feed-eq : child-feed ≡ BS.ψ C.ℓ₁ (proj₂ U.o₂ C.c₁) (proj₂ U.r₂ C.c₁) (F.B₀ C.ℓ₁)
    U.one w₁ (O.Ωt U.one) (proj₁ (O.Ωt C.ℓ₁))
  child-feed-eq = refl
feed-child : U.Inner.feed C.c₁ ≡ proj₁ child-feed
feed-child = trans (U.feed-child C.c₁) (sym (cong proj₁ child-feed-eq))
chain2-child : U.Inner.chain 2 ≡ proj₁ child-feed
chain2-child = trans (cong U.Inner.feed (sym C.c₁-eq)) feed-child
c₁-Ω : H.M 1 (E.Ωt (E.natT 1)) C.c₁
c₁-Ω = subst (H.M 1 (E.Ωt (E.natT 1))) (sym C.c₁-eq)
  (H.m⊴N 1 (H.Mβ 0) (subst (λ d → K._⊴_ (proj₁ (O.Ωt U.one)) d)
    (sym (U.feed-child B.zero))
    (TF.ψ-⊵ (U.a B.zero) (proj₂ U.o₂ B.zero) (proj₂ U.r₂ B.zero) (F.B₀ (U.a B.zero))
      U.one (P.self P.∙ proj₂ (proj₁ U.o₂) B.zero) (O.Ωt U.one) (proj₁ (O.Ωt (U.a B.zero))))))
opaque
  unfolding child-feed C.neck-path C.c₁ U.Inner.feed U.Inner.g
  kept : B.Tr U.one
  kept = Cut.cut Cut.path (proj₁ child-feed)
  branch : B.Tr B.zero → B.Tr U.one
  branch d = Cut.br kept d
  valid : Cut.Steps Cut.path (proj₁ child-feed)
  valid = tt
  cut-isΩ : Cut.head (Cut.cut Cut.path (proj₁ child-feed)) ≡ Cut.hΩ
  cut-isΩ = refl
actual-below : K._⊴_ (Cut.cut Cut.path (proj₁ child-feed)) (proj₁ child-feed)
actual-below = Cut.cut-below Cut.path (proj₁ child-feed) valid
BranchNeed : Set
BranchNeed = ∀ η d → K.M⁰ η d → H.M 1 (E.fsT slot η) (branch d)
domain₀ : K.M⁰ [] B.zero
domain₀ = K.mz
domain₁ : K.M⁰ (E.natT 1) (B.suc B.zero)
domain₁ = K.m1 refl K.mz
```
