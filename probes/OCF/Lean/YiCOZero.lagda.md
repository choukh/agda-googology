# UpperChild 的零源值出口与适用范围
验收文件；编译定理：UpperChild 的 source 为零时有真正折叠值界 ψ₀(Ω₄)，实际 out zero 与 first-ceiling 同界。
零源前提有实例；实际 a(chain 1) 不与任何有限层相关，故不能接有限坐标出口；不否定一般上界或里程碑。
首个未完成处是含 Ω 坐标的折叠值保持：UpperChild 的 model 尚未导出该值界；全链与 output 未推进。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCOZero where
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiXWChild as C
import OCF.Lean.YiXUFirst as X
import OCF.Lean.YiXUBoundary as Boundary
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiXVSourceFamily as Fam
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceEmbed as E
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiCOFinite as Fin
open import OCF.Lean.YiBRRel using (RelL; iz)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)

zero-premise : C.UpperChild (U.a B.zero) (E.Ω 1)
zero-premise = C.upper-child S.zero (C.child-related iz) Fam.D₁.uz
zero-source : C.UpperChild.source zero-premise ≡ S.zero
zero-source = refl

zero-source-exit : ∀ {ell X₁} (c : C.UpperChild ell X₁) → C.UpperChild.source c ≡ S.zero →
  (o : P.Ok ell) → K.readRW (proj₁ (MT.ψ₀ᶻ ell o (proj₁ (O.Ωt ell)))) ≼ L.ψ⁰ (E.Ω 4)
zero-source-exit {ell} c e o = Fin.finite-ceiling 3 o
  (subst (λ x → RelL ell (C.old-child x)) e (C.UpperChild.coordinate c))

zero-out-ceiling : K.readRW (proj₁ (U.Inner.out B.zero)) ≼ L.ψ⁰ (E.Ω 4)
zero-out-ceiling = subst (λ x → K.readRW (proj₁ x) ≼ L.ψ⁰ (E.Ω 4))
  (sym (UL.out-child B.zero)) (zero-source-exit zero-premise zero-source (proj₂ U.o₂ B.zero))
prior-zero-ceiling : K.readRW (proj₁ (U.Inner.out B.zero)) ≼ L.ψ⁰ (E.Ω 4)
prior-zero-ceiling = X.first-ceiling

no-chain1-finite-coordinate : ∀ n → RelL (U.a (U.Inner.chain 1)) (J.nat n) → ⊥
no-chain1-finite-coordinate n r = Boundary.no-next-NoΩ (Fin.finite-noΩ n r)
no-chain1-zero-source : ∀ {X₁} (c : C.UpperChild (U.a (U.Inner.chain 1)) X₁) →
  C.UpperChild.source c ≡ S.zero → ⊥
no-chain1-zero-source c e = no-chain1-finite-coordinate 3
  (subst (λ x → RelL (U.a (U.Inner.chain 1)) (C.old-child x)) e (C.UpperChild.coordinate c))

chain1-premise : C.UpperChild (U.a (U.Inner.chain 1)) C.cap₁
chain1-premise = C.actual
```
