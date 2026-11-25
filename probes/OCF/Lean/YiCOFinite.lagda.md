# 有限坐标的标准折叠值出口
验收文件；编译定理：与有限层 n 相关的层号，其标准最小表折叠读回不高于 ψ₀(Ω_{n+1})。
这是有限坐标的值界，不是一般 UpperChild 出口；后者的含 Ω 情形仍未构造，不能由读法界替代。
来源：YiXUFirst.first-upper/first-ceiling 的证明改为变量层号与 n；read-rel 沿其私有递归。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCOFinite where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as SF
import OCF.Lean.YiLegOps as SO
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
import OCF.Lean.YiBROps as BO
import OCF.Lean.YiBRFold as BF
import OCF.Lean.YiMTRel as MR
open import OCF.Lean.YiNRHit using (NoΩ)
open import OCF.Lean.YiLSRead using (read)
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceSelfInput as D
import OCF.Lean.YiXVSourceWorldInput as W
import OCF.Lean.YiXVSourceSem as Sem
import OCF.Lean.YiXVSourcePath as Path
import OCF.Lean.YiXVSourceEmbed as E
import OCF.Lean.YiXVZeroRead as Zero
open import OCF.Align.YiLvValBase using (γ; reference-row)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; l≼; ≼l; ≼-trans; ≼-refl)
finite-E : ∀ n {ell} (o : P.Ok ell) → RelL ell (J.nat n) → RelE ell (J.nat n) o (D.ev n) (D.rt n)
finite-E zero o lz = ez
finite-E (suc n) o (lS r) = eS (finite-E n _ r)
finite-noΩ : ∀ n {ell} → RelL ell (J.nat n) → NoΩ ell
finite-noΩ zero lz = tt
finite-noΩ (suc n) (lS r) _ = finite-noΩ n r
read-rel : ∀ {x y} → RelT B.zero S.zero x y → K.readRW x ≼ read y
read-rel {x = B.zero} iz = z≼
read-rel {x = B.suc x} (is r) = s≼s (read-rel r)
read-rel {x = B.lim f a} (il (r , d)) = l≼ (λ n → ≼l n (read-rel (r n)))
finite-upper : ∀ n {ell} (o : P.Ok ell) → RelL ell (J.nat n) →
  K.readRW (proj₁ (MT.ψ₀ᶻ ell o (proj₁ (O.Ωt ell)))) ≼
  L.ψ⁰ (L.add (E.Ω n) (λ q → q) (E.Ω n L.+ E.Ω n))
finite-upper n {ell} o r = ≼-trans (read-rel (proj₁
  (MR.A {tb = MT.rbᶻ ell} (finite-E n o r) (finite-noΩ n r)
    (F.B₀ ell) (SF.B₀ (J.nat n)) (BF.B₀-R r) (O.Ωt B.zero) (is iz) ds (BO.Ωt-R r))))
  (W.Out.bot (Sem.actual n n Path.top))
finite-ceiling : ∀ n {ell} (o : P.Ok ell) → RelL ell (J.nat n) →
  K.readRW (proj₁ (MT.ψ₀ᶻ ell o (proj₁ (O.Ωt ell)))) ≼ L.ψ⁰ (E.Ω (suc n))
finite-ceiling n o r = ≼-trans (finite-upper n o r)
  (≼-trans (Zero.mono n (E.Bound.mult n 3))
    (subst (λ y → L.ψ⁰ (γ n 6) ≼ y) (sym (reference-row n)) (≼l 6 (≼-refl _))))
```
