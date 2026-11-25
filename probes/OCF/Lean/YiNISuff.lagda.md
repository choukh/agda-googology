# 第 1 项所需的域成员与外部接线
验收文件；编译条件定理 first-at-two 保留请求成员、参照等式、实际输出比较三个前提。
没有构造更深 neck，也没有填入 index 为 slot 的请求；两已知点不足以实填此条件。
来源：YiNIBridge 的语义反射与 YiKVRel.G⁰.m-right；实际链及部分和只读 YiUTTwoLocal。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNISuff where
open import Data.Product using (proj₁)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Lean.YiNIDomain as D
open import OCF.Lean.YiNIIface
import OCF.Lean.YiNIBridge as Bridge
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiC0Next as N
import OCF.Lean.YiC0Local as C
import OCF.Lean.YiC0Reduce as R
import OCF.Lean.YiNIInstances as I
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_; ≼-trans)

record Cover (f : Family) (target : E.T) (y : B.Tr B.zero) : Set where
  field
    member : Family.Member f
    target-eq : Request.reference (Family.request f member) ≡ target
    upper : K.readRW (D.output (Request.node (Family.request f member))) ≼ K.readRW y

cover-rel : ∀ f t y → Law f → Cover f t y → K.M⁰ t y
cover-rel f t y law c = subst (λ s → K.M⁰ s y) (Cover.target-eq c)
  (CS.sem→M⁰ (Request.nonempty d) y (≼-trans (law (Cover.member c)) (Cover.upper c)))
  where d = Family.request f (Cover.member c)

record NextCover (f : Family) : Set where
  field
    member : Family.Member f
    index-is-slot : Request.index (Family.request f member) ≡ N.slot
    upper : K.readRW (D.output (Request.node (Family.request f member)))
      ≼ K.readRW (proj₁ (U.Inner.out (U.Inner.chain 2)))
  offset : B.L
  offset = D.Node.offset (Request.node (Family.request f member))
  readback : D.Readback offset
  readback = D.Node.readback (Request.node (Family.request f member))

next-cover : ∀ f → NextCover f → Cover f N.row₁ (proj₁ (U.Inner.out (U.Inner.chain 2)))
next-cover f c = record
  { member = NextCover.member c
  ; target-eq = trans (cong (λ ν → E.ψ [] (E.Ωt ν) ∷ []) (NextCover.index-is-slot c)) (sym N.row₁-shape)
  ; upper = NextCover.upper c }

first-at-two : ∀ f → Law f → NextCover f → N.RowOneAtTwo
first-at-two f law c = K.G⁰.m-right (UL.P 1)
  (cover-rel f N.row₁ (proj₁ (U.Inner.out (U.Inner.chain 2))) law (next-cover f c))

zero-cover : Cover I.known R.row0 (proj₁ (U.Inner.out (U.Inner.chain 1)))
zero-cover = record
  { member = I.at-neck ; target-eq = refl
  ; upper = subst (λ d → K.readRW (D.output I.neck) ≼ K.readRW (proj₁ (U.Inner.out d))) C.c₁-eq
      (subst (λ x → K.readRW x ≼ K.readRW (proj₁ (U.Inner.out C.c₁))) (sym I.neck-output) R.neck-below) }

zero-example : K.M⁰ R.row0 (proj₁ (U.Inner.out (U.Inner.chain 1)))
zero-example = cover-rel I.known R.row0 (proj₁ (U.Inner.out (U.Inner.chain 1))) I.known-law zero-cover

known-slot-impossible : (a : I.Known) → Request.index (Family.request I.known a) ≡ N.slot → ⊥
known-slot-impossible I.at-station ()
known-slot-impossible I.at-neck ()

known-no-next : NextCover I.known → ⊥
known-no-next c = known-slot-impossible (NextCover.member c) (NextCover.index-is-slot c)
```
