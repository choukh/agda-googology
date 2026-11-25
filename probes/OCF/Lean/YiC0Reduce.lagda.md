# 指定零层孩子结点到公共第 0 项
验收文件；条件编译定理：NeckLow 推出公共 FirstRow，累计编号固定为 1。
NeckLow 是实际 neck 的标准底输出对 ψ₀(Ω_Ω) 的值界，本件未实填。
不声称完成第 0 项或整个 ψ₀(Ω_{Ω₂})；目标 HC 域有闭证书。
来源：下降复用 YiMTKeel.descᶻ，关系反射复用 YiKCSem.sem→M⁰；不改公共对象。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC0Reduce where
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiBRValue as BR
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiMTKeel as MK
import OCF.Lean.YiKSDesc as D
import OCF.Lean.YiC0Local as C
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiRefTw2 as RT
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; z≼; s≼s; l≼; ≼l)
open U using (module Inner)
row0 : E.T
row0 = E.fsn (AL.S 2) 0
row0-eq : row0 ≡ AL.S 1
row0-eq = refl
opaque
  hc₀ : E.HC row0
  hc₀ = XI.back (AL.hc-S 1)
o-neck : P.Ok C.neck
o-neck = D.ok¹ C.neck-path (proj₂ U.o₂ C.c₁)
-- perf: S-1，标准底输出与唯一展开规格一起封装。
opaque
  neck-out : O.Tr⁺ B.zero
  neck-out = MT.ψ₀ᶻ C.neck o-neck (proj₁ (O.Ωt C.neck))
  neck-out-eq : neck-out ≡ MT.ψ₀ᶻ C.neck o-neck (proj₁ (O.Ωt C.neck))
  neck-out-eq = refl
private
  read-back : (x : B.Tr B.zero) → K.readRW x ≼ BR.readRW x
  read-back B.zero = z≼
  read-back (B.suc x) = s≼s (read-back x)
  read-back (B.lim f a) = l≼ (λ n → ≼l n (read-back (f n)))
  read-desc : ∀ {j ℓ} (p : D._⊑¹_ j ℓ) (o : P.Ok ℓ)
    → K.readRW (MK.F₀ᶻ j (D.ok¹ p o)) ≼ K.readRW (MK.F₀ᶻ ℓ o)
  read-desc {j} {ℓ} p o = ≼-trans (read-back (MK.F₀ᶻ j (D.ok¹ p o)))
    (≼-trans (MK.descᶻ p o) (CS.rr≼ (MK.F₀ᶻ ℓ o)))
neck-below : K.readRW (proj₁ neck-out) ≼ K.readRW (proj₁ (Inner.out C.c₁))
neck-below = subst (λ z → K.readRW (proj₁ z) ≼ K.readRW (proj₁ (Inner.out C.c₁)))
  (sym neck-out-eq)
  (subst (λ z → K.readRW (MK.F₀ᶻ C.neck o-neck) ≼ K.readRW (proj₁ z))
    (sym C.child-output) (read-desc C.neck-path (proj₂ U.o₂ C.c₁)))
NeckLow : Set
NeckLow = RT.Rt hc₀ ≼ K.readRW (proj₁ neck-out)
NeckRelation : Set
NeckRelation = K.M⁰ row0 (proj₁ neck-out)
relation→low : NeckRelation → NeckLow
relation→low m = K.lower⁰ m hc₀
low→relation : NeckLow → NeckRelation
low→relation = CS.sem→M⁰ hc₀ (proj₁ neck-out)
need : NeckLow → C.Need
need low = CS.sem→M⁰ hc₀ (proj₁ (Inner.out C.c₁)) (≼-trans low neck-below)
first-row : NeckLow → UL.FirstRow
first-row low = 1 , K.G⁰.m-right (proj₁ (Inner.out B.zero))
  (subst (λ d → K.M⁰ row0 (proj₁ (Inner.out d))) C.c₁-eq (need low))
first-value : NeckLow → (h : SI.E.HC row0) → SI.E.tree h ≼ K.readRW (proj₁ U.output)
first-value low h = ≼-trans (XI.tree-back h)
  (K.lower⁰ (subst (λ z → K.M⁰ row0 (proj₁ z)) (sym U.row)
    (K.G⁰.m-cum (λ n → Inner.out (Inner.chain n)) 1
      (subst (λ d → K.M⁰ row0 (proj₁ (Inner.out d))) C.c₁-eq (need low)))) (XI.back h))
```
