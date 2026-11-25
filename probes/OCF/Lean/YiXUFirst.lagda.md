# 干净对象首分支的独立上界
验收文件；编译定理：Inner.out zero 的读回不高于 ψ₀(Ω₄)，首链点具有有限层上界模拟证书。
不提供公共 output 的上界，不判定 ψ₀(Ω_{Ω₂})；入口 first-ceiling 与 chain1-model。
来源：YiMTRel.A/S 接 YiXVSourceSem.actual，封顶用 YiXVSourceEmbed.Bound.mult 与 YiLvValBase.reference-row；read-rel 沿 YiBRValue.rel≅ 的递归改为 K.readRW 出口。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXUFirst where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiCBActual as CB
import OCF.Lean.YiCLFam as H
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
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceFamily as Fam
import OCF.Lean.YiXVSourceEmbed as E
import OCF.Lean.YiXVZeroRead as Zero
open import OCF.Lean.YiASIface using (s0; ss)
open import OCF.Align.YiLvValBase using (γ; reference-row)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; l≼; ≼l; ≼-trans; ≼-refl)

re3 : RelE (H.fn 3) (J.nat 3) (proj₂ U.o₂ B.zero) (D.ev 3) (D.rt 3)
re3 = eS (eS (eS ez))
no3 : NoΩ (H.fn 3)
no3 = λ _ _ _ → tt
r3 : RelT B.zero S.zero
  (proj₁ (MT.ψ₀ᶻ (H.fn 3) (proj₂ U.o₂ B.zero) (proj₁ (O.Ωt (H.fn 3)))))
  (SF.ψ₀ (J.nat 3) (D.ev 3) (D.rt 3) (SO.Ωt (J.nat 3)))
r3 = proj₁ (MR.A {tb = MT.rbᶻ (H.fn 3)} re3 no3 (F.B₀ (H.fn 3)) (SF.B₀ (J.nat 3))
  (BF.B₀-R (E→L re3)) (O.Ωt B.zero) (is iz) ds (BO.Ωt-R (E→L re3)))
private
  -- K.readRW 与旧关系定理的 BR.readRW 是两个不同递归函数，此处直接给 K 出口。
  read-rel : ∀ {x y} → RelT B.zero S.zero x y → K.readRW x ≼ read y
  read-rel {x = B.zero} iz = z≼
  read-rel {x = B.suc x} (is r) = s≼s (read-rel r)
  read-rel {x = B.lim f a} (il (r , d)) = l≼ (λ n → ≼l n (read-rel (r n)))
-- perf: C-24，实际源树只通过已编译关系计算；不归约两个具体输出。
first-upper : K.readRW (proj₁ (U.Inner.out B.zero)) ≼
  L.ψ⁰ (L.add (L.Ω (L.natᴵ 3)) (λ q → q) (L.Ω (L.natᴵ 3) L.+ L.Ω (L.natᴵ 3)))
first-upper = subst (λ x → K.readRW (proj₁ x) ≼
  L.ψ⁰ (L.add (L.Ω (L.natᴵ 3)) (λ q → q) (L.Ω (L.natᴵ 3) L.+ L.Ω (L.natᴵ 3))))
  (sym CB.out0) (≼-trans (read-rel r3) (W.Out.bot (Sem.actual 3 3 P.top)))

first-ceiling : K.readRW (proj₁ (U.Inner.out B.zero)) ≼ L.ψ⁰ (E.Ω 4)
first-ceiling = ≼-trans first-upper
  (≼-trans (Zero.mono 3 (E.Bound.mult 3 3))
    (subst (λ y → L.ψ⁰ (γ 3 6) ≼ y) (sym (reference-row 3)) (≼l 6 (≼-refl _))))

chain1-old : J.Tr 1
chain1-old = SF.ψs (J.nat 3) (D.ev 3) (D.rt 3) (SF.B₀ (J.nat 3)) (J.nat 1)
  (Slots.pth (ss (ss s0))) (SO.Ωt (J.nat 1)) (SO.Ωt-nz (J.nat 1)) (SO.Ωt (J.nat 3))
chain1-related : RelT K.one (J.nat 1) (U.Inner.chain 1) chain1-old
chain1-related = subst (λ c → RelT K.one (J.nat 1) c chain1-old) (sym CB.chain1)
  (proj₁ (MR.S {tb = MT.rbᶻ (H.fn 3)} re3 no3 (F.B₀ (H.fn 3)) (SF.B₀ (J.nat 3))
    (BF.B₀-R (E→L re3)) (winuS (wincS wself)) (O.Ωt K.one)
    (BO.Ωt-R (lS lz)) (BO.Ωn-R (lS lz)) (BO.Ωt-R (E→L re3))))
chain1-model : Fam.U 1 chain1-old
  (W.φ P.top (ss (ss s0)) (L.add (E.Ω 3) (λ q → q) (E.Ω 3 L.+ E.Ω 3)))
chain1-model = W.Out.slots (Sem.actual 3 3 P.top) 1 (ss (ss s0))
```
